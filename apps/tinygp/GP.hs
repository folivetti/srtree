{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
module GP where

import Data.SRTree
import Algorithm.SRTree.Opt
import Algorithm.SRTree.Likelihoods
import Data.SRTree.Print
import Data.SRTree.Eval
import Data.SRTree.Recursion ( cata )
import System.Random
import Control.Monad.State.Strict
import Control.Monad
import Data.Vector qualified as V
import Control.Monad (when)
import Data.Massiv.Array qualified as M
import Debug.Trace ( traceShow, trace )
import Util
import Data.List ( intercalate, maximumBy )
import qualified Data.Vector.Mutable as MV

data Method = Grow | Full | BTC
type Rng a = StateT StdGen IO a

type GenUni = Fix SRTree -> Fix SRTree 
type GenBin = Fix SRTree -> Fix SRTree -> Fix SRTree
type FitFun = Individual -> Rng Individual

data Individual = Individual { _tree :: Fix SRTree, _fit :: Double, _params :: [PVector] }

instance Show Individual where 
    show (Individual t f p) = showExpr t <> "," <> show f <> "," <> show p 

toss :: Rng Bool
toss = state random
{-# INLINE toss #-}

randomRange :: (Ord val, Random val) => (val, val) -> Rng val
randomRange rng = state (randomR rng)
{-# INLINE randomRange #-}

randomFrom :: [a] -> Rng a
randomFrom funs = do n <- randomRange (0, length funs - 1)
                     pure $ funs !! n
{-# INLINE randomFrom #-}

randomFromV :: V.Vector a -> Rng a
randomFromV funs = do n <- randomRange (0, length funs - 1)
                      pure $ funs V.! n
{-# INLINE randomFromV #-}

countNodes' :: Fix SRTree -> Int
countNodes' = cata alg 
  where 
    alg (Var _)     = 1
    alg (Param _)   = 1
    alg (Const _)   = 0
    alg (Bin _ l r) = 1 + l + r
    alg (Uni Abs t) = t
    alg (Uni _ t)   = 1 + t
{-# INLINE countNodes' #-}


randomTree :: HyperParams -> Bool -> Rng (Fix SRTree)
randomTree hp grow 
  | depth <= 1 || size <= 2 = randomFrom term 
  | (min_depth >= 0 || (depth > 2 && not grow)) && size > 2 = genNonTerm 
  | otherwise = genTermOrNon
  where 
    min_depth = _minDepth hp
    depth     = _maxDepth hp
    size      = _maxSize hp
    term      = _term hp
    nonterm   = _nonterm hp

    genNonTerm =
       do et <- randomFrom nonterm
          case et of 
            Left uniT -> uniT <$> randomTree hp{_minDepth = min_depth-1, _maxDepth = depth - 1, _maxSize = size - 1} grow
            Right binT -> do l <- randomTree hp{_minDepth = min_depth-1, _maxDepth = depth - 1, _maxSize = size - 1} grow
                             r <- randomTree hp{_minDepth = min_depth-1, _maxDepth = depth - 1, _maxSize = size - 1 - countNodes' l} grow
                             pure (binT l r)
    genTermOrNon = do r <- toss
                      if r
                        then randomFrom term 
                        else genNonTerm        

data HyperParams = 
    HP { _minDepth  :: Int 
       , _maxDepth  :: Int
       , _maxSize   :: Int 
       , _popSize   :: Int
       , _tournSize :: Int
       , _pc        :: Double 
       , _pm        :: Double 
       , _term      :: [Fix SRTree]
       , _nonterm   :: [Either GenUni GenBin] 
       }

tournament :: HyperParams -> V.Vector Individual -> Rng Individual
tournament hp pop = do
  selection <- replicateM (_tournSize hp) (randomFromV $ V.filter (not.isNaN._fit) pop)
  let maxFitness = maximum (fmap _fit selection)
      champions = V.filter ((== maxFitness) . _fit) pop
  if null selection
     then randomFromV pop
     else randomFromV champions

randomIndividual :: HyperParams -> FitFun -> Bool -> Rng Individual
randomIndividual hyperparams fitFun grow = do
    t <- randomTree hyperparams grow 
    let p = countParams t
    --theta' <- replicateM p (randomRange (-1,1))
    fitFun $ Individual t 0.0 [] -- (M.fromList compMode theta' :: PVector)
    --pure ind
    --if isInfinite (_fit ind)
    --   then randomIndividual hyperparams fitFun grow 
    --   else pure ind

initialPop :: HyperParams -> FitFun -> Rng (V.Vector Individual)
initialPop hyperparams fitFun = do 
   let depths = [3 .. _maxDepth hyperparams]
   pop <- forM depths $ \md -> 
           do let m = _popSize hyperparams `div` (_maxDepth hyperparams - 3 + 1)
                  g = V.fromList . take m $ cycle [True, False]
              mapM (randomIndividual hyperparams{ _maxDepth = md} fitFun) g
   pure (V.concat pop)

fitnessMV :: Distribution -> [(SRMatrix, PVector, Maybe PVector)] -> Individual -> Rng Individual
fitnessMV dist datas ind = do
  fs <- forM datas (fitness dist ind)
  let fitOpt = minimum $ map fst fs
  pure ind{_fit = fitOpt, _params = map snd fs}

fitness :: Distribution -> Individual ->  (SRMatrix, PVector, Maybe PVector) -> Rng (Double, PVector)
fitness dist ind (x, y, e) = do
    let tree = relabelParams $ _tree ind
        p    = countParams tree
    theta1' <- M.fromList M.Seq <$> replicateM p (randomRange (-1,1))
    theta2' <- M.fromList M.Seq <$> replicateM p (randomRange (-1,1))
    let (theta1, f1, _) = minimizeNLL dist e 50 x y tree theta1'
        (theta2, f2, _) = minimizeNLL dist e 50 x y tree theta2'
        fit1 = if isNaN f1 then (-1.0/0.0) else negate f1
        fit2 = if isNaN f1 then (-1.0/0.0) else negate f2
        thetaOpt = if fit1 > fit2 then theta1 else theta2
        fitOpt   = max fit1 fit2
    pure (fitOpt, thetaOpt)


mutate :: HyperParams -> Individual -> Rng (Maybe Individual)
mutate hp ind = do
  let sz = countNodes' (_tree ind)
  p <- state $ randomR (0, sz-1)
  b <- state random
  t <- go p (_maxSize hp) (_tree ind)
  --(t, b) <- go sz (_pm hp) (_tree ind)
  if b <= _pm hp && countNodes t <= _maxSize hp
     then pure . Just $ Individual t 0.0 []
     else pure Nothing
      where
        go 0 msz t = randomTree hp{_maxSize = msz-1} True
        go n msz (Fix (Uni f t)) = Fix . Uni f <$> go (n-1) (msz-1) t
        go n msz (Fix (Bin op l r)) = do
          let nl = countNodes l
              nr = countNodes r
          if nl <= n - 1
             then Fix . Bin op l <$> go (n-nl-1) (msz-nl-1) r
             else do l' <- go (n-1) (msz-nr-1) l
                     pure $ Fix $ Bin op l' r

crossover :: HyperParams -> Individual -> Individual -> Rng (Maybe Individual)
crossover hp ind1 ind2 = do
  b <- state random
  if b < (_pc hp)
     then do let n1 = countNodes $ _tree ind1
                 n2 = countNodes $ _tree ind2
             p1 <- state $ randomR (0, n1-1)
             p2 <- state $ randomR (0, n2-1)
             let part1 = pickLeft p1 $ _tree ind1
                 part2 = pickRight p2 $ _tree ind2
                 t = part1 part2
                 n = countNodes t
             if n <= _maxSize hp
                then pure . Just $ ind1{_tree = t}
                else pure Nothing
     else pure Nothing
  where
    pickRight :: Int -> Fix SRTree -> Fix SRTree
    pickRight 0 node = node
    pickRight n (Fix (Uni f t)) = pickRight (n-1) t
    pickRight n (Fix (Bin op l r)) = let nl = countNodes l
                                     in if nl <= n-1
                                           then pickRight (n-nl-1) r
                                           else pickRight (n-1) l
    pickLeft :: Int -> Fix SRTree -> (Fix SRTree -> Fix SRTree)
    pickLeft 0 node = \t -> t
    pickLeft n (Fix (Uni f t)) = let g = pickLeft (n-1) t in \t' -> Fix $ Uni f (g t')
    pickLeft n (Fix (Bin op l r)) = let nl = countNodes l
                                    in if nl <= n-1
                                          then let g = pickLeft (n-nl-1) r in \t -> Fix $ Bin op l (g t)
                                          else let g = pickLeft (n-1) l in \t -> Fix $ Bin op (g t) r


evolve :: HyperParams -> FitFun -> V.Vector Individual -> Rng Individual
evolve hp fitFun pop = do 
    parent1 <- tournament hp pop
    parent2 <- tournament hp pop 
    mChild <- crossover hp parent1 parent2
    child' <- case mChild of
                Nothing    -> mutate hp parent1
                Just child -> mutate hp child
    --let p = countParams (_tree child')
    --theta' <- M.fromList compMode <$> replicateM p (randomRange (-1,1))
    case child' of
        Nothing -> pure parent1
        Just c  -> fitFun c

printFinal dist ind dataTrains dataTests = do
  let tree     = relabelParams $ _tree ind
      thetas   = _params ind
      mseTrain = maximum $ map (\(theta, (x,y,e)) -> nll dist e x y tree theta) $ zip thetas dataTrains
      mseTest  = maximum $ map (\(theta, (x,y,e)) -> nll dist e x y tree theta) $ zip thetas dataTests
      r2Train  = minimum $ map (\(theta, (x,y,e)) -> r2 x y tree theta) $ zip thetas dataTrains
      r2Test   = minimum $ map (\(theta, (x,y,e)) -> r2 x y tree theta) $ zip thetas dataTests
      thetaStr = intercalate "_" $ map (intercalate ";" . map show . M.toList) thetas
  putStrLn "id,Expression,theta,size,MSE_train,MSE_test,R2_train,R2_test"
  putStr $ "0," <> showExpr tree <> "," <> thetaStr <> "," <> show (countNodes tree) <> "," <> show mseTrain <> "," <> show mseTest <> "," <> show r2Train <> "," <> show r2Test

report :: Int -> V.Vector Individual -> IO ()
report gen = mapM_ reportOne
  where reportOne ind = do putStr (show gen)
                           putStr ": "
                           putStr (showExpr (_tree ind))
                           putStr " - " 
                           putStr (show (_fit ind))
                           putStr " "
                           print (map M.toList $ _params ind)
{-# INLINE report #-}

evolution :: Int -> HyperParams -> FitFun -> Rng (Individual)
evolution gen hp fitFun = do 
    pop <- initialPop hp fitFun
    --liftIO $ report (-1) pop
    go gen pop
        where 
            go 0 !pop = pure $ pop  V.! 0
            go n !pop = do
                let best = V.maximumOn _fit $ V.filter (not.isNaN._fit) pop
                pop' <- V.modify (\v -> MV.write v 0 best) <$> V.replicateM (_popSize hp) (evolve hp fitFun pop)
                --liftIO $ report (gen-n) pop'
                go (n-1) pop'
