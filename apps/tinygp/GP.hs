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
import Control.Monad.State
import Control.Monad
import Data.Vector qualified as V
import Control.Monad (when)
import Data.Massiv.Array qualified as M
import Debug.Trace ( traceShow, trace )

data Method = Grow | Full | BTC

type Rng a = StateT StdGen IO a 
type GenUni = Fix SRTree -> Fix SRTree 
type GenBin = Fix SRTree -> Fix SRTree -> Fix SRTree
type FitFun = Individual -> Individual 

data Individual = Individual { _tree :: Fix SRTree, _fit :: Double, _params :: PVector }

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
{-# INLINE randomTree #-}

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
{-# INLINE tournament #-}

randomIndividual :: HyperParams -> FitFun -> Bool -> Rng Individual
randomIndividual hyperparams fitFun grow = do
    t <- randomTree hyperparams grow 
    let p = countParams t
    theta' <- replicateM p (randomRange (-1,1))
    let ind = fitFun $ Individual t 0.0 (M.fromList compMode theta' :: PVector)
    pure ind
    --if isInfinite (_fit ind)
    --   then randomIndividual hyperparams fitFun grow 
    --   else pure ind
{-# INLINE randomIndividual #-}

initialPop :: HyperParams -> FitFun -> Rng (V.Vector Individual)
initialPop hyperparams fitFun = do 
   let depths = [3 .. _maxDepth hyperparams]
   pop <- forM depths $ \md -> 
           do let m = _popSize hyperparams `div` (_maxDepth hyperparams - 3 + 1)
                  g = V.fromList . take m $ cycle [True, False]
              mapM (randomIndividual hyperparams{ _maxDepth = md} fitFun) g
   pure (V.concat pop)
{-# INLINE initialPop #-}

fitness :: SRMatrix -> PVector -> Individual -> Individual
fitness x y ind =
    let 
        tree = relabelParams $ _tree ind
        thetaOrig = _params ind
        (theta, fit, _) = minimizeNLL Gaussian Nothing Nothing 10 x y tree thetaOrig
        --theta = _params ind
        fit' = negate $ mse x y tree thetaOrig -- nll Gaussian (Just 1) x y (relabelParams $ _tree ind) (_params ind)
       -- (fit, g) = gradNLL Gaussian Nothing x y (_tree ind) (_params ind)
    in if M.isNull (_params ind)
          then ind{_fit=fit'}
          else ind{_fit = negate (mse x y tree theta), _params = theta}
    --in ind{_fit = fit, _params = theta}
{-# INLINE fitness #-}

isAbs (Fix (Uni Abs _)) = True 
isAbs _ = False 
{-# INLINE isAbs #-}

isInv (Fix (Bin Div (Fix (Const 1.0)) _)) = True 
isInv _ = False 
{-# INLINE isInv #-}

mutate :: HyperParams -> Individual -> Rng Individual
mutate hp ind = do
  let sz = countNodes' (_tree ind)
  (t, b) <- go sz (_pm hp) (_tree ind)
  if b 
     then pure $ Individual t 0.0 M.empty
     else pure ind
      where
        go s p t
          | isAbs t = do let [x] = getChildren t
                         (t', b) <- go s p x
                         pure (Fix $ replaceChildren [t'] $ unfix t, b)
          | otherwise = do
              v <- state random 
              if v < p 
                then do let sz2 = countNodes' t 
                            maxSz = _maxSize hp - s + sz2 - 2
                        (, True) <$> randomTree hp{_maxSize = maxSz} True 
                else case arity t of 
                       0 -> pure (t, False)
                       1 -> do let [x] = getChildren t 
                               (t', b) <- go s p x 
                               pure (Fix $ replaceChildren [t'] $ unfix t, b)
                       2 -> do let [l,r] = getChildren t 
                               (l', b) <- if isInv t 
                                             then pure (l, False)
                                             else go s p l
                               if b 
                                 then pure (Fix $ replaceChildren [l', r] $ unfix t, b)
                                 else do (r', b') <- go s p r 
                                         pure (Fix $ replaceChildren [l, r'] $ unfix t, b')

crossover :: HyperParams -> Individual -> Individual -> Rng Individual
crossover hp ind1 ind2 = pure ind1

evolve :: HyperParams -> FitFun -> V.Vector Individual -> Rng Individual
evolve hp fitFun pop = do 
    parent1 <- tournament hp pop
    parent2 <- tournament hp pop 
    child <- crossover hp parent1 parent2
    child' <- mutate hp child
    let p = countParams (_tree child')
    theta' <- M.fromList compMode <$> replicateM p (randomRange (-1,1))
    pure $ fitFun child'{_params = theta'}
{-# INLINE evolve #-}

report :: Int -> V.Vector Individual -> IO ()
report gen = mapM_ reportOne
  where reportOne ind = do putStr (show gen)
                           putStr ": "
                           putStr (showExpr (_tree ind))
                           putStr " - " 
                           putStr (show (_fit ind))
                           putStr " "
                           print (M.toList $ _params ind)
{-# INLINE report #-}

evolution :: Int -> HyperParams -> FitFun -> Rng (V.Vector Individual)
evolution gen hp fitFun = do 
    pop <- initialPop hp fitFun
    liftIO $ report (-1) pop
    go gen pop 
        where 
            go 0 pop = pure pop 
            go n pop = do 
                let best = V.maximumOn _fit $ V.filter (not.isNaN._fit) pop
                pop' <- V.cons best <$> V.replicateM (_popSize hp - 1) (evolve hp fitFun pop)
                liftIO $ report (gen-n) pop'
                go (n-1) pop'
