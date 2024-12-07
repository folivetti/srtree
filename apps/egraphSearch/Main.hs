{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}
{-# LANGUAGE  MultiWayIf #-}
{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE  BangPatterns #-}
{-# LANGUAGE  TypeSynonymInstances, FlexibleInstances #-}

module Main where 

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Simplify
import Algorithm.EqSat.Build
import Algorithm.EqSat.Queries
import Algorithm.EqSat.Info
import Algorithm.EqSat.DB
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.ModelSelection
import Algorithm.SRTree.Opt
import Control.Lens (element, makeLenses, over, (&), (+~), (-~), (.~), (^.))
import Control.Monad (foldM, forM_, forM, when, unless, filterM, (>=>), replicateM, replicateM_)
import Control.Monad.State.Strict
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import Data.Massiv.Array as MA hiding (forM_, forM)
import Data.Maybe (fromJust, isNothing, isJust)
import Data.SRTree
import Data.SRTree.Datasets
import Data.SRTree.Eval
import Data.SRTree.Random (randomTree)
import Data.SRTree.Print
import Options.Applicative as Opt hiding (Const)
import Random
import System.Random
import qualified Data.HashSet as Set
import Data.List ( sort, maximumBy, intercalate, sortOn, intersperse )
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as FingerTree
import Data.Function ( on )
import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IntMap
import List.Shuffle ( shuffle )
import Algorithm.SRTree.NonlinearOpt

import Debug.Trace
import Algorithm.EqSat (runEqSat)

import GHC.IO (unsafePerformIO)
import Control.Scheduler 
import Control.Monad.IO.Unlift
import Data.SRTree (convertProtectedOps)
-- Insert random expression 
-- Evaluate random subtree 
-- Insert new random parent eNode 

type RndEGraph a = EGraphST (StateT StdGen IO) a

io = lift . lift
{-# INLINE io #-}
rnd = lift
{-# INLINE rnd #-}

myCost :: SRTree Int -> Int
myCost (Var _)      = 1
myCost (Const _)    = 1
myCost (Param _)    = 1
myCost (Bin op l r) = 2 + l + r
myCost (Uni _ t)    = 3 + t

data Alg = OnlyRandom | BestFirst deriving (Show, Read, Eq)


-- experiment 1 80/30
fitnessFun :: Int -> Distribution -> SRMatrix -> PVector -> Maybe PVector -> SRMatrix -> PVector -> Maybe PVector -> Fix SRTree -> PVector -> (Double, PVector)
fitnessFun nIter distribution x y mYErr x_val y_val mYErr_val _tree thetaOrig =
  if isNaN val || isNaN tr
    then (-(1/0), theta) -- infinity
    else (min tr val, theta)
  where
    tree         = relabelParams _tree
    nParams      = countParams tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    (Sz2 m' _)    = MA.size x
    (theta, fit, nEvs) = minimizeNLL' VAR1 distribution mYErr nIter x y tree thetaOrig
    evalF a b c  = negate $ nll distribution c a b tree $ if nParams == 0 then thetaOrig else theta
    tr           = evalF x y mYErr
    val          = evalF x_val y_val mYErr_val

{-# INLINE fitnessFun #-}

fitnessFunRep :: Int -> Int -> Distribution -> SRMatrix -> PVector -> Maybe PVector -> SRMatrix -> PVector -> Maybe PVector -> Fix SRTree -> RndEGraph (Double, PVector)
fitnessFunRep nRep nIter distribution x y mYErr x_val y_val mYErr_val _tree = do
    let tree = relabelParams _tree
        nParams = countParams tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    thetaOrigs <- replicateM nRep (rnd $ randomVec nParams)
    let fits = Prelude.map (fitnessFun nIter distribution x y mYErr x_val y_val mYErr_val _tree) thetaOrigs
    --replicateM nRep (fitnessFun nIter distribution x y mYErr x_val y_val mYErr_val _tree)
    pure (maximumBy (compare `on` fst) fits)
{-# INLINE fitnessFunRep #-}

-- helper query functions

getFitness :: EClassId -> RndEGraph (Maybe Double)
getFitness c = gets (_fitness . _info . (IM.! c) . _eClass)
{-# INLINE getFitness #-}
getTheta :: EClassId -> RndEGraph (Maybe PVector)
getTheta c = gets (_theta . _info . (IM.! c) . _eClass)
{-# INLINE getTheta #-}
getSize :: EClassId -> RndEGraph Int
getSize c = gets (_size . _info . (IM.! c) . _eClass)
{-# INLINE getSize #-}
isSizeOf p = p . _size . _info
{-# INLINE isSizeOf #-}


rewriteBasic2 :: [Rule]
rewriteBasic2 =
    [
      "x" * "y" :=> "y" * "x"
    , "x" + "y" :=> "y" + "x"
    , ("x" ** "y") * ("x" ** "z") :=> "x" ** ("y" + "z") -- :| isPositive "x"
    , ("x" + "y") + "z" :=> "x" + ("y" + "z")
    , ("x" * "y") * "z" :=> "x" * ("y" * "z")
    , ("x" * "y") + ("x" * "z") :=> "x" * ("y" + "z")
    , ("w" * "x") + ("z" * "x") :=> ("w" + "z") * "x" -- :| isConstPt "w" :| isConstPt "z"
    --, "x" - "x" :=> 0
    --, "x" / "x" :=> 1 -- :| isNotZero "x"
    ]

egraphSearch alg distribution x y mYErr x_val y_val mYErr_val x_te y_te mYErr_te terms nEvals maxSize printPareto printTrace slowIter slowRep = do
  ec <- insertRndExpr maxSize
  --ec <- insertBestExpr -- use only to debug
  updateIfNothing ec
  insertTerms
  evaluateUnevaluated
  runEqSat myCost rewritesParams 1
  cleanDB

  while ((<nEvals) . snd) (1,1) $
    \(radius, nEvs) ->
      do
       nCls  <- gets (IM.size . _eClass)
       nUnev <- gets (IntSet.size . _unevaluated . _eDB)
       let nEvs = nCls - nUnev
       bestF <- getBestFitness

       (ecN, b) <- case alg of
                    OnlyRandom -> do let ratio = fromIntegral nEvs / fromIntegral nCls
                                     b <- rnd (tossBiased ratio)
                                     ec <- if b && ratio > 0.99
                                              then insertRndExpr maxSize >>= canonical
                                              else evaluateRndUnevaluated >>= canonical
                                     pure (ec, False)
                    BestFirst  -> do
                      ecsPareto <- getParetoEcsUpTo radius
                      ecPareto     <- combineFrom ecsPareto >>= canonical
                      curFitPareto <- getFitness ecPareto

                      if isNothing curFitPareto
                        then pure (ecPareto, False)
                        else do ecsBest    <- getTopECLassThat radius (isSizeOf (<maxSize))
                                ecBest     <- combineFrom ecsBest >>= canonical
                                curFitBest <- getFitness ecBest
                                if isNothing curFitBest
                                  then pure (ecBest, False)
                                  else do ee <- evalRndSubTree
                                          case ee of
                                            Nothing -> do ec <- insertRndExpr maxSize >>= canonical
                                                          pure (ec, True)
                                            Just c  -> pure (c, False)
       ecN' <- canonical ecN
       upd <- updateIfNothing ecN'
       --test <- getFitness ecN
       --fitDB <- gets (FingerTree.length . _fitRangeDB . _eDB)

       when upd $ runEqSat myCost rewritesParams 1 >>= \_ -> cleanDB
       --when (not upd) $ io . print $ ("ops", b, test, ecN', fromIntegral nEvs / fromIntegral nCls, fitDB)
       when printTrace
         do
            ecN'' <- canonical ecN'
            _tree <- getBestExpr ecN''
            fi <- negate . fromJust <$> getFitness ecN''
            theta <- fromJust <$> getTheta ecN''
            let thetaStr   = intercalate ";" $ Prelude.map show (MA.toList theta)
            io . putStrLn $ showExpr _tree <> "," <> thetaStr <> "," <> show fi
            pure ()
       --cleanDB
       let radius' = if (not upd) then (max 3 $ min (500 `div` maxSize) (radius+1)) else (max 3 $ radius-1)
           nEvs'    = nEvs + if upd then 1 else 0
       pure (radius', nEvs')
  eclasses <- gets (IntMap.toList . _eClass)
  -- forM_ eclasses $ \(_, v) -> (io.print) (Set.size (_eNodes v), Set.size (_parents v))
  io $ putStrLn "id,Expression,theta,size,MSE_train,MSE_val,MSE_test,R2_train,R2_val,R2_test,nll_train,nll_val,nll_test,mdl_train,mdl_val,mdl_test"
  if printPareto
    then paretoFront
    else printBest
  --ft <- gets (_fitRangeDB . _eDB)
  --io . print $ Foldable.toList ft

  where
    --slowIter = 30
    --slowRep = 1
    longIter = 100
    longRep = 5



    updateIfNothing ec = do
      mf <- getFitness ec
      case mf of
        Nothing -> do
          t <- getBestExpr ec
          (f, p) <- fitnessFunRep slowRep slowIter distribution x y mYErr x_val y_val mYErr_val t
          insertFitness ec f p
          --io $ print f
          pure True
        Just _ -> pure False

    getBestFitness = do
      bec <- (gets (snd . getGreatest . _fitRangeDB . _eDB) >>= canonical)
      gets (_fitness . _info . (IM.! bec) . _eClass)

    evalRndSubTree :: RndEGraph (Maybe EClassId)
    evalRndSubTree = do ecIds <- gets (IntSet.toList . _unevaluated . _eDB)
                        if not (null ecIds)
                          then do rndId' <- rnd $ randomFrom ecIds
                                  rndId  <- canonical rndId'
                                  constType <- gets (_consts . _info . (IM.! rndId) . _eClass)
                                  case constType of
                                    NotConst -> pure $ Just rndId
                                    _        -> pure Nothing
                          else pure Nothing


    combineFrom [] = pure 0 -- this is the first terminal and it will always be already evaluated
    combineFrom ecs = do
        nt  <- rnd rndNonTerm
        p1  <- rnd (randomFrom ecs)
        p2  <- rnd (randomFrom ecs)
        l1  <- rnd (randomFrom [2..maxSize-2]) -- sz 10: [2..8]

        e1  <- randomChildFrom p1 l1 >>= canonical
        ml  <- gets (_size . _info . (IM.! e1) . _eClass)
        l2  <- rnd (randomFrom [1..(maxSize - ml - 1)]) -- maxSize - maxSize + 2 - 2= 0 -- sz 10: [1..7] (2) / [1..1] (8)
        e2  <- randomChildFrom p2 l2 >>= canonical
        case nt of
          Uni Id ()    -> canonical e1
          Uni f ()     -> add myCost (Uni f e1) >>= canonical
          Bin op () () -> do b <- rnd toss
                             if b
                              then add myCost (Bin op e1 e2) >>= canonical
                              else add myCost (Bin op e2 e1) >>= canonical

    getParetoEcsUpTo n = concat <$> forM [1..maxSize] (\i -> getTopECLassWithSize  i n)

    randomChildFrom ec' maxL = do
      p <- rnd toss -- whether to go deeper or return this level
      ec <- canonical ec'
      l <- gets (_size . _info . (IM.! ec) . _eClass )

      if p || l > maxL
          then do --enodes <- gets (_eNodes . (IM.! ec) . _eClass)
                  enode  <- gets (_best . _info . (IM.! ec) . _eClass) -- we should return the best otherwise we may build larger exprs
                  case enode of
                      Uni _ eci     -> randomChildFrom eci maxL
                      Bin _ ecl ecr -> do coin <- rnd toss
                                          if coin
                                            then randomChildFrom ecl maxL
                                            else randomChildFrom ecr maxL
                      _ -> pure ec -- this shouldn't happen unless maxL==0
          else pure ec

    nonTerms   = [ Bin Add () (), Bin Sub () (), Bin Mul () (), Bin Div () ()
                 , Bin PowerAbs () (),  Uni Recip ()] -- , Uni LogAbs (), Uni Exp (), Uni Sin (), Uni SqrtAbs ()]
    rndTerm    = Random.randomFrom terms
    rndNonTerm = Random.randomFrom $ (Uni Id ()) : nonTerms
    rndNonTerm2 = Random.randomFrom nonTerms

    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical

    insertRndExpr :: Int -> RndEGraph EClassId
    insertRndExpr maxSize =
      do grow <- rnd toss
         n <- rnd (randomFrom [if maxSize > 4 then 4 else 1 .. maxSize])
         t <- rnd $ Random.randomTree 3 8 n rndTerm rndNonTerm2 grow
         fromTree myCost t >>= canonical

    insertBestExpr :: RndEGraph EClassId
    insertBestExpr = do --let t =  "t0" / (recip ("t1" - "x0") + powabs "t2" "x0")
                        --let t = ((("t0" + (powabs "t0" "x0")) / "t0") * "x0")
                        let --t = "t0" / (recip ("t0" + "x0") - powabs "t0" "x0")
                            t = powabs "t0" (powabs ("t0" * "x0") (powabs "x0" "t0"))

                        ecId <- fromTree myCost t >>= canonical
                        (f, p) <- fitnessFunRep slowRep slowIter distribution x y mYErr x_val y_val mYErr_val t
                        insertFitness ecId f p
                        io . putStrLn $ "Best fit global: " <> show f
                        pure ecId
        where powabs l r  = Fix (Bin PowerAbs l r)

    getBestExprWithSize n =
        do ec <- getTopECLassWithSize n 1 >>= traverse canonical
           if (not (null ec))
            then do
              bestFit <- getFitness $ head ec
              bestP   <- gets (_theta . _info . (IM.! (head ec)) . _eClass)
              (:[]) . (,bestP) . (,bestFit) . (,ec) <$> getBestExpr (head ec)
            else pure []




    printExpr ix ec = do 
        fit <- fromJust <$> getFitness ec 
        theta <- gets (fromJust . _theta . _info . (IM.! ec) . _eClass)
        --((best, mf), mtheta) <- (,theta) . (,fit) <$> getBest ec
        best <- getBestExpr ec
        --(_, theta) <- fitnessFunRep longRep longIter distribution x y mYErr x_val y_val mYErr_val best
        let best'     = relabelParams best
            expr      = paramsToConst (MA.toList theta) best'
            unprotect = convertProtectedOps expr 
            mse_train = mse x y best' theta
            mse_val   = mse x_val y_val best' theta
            mse_te    = mse x_te y_te best' theta
            r2_train  = r2 x y best' theta
            r2_val    = r2 x_val y_val best' theta
            r2_te     = r2 x_te y_te best' theta
            nll_train  = nll distribution mYErr x y best' theta
            nll_val    = nll distribution mYErr_val x_val y_val best' theta
            nll_te     = nll distribution mYErr_te x_te y_te best' theta
            mdl_train  = mdl distribution mYErr x y theta best' --unprotect
            mdl_val    = mdl distribution mYErr_val x_val y_val theta best' --unprotect
            mdl_te     = mdl distribution mYErr_te x_te y_te theta best' --unprotect
            vals       = intercalate "," $ Prelude.map show [mse_train, mse_val, mse_te, r2_train, r2_val, r2_te, nll_train, nll_val, nll_te, mdl_train, mdl_val, mdl_te]
            thetaStr   = intercalate ";" $ Prelude.map show (MA.toList theta)
        io . putStrLn $ show ix <> "," <> showExpr expr <> "," <> thetaStr <> "," <> show (countNodes $ convertProtectedOps expr) <> "," <> vals

    printBest = do
      bec <- gets (snd . getGreatest . _fitRangeDB . _eDB) >>= canonical
      printExpr 0 bec

    paretoFront = go 1 0 (-(1.0/0.0))
      where
        go n ix f
          | n > maxSize = pure ()
          | otherwise   = do
              ecList <- getBestExprWithSize n
              if not (null ecList)
                 then do let (((best, ec), mf), mtheta) = head ecList
                             improved = fromJust mf > f 
                         cm <- gets _canonicalMap
                         ec' <- traverse canonical ec
                         when improved $ printExpr ix (head ec')
                         go (n+1) (ix + if improved then 1 else 0) (max f (fromJust mf))
                 else go (n+1) ix f

    evaluateUnevaluated = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          forM_ ec $ \c -> do
              t <- getBestExpr c
              (f, p) <- fitnessFunRep slowRep slowIter distribution x y mYErr x_val y_val mYErr_val t
              insertFitness c f p

    evaluateRndUnevaluated = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          c <- rnd . randomFrom $ ec 
          t <- getBestExpr c
          (f, p) <- fitnessFunRep slowRep slowIter distribution x y mYErr x_val y_val mYErr_val t
          insertFitness c f p
          pure c

while p arg prog = do when (p arg) do arg' <- prog arg
                                      while p arg' prog

data Args = Args
  { _dataset      :: String,
    _testData     :: String,
    _gens         :: Int,
    _alg          :: Alg,
    _maxSize      :: Int,
    _split        :: Int,
    _printPareto  :: Bool,
    _trace        :: Bool,
    _distribution :: Distribution,
    _optIter      :: Int,
    _optRepeat    :: Int
  }
  deriving (Show)

-- parser of command line arguments
opt :: Parser Args
opt = Args
   <$> strOption
       ( long "dataset"
       <> short 'd'
       <> metavar "INPUT-FILE"
       <> help "CSV dataset." )
  <*> strOption
       ( long "test"
       <> short 't'
       <> value ""
       <> showDefault
       <> help "test data")
   <*> option auto
      ( long "generations"
      <> short 'g'
      <> metavar "GENS"
      <> showDefault
      <> value 100
      <> help "Number of generations." )
   <*> option auto
       ( long "algorithm"
       <> short 'a'
       <> metavar "ALG"
       <> help "Algorithm." )
  <*> option auto
       ( long "maxSize"
       <> short 's'
       <> help "max-size." )
  <*> option auto
       ( long "split"
       <> short 'k'
       <> value 1 
       <> showDefault
       <> help "k-split ratio training-validation")
  <*> switch
       ( long "print-pareto"
       <> help "print Pareto front instead of best found expression")
  <*> switch
       ( long "trace"
       <> help "print all evaluated expressions.")
  <*> option auto
       ( long "distribution"
       <> value Gaussian
       <> showDefault
       <> help "distribution of the data.")
  <*> option auto
       ( long "opt-iter"
       <> value 30
       <> showDefault
       <> help "number of iterations in parameter optimization.")
  <*> option auto
       ( long "opt-retries"
       <> value 1
       <> showDefault
       <> help "number of retries of parameter fitting.")

chunksOf :: Int -> [e] -> [[e]]
chunksOf i ls = Prelude.map (Prelude.take i) (build (splitter ls))
 where
  splitter :: [e] -> ([e] -> a -> a) -> a -> a
  splitter [] _ n = n
  splitter l c n = l `c` splitter (Prelude.drop i l) c n
  build :: ((a -> [a] -> [a]) -> [a] -> [a]) -> [a]
  build g = g (:) []

splitData :: SRMatrix -> PVector -> Maybe PVector ->Int -> State StdGen (SRMatrix, SRMatrix, PVector, PVector, Maybe PVector, Maybe PVector)
splitData x y mYErr k = do
  if k == 1
    then pure (x, x, y, y, mYErr, mYErr)
    else do
      ixs' <- (state . shuffle) [0 .. sz-1]
      let ixs = chunksOf k ixs'

      let (x_tr, x_te) = getX ixs x
          (y_tr, y_te) = getY ixs y
          mY = fmap (getY ixs) mYErr
          (y_err_tr, y_err_te) = (fmap fst mY, fmap snd mY)
      pure (x_tr, x_te, y_tr, y_te, y_err_tr, y_err_te)
  where
    (MA.Sz sz) = MA.size y
    --qty_tr     = round (thr * fromIntegral sz)
    --qty_te     = sz - qty_tr
    comp_x     = MA.getComp x
    comp_y     = MA.getComp y

    getX :: [[Int]] -> SRMatrix -> (SRMatrix, SRMatrix)
    getX ixs xs' = let xs = MA.toLists xs' :: [MA.ListItem MA.Ix2 Double]
                    in ( MA.fromLists' comp_x [xs !! ix | ixs_i <- ixs, ix <- Prelude.tail ixs_i]
                       , MA.fromLists' comp_x [xs !! ix | ixs_i <- ixs, let ix = Prelude.head ixs_i]
                       )
    getY :: [[Int]] -> PVector -> (PVector, PVector)
    getY ixs ys  = ( MA.fromList comp_y [ys MA.! ix | ixs_i <- ixs, ix <- Prelude.tail ixs_i]
                   , MA.fromList comp_y [ys MA.! ix | ixs_i <- ixs, let ix = Prelude.head ixs_i]
                   )

getTrain ((a, b, _, _), (c, _), _, _) = (a,b,c)

main :: IO ()
main = do
  --args <- pure (Args "nikuradse_2.csv" 100) -- execParser opts
  args <- execParser opts
  g <- getStdGen
  ((x, y, _, _), (mYErr, _), _, _) <- loadDataset (_dataset args) True
  (x_te, y_te, mYErr_te) <- if null (_testData args)
                              then pure (x, y, mYErr)
                              else getTrain <$> loadDataset (_testData args) True
  let ((x_tr, x_val, y_tr, y_val, mYErr_tr, mYErr_val),g') = runState (splitData x y mYErr $ _split args) g
  let (Sz2 _ nFeats) = MA.size x
      terms          = if _distribution args == ROXY
                          then [var 0, param 0]
                          else [var ix | ix <- [0 .. nFeats-1]] <> [param 0] -- [param ix | ix <- [0 .. 5]]
      alg            = evalStateT (egraphSearch (_alg args) (_distribution args) x_tr y_tr mYErr_tr x_val y_val mYErr_val x_te y_te mYErr_te terms (_gens args) (_maxSize args) (_printPareto args) (_trace args) (_optIter args) (_optRepeat args)) emptyGraph
  evalStateT alg g'

  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )
