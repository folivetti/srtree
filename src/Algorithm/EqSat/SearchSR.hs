-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.EqSat.Search
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Support functions for search symbolic expressions with e-graphs
--
-----------------------------------------------------------------------------

module Algorithm.EqSat.SearchSR where

import Data.SRTree
import Data.SRTree.Datasets
import Data.SRTree.Eval (compileLoss)
import System.Random
import Control.Monad.State.Strict
import Control.Concurrent (getNumCapabilities)
import Control.Concurrent.Async (mapConcurrently)
import Data.Maybe (catMaybes)
import Control.Exception (evaluate)
import qualified Control.DeepSeq as DeepSeq
import Algorithm.EqSat.Egraph
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.AD (ADBackEnd(..))
import Algorithm.SRTree.AD.Unboxed (setMTPopParallel)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IntSet
import qualified Data.SRTree.Random as Random
import Data.Function ( on )
import Algorithm.SRTree.NonlinearOpt
import Control.Monad ( when, replicateM, forM, forM_ )
import Numeric.Optimization.NLOPT
import Algorithm.EqSat.Info
import Algorithm.EqSat.Build
import Data.SRTree.Random
import Algorithm.EqSat.Queries
import Data.List ( maximumBy )
import qualified Data.List as Data.List
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Vector.Unboxed as V

-- Environment of an e-graph with support to random generator and IO
type RndEGraph a = EGraphST (StateT StdGen IO) a

io :: IO a -> RndEGraph a
io = lift . lift
{-# INLINE io #-}
rnd :: StateT StdGen IO a -> RndEGraph a
rnd = lift
{-# INLINE rnd #-}

-- TEMP instrumentation (EGGP_STATS=1), removed after measurement
-- (evals counter, dedup counter)
-- end TEMP instrumentation

-- | Run an 'RndEGraph' action against a read-only egraph snapshot with the given
-- generator (for concurrent workers that do not mutate the shared egraph).
runRndEGraph :: EGraph -> StdGen -> RndEGraph a -> IO a
runRndEGraph eg g m = do
  ((a, _), _) <- runStateT (runStateT m eg) g
  pure a
{-# INLINE runRndEGraph #-}

-- | Fit a batch of e-classes in parallel, then insert the results serially.
-- Semantics mirror 'updateIfNothing' (skip already-fitted) unless 'force' is
-- True. The shared 'StdGen' is split once; each worker gets its own generator,
-- so the global draw sequence differs from the serial search (acceptable).
-- While the batch runs, the MultiThread backend is switched to single-chunk so
-- cores go to the batch rather than oversubscribing the inner per-tree split.
fitBatch :: Bool
         -> (Fix SRTree -> RndEGraph (Double, [Target]))
         -> [EClassId]
         -> RndEGraph ()
fitBatch force fitFun ecs0 = do
  ecs <- Prelude.mapM canonical ecs0
  jobs <- fmap catMaybes $ forM ecs $ \ec -> do
            mf <- getFitness ec
            if force || mf == Nothing
               then do tree <- getBestExpr ec
                       pure (Just (ec, tree))
               else pure Nothing
  case jobs of
    [] -> pure ()
    _  -> do
      nCaps <- io getNumCapabilities
      g0 <- rnd get
      let (seed, g1) = random g0 :: (Int, StdGen)
          gs    = [ mkStdGen (seed + fromIntegral i) | i <- [0 .. length jobs - 1] ]
          jobsG = [ (ec, tree, g) | ((ec, tree), g) <- zip jobs gs ]
          chunk k xs = [ [ xs !! j | j <- [i, i + k .. length xs - 1] ] | i <- [0 .. k - 1] ]
      rnd (put g1)
      eg <- get
      io (setMTPopParallel True)
      results <- io $ fmap concat (mapConcurrently (mapM (runJob eg fitFun)) (chunk nCaps jobsG))
      io (setMTPopParallel False)
      forM_ results $ \(ec0, f, p) -> insertFitness ec0 f p
  where
    runJob :: EGraph -> (Fix SRTree -> RndEGraph (Double, [Target])) -> (EClassId, Fix SRTree, StdGen) -> IO (EClassId, Double, [Target])
    runJob eg fit' (ec, tree, g) = do
      (f, p) <- runRndEGraph eg g (fit' tree)
      f' <- evaluate (DeepSeq.force f)
      p' <- evaluate (DeepSeq.force p)
      pure (ec, f', p')

myCost :: SRTree Int -> Int
myCost (Var _)     = 1
myCost (Const _)   = 1
myCost (Param _)   = 1
myCost (Bin _ l r) = 2 + l + r
myCost (Uni _ t)   = 3 + t

while :: Monad f => (t -> Bool) -> t -> (t -> f t) -> f t
while p arg prog = do if (p arg)
                      then do arg' <- prog arg
                              while p arg' prog
                      else pure arg

fitnessFun :: ADBackEnd -> Bool -> Int -> Distribution -> DataSet -> DataSet -> Fix SRTree -> Target -> (Double, Target)
fitnessFun backend skipVal nIter distribution (x, y, mYErr) (x_val, y_val, mYErr_val) tree thetaOrig =
  if isNaN val
    then (-(1/0), theta)
    else (val, theta)
  where
    nParams       = countParamsUniq tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    (theta, loss, _) = minimizeNLL' VAR1 backend (NLL distribution) mYErr nIter x y tree thetaOrig
    evalF a b c   = negate $ compileLoss a (buildLoss (NLL distribution) (fromIntegral (V.length b)) tree) b c $ if nParams == 0 then thetaOrig else theta
    -- at folds=1 the validation split is the training data itself, so the
    -- train loss returned by minimizeNLL' already is the val loss; skipping
    -- the separate compileLoss below avoids re-evaluating every expression.
    val           = if skipVal then negate loss else evalF x_val y_val mYErr_val

--{-# INLINE fitnessFun #-}

fitnessFunRep :: ADBackEnd -> Bool -> Int -> Int -> Distribution -> DataSet -> DataSet -> Fix SRTree -> RndEGraph (Double, Target)
fitnessFunRep backend skipVal nRep nIter distribution dataTrain dataVal tree = do
    let nParams = countParamsUniq tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    thetaOrigs <- replicateM nRep (rnd $ randomVec nParams)
    pure $ maximumBy (\(x, _) (y, _) -> compare x y) $ Prelude.map (fitnessFun backend skipVal nIter distribution dataTrain dataVal tree) thetaOrigs
--{-# INLINE fitnessFunRep #-}


fitnessMV :: ADBackEnd -> Bool -> Bool -> Int -> Int -> Distribution -> [(DataSet, DataSet)] -> Fix SRTree -> RndEGraph (Double, [Target])
fitnessMV backend skipVal shouldReparam nRep nIter distribution dataTrainsVals _tree = do
  let tree = if shouldReparam then relabelParams _tree else relabelParamsOrder _tree
  response <- forM dataTrainsVals $ \(dt, dv) -> fitnessFunRep backend skipVal nRep nIter distribution dt dv tree
  pure (minimum (Prelude.map fst response), Prelude.map snd response)





-- RndEGraph utils
-- fitFun fitnessFunRep rep iter distribution x y mYErr x_val y_val mYErr_val
insertExpr :: Fix SRTree -> (Fix SRTree -> RndEGraph (Double, [Target])) -> RndEGraph EClassId
insertExpr t fitFun = do
    ecId <- fromTree myCost t >>= canonical
    (f, p) <- fitFun t
    insertFitness ecId f p
    pure ecId
  where powabs l r  = Fix (Bin PowerAbs l r)

updateIfNothing fitFun ec = do
      mf <- getFitness ec
      case mf of
        Nothing -> do
          t <- getBestExpr ec
          (f, p) <- fitFun t
          insertFitness ec f p
          pure True
        Just _ -> pure False

pickRndSubTree :: RndEGraph (Maybe EClassId)
pickRndSubTree = do ecIds <- gets (IntSet.toList . _unevaluated . _eDB)
                    if not (null ecIds)
                      then do rndId' <- rnd $ randomFrom ecIds
                              rndId  <- canonical rndId'
                              constType <- (_consts . _info) <$> getEClass rndId
                              case constType of
                                NotConst -> pure $ Just rndId
                                _        -> pure Nothing
                      else pure Nothing

getParetoEcsUpTo n maxSize = concat <$> forM [1..maxSize] (\i -> getTopFitEClassWithSize i n)
getParetoDLEcsUpTo n maxSize = concat <$> forM [1..maxSize] (\i -> getTopDLEClassWithSize i n)

getBestExprWithSize n =
        do ec <- getTopFitEClassWithSize n 1 >>= traverse canonical
           case ec of
             (x:_) -> do bestFit <- getFitness x
                         bestP   <- (_theta . _info) <$> getEClass x
                         pure [(x, bestFit)]
             []    -> pure []

insertRndExpr maxSize rndTerm rndNonTerm =
      do grow <- rnd toss
         n <- rnd (randomFrom [if maxSize > 4 then 4 else 1 .. maxSize])
         t <- rnd $ Random.randomTree 3 8 n rndTerm rndNonTerm grow
         fromTree myCost t >>= canonical

refit fitFun ec = do
  t <- getBestExpr ec
  (f, p) <- fitFun t
  mf <- getFitness ec
  case mf of
    Nothing -> insertFitness ec f p
    Just f' -> when (f > f') $ insertFitness ec f p

--printBest :: (Int -> EClassId -> RndEGraph ()) -> RndEGraph ()
printBest fitFun printExprFun = do
      mbec <- gets (fmap snd . getGreatest . _fitRangeDB . _eDB)
      case mbec of
        Just bec -> do bestFit <- (_fitness . _info) <$> getEClass bec
                       printExprFun 0 bec
        Nothing  -> pure ()

--paretoFront :: Int -> (Int -> EClassId -> RndEGraph ()) -> RndEGraph ()
paretoFront fitFun maxSize printExprFun = go 1 0 (-(1.0/0.0))
    where
    go :: Int -> Int -> Double -> RndEGraph [[String]]
    go n ix f
        | n > maxSize = pure []
        | otherwise   = do
            ecList <- getBestExprWithSize n
            case ecList of
              ((ec, Just f'):_) -> do
                let improved = f' >= f && (not . isNaN) f' && (not . isInfinite) f'
                ec' <- canonical ec
                if improved
                  then do refit fitFun ec'
                          t <- printExprFun ix ec'
                          ts <- go (n+1) (ix + if improved then 1 else 0) (max f f')
                          pure (t:ts)
                  else go (n+1) (ix + if improved then 1 else 0) (max f f')
              _ -> go (n+1) ix f

evaluateUnevaluated fitFun = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          forM_ ec $ \c -> do
              t <- getBestExpr c
              (f, p) <- fitFun t
              insertFitness c f p

evaluateRndUnevaluated fitFun = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          c <- rnd . randomFrom $ ec
          t <- getBestExpr c
          (f, p) <- fitFun t
          insertFitness c f p
          pure c

-- | check whether an e-node exists or does not exist in the e-graph
doesExist, doesNotExist :: ENode -> RndEGraph Bool
doesExist en = gets ((HashMap.member en) . _eNodeToEClass)
doesNotExist en = gets ((not . HashMap.member en) . _eNodeToEClass)

-- | check whether the partial tree defined by a list of ancestors will create
-- a non-existent expression when combined with a certain e-node.
doesNotExistGens :: [Maybe (EClassId -> ENode)] -> ENode -> RndEGraph Bool
doesNotExistGens []              en = gets ((not . HashMap.member en) . _eNodeToEClass)
doesNotExistGens (mGrand:grands) en = do  b <- gets ((not . HashMap.member en) . _eNodeToEClass)
                                          if b
                                            then pure True
                                            else case mGrand of
                                                Nothing -> pure False
                                                Just gf -> do ec  <- gets ((HashMap.! en) . _eNodeToEClass)
                                                              en' <- canonize (gf ec)
                                                              doesNotExistGens grands en'

-- | check whether combining a partial tree `parent` with the e-node `en'`
-- will create a new expression
checkToken parent en' = do  en <- canonize en'
                            mEc <- gets (HashMap.lookup en . _eNodeToEClass)
                            case mEc of
                                Nothing -> pure True
                                Just ec -> do ec' <- canonical ec
                                              ec'' <- canonize (parent ec')
                                              not <$> doesExist ec''
