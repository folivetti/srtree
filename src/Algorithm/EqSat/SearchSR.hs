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
import System.Random
import Control.Monad.State.Strict
import Algorithm.EqSat.Egraph
import Algorithm.SRTree.Likelihoods
import qualified Data.IntMap as IM
import qualified Data.IntSet as IntSet
import qualified Data.SRTree.Random as Random
import Data.Function ( on )
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.NonlinearOpt
import Control.Monad ( when, replicateM, forM, forM_ )
import Algorithm.EqSat.Egraph
import Algorithm.SRTree.Opt
import Algorithm.EqSat.Info
import Algorithm.EqSat.Build
import Data.Maybe ( fromJust )
import Data.SRTree.Random
import Algorithm.EqSat.Queries
import Data.List ( maximumBy )
import qualified Data.Map.Strict as Map
import Control.Monad.Identity

-- Environment of an e-graph with support to random generator and IO
type RndEGraph a = EGraphST (StateT StdGen (StateT [ECache] IO)) a

io :: IO a -> RndEGraph a
io = lift . lift . lift
{-# INLINE io #-}
getCache :: StateT [ECache] IO a -> RndEGraph a
getCache = lift . lift
rnd :: StateT StdGen (StateT [ECache] IO)  a -> RndEGraph a
rnd = lift
{-# INLINE rnd #-}

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

fitnessFun :: Int -> Distribution -> DataSet -> DataSet -> EGraph -> EClassId -> ECache -> PVector -> (Double, PVector, ECache)
fitnessFun nIter distribution (x, y, mYErr) (x_val, y_val, mYErr_val) egraph root cache thetaOrig =
  if isNaN val -- || isNaN tr
    then (-(1/0), theta,cache') -- infinity
    else (val, theta, cache')
  where
    tree          = runIdentity $ getBestExpr root `evalStateT` egraph
    nParams       = countParamsUniqEg egraph root + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    (theta, _, _, cache') = minimizeNLLEGraph VAR1 distribution mYErr nIter x y egraph root cache thetaOrig
    evalF a b c   = negate $ nll distribution c a b tree $ if nParams == 0 then thetaOrig else theta
    val           = evalF x_val y_val mYErr_val

--{-# INLINE fitnessFun #-}

fitnessFunRep :: Int -> Int -> Distribution -> DataSet -> DataSet -> EClassId -> ECache -> RndEGraph (Double, PVector, ECache)
fitnessFunRep nRep nIter distribution dataTrain dataVal root cache = do
    egraph <- get
    let nParams = countParamsUniqEg egraph root + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
        fst' (a, _, _) = a
    thetaOrigs <- replicateM nRep (rnd $ randomVec nParams)
    let fits = maximumBy (compare `on` fst') $ Prelude.map (fitnessFun nIter distribution dataTrain dataVal egraph root cache) thetaOrigs
    pure fits
--{-# INLINE fitnessFunRep #-}


fitnessMV :: Bool -> Int -> Int -> Distribution -> [(DataSet, DataSet)] -> EClassId -> RndEGraph (Double, [PVector])
fitnessMV shouldReparam nRep nIter distribution dataTrainsVals root = do
  -- let tree = if shouldReparam then relabelParams _tree else relabelParamsOrder _tree
  -- WARNING: this should be done BEFORE inserting into egraph, so it's up to the algorithm'
  caches <- getCache get
  response <- forM (Prelude.zip dataTrainsVals caches) $ \((dt, dv), cache) -> fitnessFunRep nRep nIter distribution dt dv root cache
  getCache $ put (Prelude.map trd response)
  pure (minimum (Prelude.map fst' response), Prelude.map snd' response)
  where fst' (a, _, _) = a
        snd' (_, a, _) = a
        trd  (_, _, a) = a




-- RndEGraph utils
-- fitFun fitnessFunRep rep iter distribution x y mYErr x_val y_val mYErr_val
insertExpr :: Fix SRTree -> (Fix SRTree -> RndEGraph (Double, [PVector])) -> RndEGraph EClassId
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
          (f, p, c) <- fitFun t
          insertFitness ec f p
          pure True
        Just _ -> pure False

pickRndSubTree :: RndEGraph (Maybe EClassId)
pickRndSubTree = do ecIds <- gets (IntSet.toList . _unevaluated . _eDB)
                    if not (null ecIds)
                          then do rndId' <- rnd $ randomFrom ecIds
                                  rndId  <- canonical rndId'
                                  constType <- gets (_consts . _info . (IM.! rndId) . _eClass)
                                  case constType of
                                    NotConst -> pure $ Just rndId
                                    _        -> pure Nothing
                          else pure Nothing

getParetoEcsUpTo n maxSize = concat <$> forM [1..maxSize] (\i -> getTopFitEClassWithSize i n)
getParetoDLEcsUpTo n maxSize = concat <$> forM [1..maxSize] (\i -> getTopDLEClassWithSize i n)

getBestExprWithSize n =
        do ec <- getTopFitEClassWithSize n 1 >>= traverse canonical
           if (not (null ec))
            then do
              bestFit <- getFitness $ head ec
              bestP   <- gets (_theta . _info . (IM.! (head ec)) . _eClass)
              pure [(head ec, bestFit)]
            else pure []

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
      bec <- gets (snd . getGreatest . _fitRangeDB . _eDB) >>= canonical
      bestFit <- gets (_fitness. _info . (IM.! bec) . _eClass)
      --refit fitFun bec
      --io.print $ "should be " <> show bestFit
      printExprFun 0 bec

--paretoFront :: Int -> (Int -> EClassId -> RndEGraph ()) -> RndEGraph ()
paretoFront fitFun maxSize printExprFun = go 1 0 (-(1.0/0.0))
    where
    go :: Int -> Int -> Double -> RndEGraph [[String]]
    go n ix f
        | n > maxSize = pure []
        | otherwise   = do
            ecList <- getBestExprWithSize n
            if not (null ecList)
                then do let (ec, mf) = head ecList
                            f' = fromJust mf
                            improved = f' >= f && (not . isNaN) f' && (not . isInfinite) f'
                        ec' <- canonical ec
                        if improved
                                then do refit fitFun ec'
                                        t <- printExprFun ix ec'
                                        ts <- go (n+1) (ix + if improved then 1 else 0) (max f f')
                                        pure (t:ts)
                                else go (n+1) (ix + if improved then 1 else 0) (max f f')
                else go (n+1) ix f

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
doesExist en = gets ((Map.member en) . _eNodeToEClass)
doesNotExist en = gets ((Map.notMember en) . _eNodeToEClass)

-- | check whether the partial tree defined by a list of ancestors will create
-- a non-existent expression when combined with a certain e-node.
doesNotExistGens :: [Maybe (EClassId -> ENode)] -> ENode -> RndEGraph Bool
doesNotExistGens []              en = gets ((Map.notMember en) . _eNodeToEClass)
doesNotExistGens (mGrand:grands) en = do  b <- gets ((Map.notMember en) . _eNodeToEClass)
                                          if b
                                            then pure True
                                            else case mGrand of
                                                Nothing -> pure False
                                                Just gf -> do ec  <- gets ((Map.! en) . _eNodeToEClass)
                                                              en' <- canonize (gf ec)
                                                              doesNotExistGens grands en'

-- | check whether combining a partial tree `parent` with the e-node `en'`
-- will create a new expression
checkToken parent en' = do  en <- canonize en'
                            mEc <- gets ((Map.!? en) . _eNodeToEClass)
                            case mEc of
                                Nothing -> pure True
                                Just ec -> do ec' <- canonical ec
                                              ec'' <- canonize (parent ec')
                                              not <$> doesExist ec''
