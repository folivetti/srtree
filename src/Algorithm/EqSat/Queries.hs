{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.EqSat.Queries
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Query functions for e-graphs
-- Heavily based on hegg (https://github.com/alt-romes/hegg by alt-romes)
--
-----------------------------------------------------------------------------

module Algorithm.EqSat.Queries where

import Algorithm.EqSat.Egraph
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.HashSet as Set
import Control.Monad.State ( gets, modify' )
import Control.Monad ( filterM )
import Control.Lens ( over )
import Data.Maybe
import Data.Sequence ( Seq(..) )

import Debug.Trace

-- this is too slow for now, it needs a db of its own
-- basically a db for each query we need
getEClassesThat :: Monad m => (EClass -> Bool) -> EGraphST m [EClassId]
getEClassesThat p = do
    gets (map fst . filter (\(ecId, ec) -> p ec) . IntMap.toList . _eClass)
    --go ecs
        where
            go :: Monad m => [EClassId] -> EGraphST m [EClassId]
            go [] = pure []
            go (ecId:ecs) = do ec <- gets (p . (IntMap.! ecId) . _eClass)
                               ecs' <- go ecs
                               if ec
                                  then pure (ecId:ecs')
                                  else pure ecs'

updateFitness :: Monad m => Double -> EClassId -> EGraphST m ()
updateFitness f ecId = do
   ec   <- gets ((IntMap.! ecId) . _eClass)
   let info = _info ec
   modify' $ over eClass (IntMap.insert ecId ec{_info=info{_fitness = Just f}})

-- | returns all the root e-classes (e-class without parents)
findRootClasses :: Monad m => EGraphST m [EClassId]
findRootClasses = gets (Prelude.map fst . Prelude.filter isParent . IntMap.toList . _eClass)
  where
    isParent (k, v) = Prelude.null (_parents v) ||  (k `Set.member` (Set.map fst (_parents v)))

-- | returns the e-class id with the best fitness that
-- is true to a predicate
getTopECLassThat :: Monad m => Int -> (EClass -> Bool) -> EGraphST m [EClassId]
getTopECLassThat n p = do
  gets (_fitRangeDB . _eDB)
    >>= go n []
  where
    go :: Monad m => Int -> [EClassId] -> RangeTree Double -> EGraphST m [EClassId]
    go 0 bests rt = pure bests
    go m bests rt = case rt of
                       Empty   -> pure bests
                       t :|> y -> do let x = snd y
                                     ecId <- canonical x
                                     ec <- gets ((IntMap.! ecId) . _eClass)
                                     if (isInfinite . fromJust . _fitness . _info $ ec)
                                       then pure bests
                                       else if p ec
                                              then go (m-1) (x:bests) t
                                              else go m bests t
getTopECLassWithSize :: Monad m => Int -> Int -> EGraphST m [EClassId]
getTopECLassWithSize sz n = do
  go n [] <$> gets ((IntMap.!? sz) . _sizeFitDB . _eDB)
  where
    -- go :: Monad m => Int -> [EClassId] -> Maybe (RangeTree Double) -> EGraphST m [EClassId]
    go _ bests Nothing   = []
    go 0 bests (Just rt) = bests
    go m bests (Just rt) = case rt of
                             Empty   -> bests
                             t :|> (f, x) -> if isInfinite f then bests else go (m-1) (x:bests) (Just t)
