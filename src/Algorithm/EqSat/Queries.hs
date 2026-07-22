{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
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
import qualified Data.Set as RangeSet
import Control.Monad.State ( gets, modify' )
import Control.Monad ( filterM )
import Control.Lens ( over )
import Data.Maybe
import Data.SRTree (childrenOf)

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
            go (ecId:ecs) = do ec <- p <$> getEClass ecId
                               ecs' <- go ecs
                               if ec
                                  then pure (ecId:ecs')
                                  else pure ecs'

updateFitness :: Monad m => Double -> EClassId -> EGraphST m ()
updateFitness f ecId = do
   ec   <- getEClass ecId
   let info = _info ec
   modify' $ over eClass (IntMap.insert ecId ec{_info=info{_fitness = Just f}})

-- | returns all the root e-classes (e-class without parents)
findRootClasses :: Monad m => EGraphST m [EClassId]
findRootClasses = gets (Prelude.map fst . Prelude.filter isParent . IntMap.toList . _eClass)
  where
    isParent (k, v) = Prelude.null (_parents v) ||  (k `Set.member` (Set.map fst (_parents v)))

-- | returns the e-class id with the best fitness that
-- is true to a predicate
getTopECLassThat :: Monad m => Bool -> Int -> (EClass -> Bool) -> EGraphST m [EClassId]
getTopECLassThat b n p = do
  let f = if b then _fitRangeDB else _dlRangeDB
  gets (f . _eDB)
    >>= go n []
  where
    go :: Monad m => Int -> [EClassId] -> RangeTree Double -> EGraphST m [EClassId]
    go 0 bests rt = pure bests
    go m bests rt = case RangeSet.maxView rt of
                       Nothing -> pure bests
                       Just (y, t) ->
                         let x = snd y
                         in do ecId <- canonical x
                               ec <- getEClass ecId
                               if (maybe True (isInfinite) . _fitness . _info $ ec)
                                 then go m bests t
                                 else if p ec
                                   then go (m-1) (ecId:bests) t
                                   else go m bests t

getTopEClassInRange :: Monad m => Bool -> Int -> (EClass -> Double) -> [(Double, Double)] -> EGraphST m [EClassId]
getTopEClassInRange b n p range = do
  let f = if b then _fitRangeDB else _dlRangeDB
  gets (f . _eDB)
    >>= go n [] range
  where
    inRange v (x, y)
      | v >= x && v <= y = 0
      | v < x = -1
      | v > y = 1
      | otherwise = 1 

    go :: Monad m => Int -> [EClassId] -> [(Double, Double)] -> RangeTree Double -> EGraphST m [EClassId]
    go _ bests []      _ = pure bests 
    go 0 bests (r:rs) rt = go n bests rs rt
    go m bests (r:rs) rt = case RangeSet.maxView rt of
                             Nothing -> pure bests
                             Just (y, t) ->
                               let x = snd y
                               in do ecId <- canonical x
                                     ec <- getEClass ecId
                                     if (maybe True (isInfinite) . _fitness . _info $ ec)
                                       then go m bests (r:rs) t
                                       else do let v = p ec
                                               case (v `inRange` r) of
                                                 0  -> go (m-1) (ecId:bests) (r:rs) t
                                                 -1 -> go n bests rs (RangeSet.insert y t)
                                                 1  -> go m bests (r:rs) t

getTopECLassIn :: Monad m => Bool -> Int -> (EClass -> Bool) -> [EClassId] -> EGraphST m [EClassId]
getTopECLassIn b n p ecs' = do
  let f = if b then _fitRangeDB else _dlRangeDB
  gets (f . _eDB)
    >>= go n []
  where
    ecs = Set.fromList ecs'
    go :: Monad m => Int -> [EClassId] -> RangeTree Double -> EGraphST m [EClassId]
    go 0 bests rt = pure bests
    go m bests rt = case RangeSet.maxView rt of
                       Nothing -> pure bests
                       Just (y, t) ->
                         let x = snd y
                         in do ecId <- canonical x
                               ec <- getEClass ecId
                               if (maybe True (isInfinite) . _fitness . _info $ ec)
                                 then go m bests t
                                 else if ecId `Set.member` ecs && p ec
                                   then go (m-1) (ecId:bests) t
                                   else go m bests t

getTopECLassNotIn :: Monad m => Bool -> Int -> (EClass -> Bool) -> [EClassId] -> EGraphST m [EClassId]
getTopECLassNotIn b n p ecs' = do
  let f = if b then _fitRangeDB else _dlRangeDB
  gets (f . _eDB)
    >>= go n []
  where
    ecs = Set.fromList ecs'

    go :: Monad m => Int -> [EClassId] -> RangeTree Double -> EGraphST m [EClassId]
    go 0 bests rt = pure bests
    go m bests rt = case RangeSet.maxView rt of
                       Nothing -> pure bests
                       Just (y, t) ->
                         let x = snd y
                         in do ecId <- canonical x
                               ec <- getEClass ecId
                               if (maybe True (isInfinite) . _fitness . _info $ ec)
                                 then go m bests t
                                 else if not (ecId `Set.member` ecs) && p ec
                                   then go (m-1) (ecId:bests) t
                                   else go m bests t

getAllEvaluatedEClasses :: Monad m => EGraphST m [EClassId]
getAllEvaluatedEClasses = do
  gets (_fitRangeDB . _eDB)
    >>= go []
  where
    go :: Monad m => [EClassId] -> RangeTree Double -> EGraphST m [EClassId]
    go bests rt = case RangeSet.maxView rt of
                    Nothing -> pure bests
                    Just (y, t) ->
                      let x = snd y
                      in do ecId <- canonical x
                            ec <- getEClass ecId
                            if (maybe True (isInfinite) . _fitness . _info $ ec)
                              then go bests t
                              else go (ecId:bests) t

getTopEClassWithSize :: Monad m => Bool -> Int -> Int -> EGraphST m [EClassId]
getTopEClassWithSize b sz n = do
   let fun = if b then _sizeFitDB else _sizeDLDB
   gets (go n [] . (IntMap.!? sz) . fun . _eDB)
  where
    go _ bests Nothing   = []
    go 0 bests (Just rt) = bests
    go m bests (Just rt) = case RangeSet.maxView rt of
                             Nothing         -> bests
                             Just ((f, x), t) -> if isInfinite f || isNaN f then go m bests (Just t) else go (m-1) (x:bests) (Just t)

getTopFitEClassThat :: Monad m => Int -> (EClass -> Bool) -> EGraphST m [EClassId]
getTopFitEClassThat  = getTopECLassThat True
getTopDLEClassThat :: Monad m => Int -> (EClass -> Bool) -> EGraphST m [EClassId]
getTopDLEClassThat   = getTopECLassThat False
getTopFitEClassIn :: Monad m =>  Int -> (EClass -> Bool) -> [EClassId] -> EGraphST m [EClassId]
getTopFitEClassIn    = getTopECLassIn True
getTopDLEClassIn :: Monad m => Int -> (EClass -> Bool) -> [EClassId] -> EGraphST m [EClassId]
getTopDLEClassIn     = getTopECLassIn False
getTopFitEClassNotIn :: Monad m => Int -> (EClass -> Bool) -> [EClassId] -> EGraphST m [EClassId]
getTopFitEClassNotIn = getTopECLassNotIn True
getTopDLEClassNotIn :: Monad m => Int -> (EClass -> Bool) -> [EClassId] -> EGraphST m [EClassId]
getTopDLEClassNotIn  = getTopECLassNotIn True
getTopFitEClassWithSize :: Monad m => Int -> Int -> EGraphST m [EClassId]
getTopFitEClassWithSize = getTopEClassWithSize True
getTopDLEClassWithSize :: Monad m => Int -> Int -> EGraphST m [EClassId]
getTopDLEClassWithSize  = getTopEClassWithSize False

rebuildAllRanges :: Monad m => EGraphST m ()
rebuildAllRanges = do szF <- gets (_sizeFitDB._eDB) >>= traverse rebuildRange
                      dlF <- gets (_sizeDLDB._eDB) >>= traverse rebuildRange
                      fR  <- gets (_fitRangeDB._eDB) >>= rebuildRange
                      dR  <- gets (_dlRangeDB._eDB) >>= rebuildRange

                      modify' $ over (eDB.fitRangeDB) (const fR)
                              . over (eDB.dlRangeDB) (const dR)
                              . over (eDB.sizeFitDB) (const szF)
                              . over (eDB.sizeDLDB) (const dlF)

canonizeRange :: Monad m => RangeTree Double -> EGraphST m (RangeTree Double)
canonizeRange = fmap RangeSet.fromList . mapM (\(x, eid) -> (x,) <$> canonical eid) . RangeSet.toList

rebuildRange :: Monad m => RangeTree Double -> EGraphST m (RangeTree Double)
rebuildRange rt = do
  canonRt <- canonizeRange rt
  pure $ snd $ go canonRt
  where
    go rt' = case RangeSet.maxView rt' of
               Nothing -> (Set.empty, RangeSet.empty)
               Just ((x, eid), rest) ->
                 let (seen, result) = go rest
                 in if Set.member eid seen
                      then (seen, result)
                      else (Set.insert eid seen, RangeSet.insert (x, eid) result)

