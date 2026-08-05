{-# LANGUAGE TupleSections #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.EqSat
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Equality Saturation for SRTree
-- Heavily based on hegg (https://github.com/alt-romes/hegg by alt-romes)
--
-----------------------------------------------------------------------------

module Algorithm.EqSat where

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.DB
import Algorithm.EqSat.Info
import Algorithm.EqSat.Build
import Control.Lens (element, makeLenses, over, (&), (+~), (-~), (.~), (^.))
import Control.Monad.State
import Data.Function (on)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.SRTree
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Control.Monad ( zipWithM )

-- | The `Scheduler` stores a map with the banned iterations of a certain rule . 
-- TODO: make it more customizable.
type Scheduler a = State (IntMap Int) a

-- to avoid importing
-- | runs equality saturation from an expression tree,
-- a given set of rules, and a cost function.
-- Returns the tree with the smallest cost.
eqSat :: Monad m => Fix SRTree -> [Rule] -> CostFun -> Int -> EGraphST m (Fix SRTree)
eqSat expr rules costFun maxIt =
    do root <- fromTree costFun expr
       _ <- runEqSat costFun rules maxIt
       recalculateBest costFun root

type CostMap = Map EClassId (Int, Fix SRTree)

-- | recalculates the costs with a new cost function
recalculateBest :: Monad m => CostFun -> EClassId -> EGraphST m (Fix SRTree)
recalculateBest costFun eid =
    do classes <- gets _eClass
       let costs = fillUpCosts classes Map.empty
       eid' <- canonical eid
       case Map.lookup eid' costs of
         Just (_, t) -> pure t
         Nothing     -> error $ "EQSAT_RECALC_MISSING eid=" <> show eid'
                              <> " nClasses=" <> show (IntMap.size classes)
                              <> " costSize=" <> show (Map.size costs)
    where
        nodeCost :: CostMap -> ENode -> (Int, Fix SRTree)
        nodeCost costMap enode =
          let (cc, nc) = unzip [ maybe (0, Fix (Const 0)) id (costMap Map.!? cid) | cid <- childrenOf enode ]
              n  = replaceChildren cc enode
              c  = costFun n
          in (c + sum cc, Fix $ replaceChildren nc enode) -- | missing children (cyclic classes) get cost 0 so every class is costed

        fillUpCosts :: IntMap EClass -> CostMap -> CostMap
        fillUpCosts classes = go (IntMap.keysSet classes)
          where
            go dirty m
              | IntSet.null dirty = m
              | otherwise = go dirty' m'
              where
                (dirty', m') = IntSet.foldl' step (IntSet.empty, m) dirty
                step (d, cm) eid = case IntMap.lookup eid classes of
                  Nothing -> (d, cm)
                  Just ecl ->
                    let currentCost = Map.lookup eid cm
                        minCost     = Set.foldl' (\acc en -> let c = nodeCost cm en
                                                  in case acc of
                                                    Nothing  -> Just c
                                                    Just c'  -> Just (if fst c <= fst c' then c else c')
                                                ) Nothing (_eNodes ecl)
                        (changed, cm') = case (currentCost, minCost) of
                          (_, Nothing)            -> (False, cm)
                          (Nothing, Just new)     -> (True, Map.insert eid new cm)
                          (Just old, Just new)
                            | fst old <= fst new  -> (False, cm)
                            | otherwise           -> (True, Map.insert eid new cm)
                        d' = if changed
                             then Set.foldl' (\acc (pid, _) -> IntSet.insert pid acc) d (_parents ecl)
                             else d
                    in d' `seq` cm' `seq` (d', cm')

-- | replaces the equality rules with two one-way rules
replaceEqRules :: Rule -> [Rule]
replaceEqRules (p1 :=> p2)  = [p1 :=> p2]
replaceEqRules (p1 :==: p2) = [p1 :=> p2, p2 :=> p1]
replaceEqRules (r :| cond)  = map (:| cond) $ replaceEqRules r

-- | run equality saturation for a number of iterations
runEqSat :: Monad m => CostFun -> [Rule] -> Int -> EGraphST m (Bool, Int)
runEqSat costFun rules maxIter = go maxIter IntMap.empty compiledRules
    where
        rules' = concatMap replaceEqRules rules
        compiledRules = map (\r -> (r, compileToQuery (source r))) rules'

        go it sch compiled =
          do -- reset dirty flag before processing this iteration
             modify' $ over (eDB . changed) (const False)

             -- step 1: match the rules using cached compiled queries
             let matchSch  = matchWithScheduler it
                 adapted i (r, cq) = map (,cq) <$> matchSch i r
                 matchAll  = zipWithM adapted [0..]
                 (filtered, sch') = runState (matchAll compiled) sch

             -- step 2: apply matches and rebuild
             matches <- mapM (\(rule, (q, vars, root)) -> map (rule,) <$> matchCached (q, vars, root)) $ concat filtered
             mapM_ (uncurry (applyMatch costFun)) $ concat matches
             rebuild costFun

             -- check dirty flag: if no modifications occurred, we've saturated
             changed <- gets (_changed . _eDB)
             if it == 1 || not changed
                then pure (True, it)
                 else
                   do eClasses <- gets _eClass
                      if IntMap.size eClasses > 1500
                        then throttle it sch' compiled
                        else go (it-1) sch' compiled

        throttle it sch compiled = do
          cleanMaps
          eClasses <- gets _eClass
          if IntMap.size eClasses <= 1500
            then go (it-1) sch compiled
            else do applySingleMergeOnlyEqSat costFun rules
                    changed <- gets (_changed . _eDB)
                    if it <= 1 || not changed
                      then pure (False, it)  -- give up and return early stop
                      else throttle (it-1) sch compiled

-- | apply a single step of merge-only equality saturation
applySingleMergeOnlyEqSat :: Monad m => CostFun -> [Rule] -> EGraphST m ()
applySingleMergeOnlyEqSat costFun rules =
  do let matchSch        = matchWithScheduler 10
         matchAll        = zipWithM matchSch [0..]
         (rls, _)        = runState (matchAll rules') IntMap.empty
     matches <- getNMatches 500 rls
     rebuild costFun
      where
        rules' = concatMap replaceEqRules rules

        getNMatches n []       = pure []
        getNMatches 0 _        = pure []
        getNMatches n ([]:rss) = getNMatches n rss
        getNMatches n ((r:rs):rss) = do matches <- map (r,) <$> match (source r)
                                        let (x, _) = splitAt n matches
                                            m      = length x
                                        if m == n
                                           then pure matches
                                           else do matches' <- getNMatches (n - length x) (rs:rss)
                                                   pure (matches <> matches')


-- | matches the rules given a scheduler
matchWithScheduler :: Int -> Int -> Rule -> Scheduler [Rule] -- [(Rule, (Map ClassOrVar ClassOrVar, ClassOrVar))]
matchWithScheduler it ruleNumber rule =
  do mbBan <- gets (IntMap.!? ruleNumber)
     if maybe False (<= it) mbBan -- check if the rule is banned
        then pure []
        else do -- let matches = match db (source rule)
                modify (IntMap.insert ruleNumber (it+5))
                pure [rule] -- $ map (rule,) matches
