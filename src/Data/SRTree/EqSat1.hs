{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.EqSat1
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Equality Saturation for SRTree
--
-----------------------------------------------------------------------------

module Data.SRTree.EqSat1 where

import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Recursion ( cataM )
import Control.Monad
import Control.Monad.State
import Control.Lens ( (+~), (-~), makeLenses, (^.), (.~), (&), element, over )
import Data.IntMap ( IntMap )
import Data.Set ( Set )
import Data.Map ( Map )
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import System.Random
import Data.Ratio
import Debug.Trace
import Data.SRTree.Egraph
import Data.SRTree.EqSatDB
import Data.Maybe ( mapMaybe )
import Data.List ( minimumBy )
import Data.Function ( on )

type Scheduler a = State (IntMap Int) a

fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust _        = error "fromJust called with Nothing"
{-# INLINE fromJust #-}

-- | runs equality saturation from an expression tree,
-- a given set of rules, and a cost function.
-- Returns the tree with the smallest cost.
eqSat :: Fix SRTree -> [Rule] -> CostFun -> EGraphST (Fix SRTree)
eqSat expr rules costFun = do let (root, eg) = fromTree costFun expr
                              put eg
                              runEqSat costFun rules
                              getBest root

type CostMap = Map EClassId (Int, Fix SRTree)

-- | gets the best expression given the default cost function
getBest :: EClassId -> EGraphST (Fix SRTree)
getBest eid = do eid' <- canonical eid
                 best <- gets (_best . _info . (IntMap.! eid') . _eClass)
                 childs <- mapM getBest $ children best
                 pure . Fix $ replaceChildren childs best

-- | recalculates the costs with a new cost function
recalculateBest :: CostFun -> EClassId -> EGraphST (Fix SRTree)
recalculateBest costFun eid =
    do classes <- gets _eClass
       let costs = fillUpCosts classes Map.empty
       eid' <- canonical eid
       pure $ snd $ costs Map.! eid'
    where
        nodeCost :: CostMap -> ENode -> Maybe (Int, Fix SRTree)
        nodeCost costMap enode =
          do optChildren <- traverse (costMap Map.!?) (children enode) -- | gets the cost of the children, if one is missing, returns Nothing
             let cc = map fst optChildren
                 nc = map snd optChildren
                 n  = replaceChildren cc enode
                 c  = costFun n
             pure (c + sum cc, Fix $ replaceChildren nc enode) -- | otherwise, returns the cost of the node + children and the expression so far

        minimumBy' f [] = Nothing
        minimumBy' f xs = Just $ minimumBy f xs

        fillUpCosts :: IntMap EClass -> CostMap -> CostMap
        fillUpCosts classes m =
            case IntMap.foldrWithKey costOfClass (False, m) classes of -- applies costOfClass to each class
              (False, _) -> m
              (True, m') -> fillUpCosts classes m' -- | if something changed, recurse

        costOfClass :: EClassId -> EClass -> (Bool, CostMap) -> (Bool, CostMap)
        costOfClass eid ecl (b, m) =
            let currentCost = m Map.!? eid
                minCost     = minimumBy' (compare `on` fst)  -- get the minimum available cost of the nodes of this class
                            $ mapMaybe (nodeCost m)
                            $ Set.toList (_eNodes ecl)
            in case (currentCost, minCost) of -- replace the costs accordingly
                  (_, Nothing)         -> (b, m)
                  (Nothing, Just new)  -> (True, Map.insert eid new m)
                  (Just old, Just new) -> if fst old <= fst new
                                            then (b, m)
                                            else (True, Map.insert eid new m)

-- | run equality saturation for a number of iterations
runEqSat :: CostFun -> [Rule] -> EGraphST ()
runEqSat costFun rules = go 10 IntMap.empty
    where
        rules' = concatMap replaceEqRules rules

        -- replaces the equality rules with two one-way rules
        replaceEqRules :: Rule -> [Rule]
        replaceEqRules (p1 :=> p2)  = [p1 :=> p2]
        replaceEqRules (p1 :==: p2) = [p1 :=> p2, p2 :=> p1]
        replaceEqRules (r :| cond)  = map (:| cond) $ replaceEqRules r

        go 0  _   = pure ()
        go it sch = do eNodes   <- gets _eNodeToEClass
                       eClasses <- gets _eClass
                       db       <- gets createDB -- creates the DB
                       -- step 1: match the rules
                       let matchSch ruleNumber rule =  matchWithScheduler db it ruleNumber rule
                           matchAll rls             = mapM (uncurry matchSch) $ zip [0..] rls
                           (matches, sch')          = runState (matchAll rules') sch

                       -- step 2: apply matches and rebuild
                       mapM_ (uncurry (applyMatch costFun)) $ concat matches
                       rebuild costFun
                       -- recalculate heights
                       calculateHeights
                       eNodes'   <- gets _eNodeToEClass
                       eClasses' <- gets _eClass
                       -- if nothing changed, return
                       if eNodes' == eNodes && eClasses' == eClasses
                          then pure ()
                          else go (it-1) sch'

-- | matches the rules given a scheduler
matchWithScheduler :: DB -> Int -> Int -> Rule -> Scheduler [(Rule, (Map ClassOrVar ClassOrVar, ClassOrVar))]
matchWithScheduler db it ruleNumber rule =
  do mbBan <- gets (IntMap.!? ruleNumber)
     if False -- mbBan == Nothing || (fromJust mbBan) > it -- check if the rule is banned
        then pure []
        else do let matches = match db (source rule)
                modify (IntMap.insert ruleNumber (it+5))
                pure $ map (rule,) matches
