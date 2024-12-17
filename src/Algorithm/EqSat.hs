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
import Data.List (intercalate, minimumBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.SRTree
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Control.Monad ( zipWithM )

import Debug.Trace

-- | The `Scheduler` stores a map with the banned iterations of a certain rule . 
-- TODO: make it more customizable.
type Scheduler a = State (IntMap Int) a

-- to avoid importing
fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust _        = error "fromJust called with Nothing"
{-# INLINE fromJust #-}

-- | runs equality saturation from an expression tree,
-- a given set of rules, and a cost function.
-- Returns the tree with the smallest cost.
eqSat :: Monad m => Fix SRTree -> [Rule] -> CostFun -> Int -> EGraphST m (Fix SRTree)
eqSat expr rules costFun maxIt =
    do root <- fromTree costFun expr
       (end, it) <- runEqSat costFun rules maxIt
       best      <- getBestExpr root
       --info      <- gets ((IntMap.! root) . _eClass)
       --info2     <- gets ((IntMap.! 9) . _eClass)
       --traceShow (info, info2) $
       if not end -- if had an early stop
         then do modify' (const emptyGraph) >> eqSat best rules costFun it -- reapplies eqsat on the best so far
         else pure best

type CostMap = Map EClassId (Int, Fix SRTree)

-- | recalculates the costs with a new cost function
recalculateBest :: Monad m => CostFun -> EClassId -> EGraphST m (Fix SRTree)
recalculateBest costFun eid =
    do classes <- gets _eClass
       let costs = fillUpCosts classes Map.empty
       eid' <- canonical eid
       pure $ snd $ costs Map.! eid'
    where
        nodeCost :: CostMap -> ENode -> Maybe (Int, Fix SRTree)
        nodeCost costMap enode =
          do optChildren <- traverse (costMap Map.!?) (childrenOf enode) -- | gets the cost of the children, if one is missing, returns Nothing
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
                            $ map decodeEnode
                            $ Set.toList (_eNodes ecl)
            in case (currentCost, minCost) of -- replace the costs accordingly
                  (_, Nothing)         -> (b, m)
                  (Nothing, Just new)  -> (True, Map.insert eid new m)
                  (Just old, Just new) -> if fst old <= fst new
                                            then (b, m)
                                            else (True, Map.insert eid new m)

-- | run equality saturation for a number of iterations
runEqSat :: Monad m => CostFun -> [Rule] -> Int -> EGraphST m (Bool, Int)
runEqSat costFun rules maxIter = go maxIter IntMap.empty
    where
        rules' = concatMap replaceEqRules rules

        -- replaces the equality rules with two one-way rules
        replaceEqRules :: Rule -> [Rule]
        replaceEqRules (p1 :=> p2)  = [p1 :=> p2]
        replaceEqRules (p1 :==: p2) = [p1 :=> p2, p2 :=> p1]
        replaceEqRules (r :| cond)  = map (:| cond) $ replaceEqRules r

        go it sch = do eNodes   <- gets _eNodeToEClass
                       eClasses <- gets _eClass
                       --createDB -- TODO: partial db is still incomplete 
                       --db       <- gets (_patDB . _eDB) -- createDB -- creates the DB

                       -- step 1: match the rules
                       let matchSch        = matchWithScheduler it
                           matchAll        = zipWithM matchSch [0..]
                           (rules, sch') = runState (matchAll rules') sch

                       -- step 2: apply matches and rebuild
                       matches <- mapM (\rule -> map (rule,) <$> match (source rule)) $ concat rules
                       mapM_ (uncurry (applyMatch costFun)) $ concat matches
                       rebuild costFun

                       -- recalculate heights
                       --calculateHeights
                       eNodes'   <- gets _eNodeToEClass
                       eClasses' <- gets _eClass

                       -- if nothing changed, return
                       if it == 1 || (eNodes' == eNodes && eClasses' == eClasses)
                          then pure (True, it)
                          else if IntMap.size eClasses' > 500 -- maximum allowed number of e-classes. TODO: customize
                                 then pure (False, it)
                                 else go (it-1) sch'

-- | apply a single step of merge-only equality saturation
applySingleMergeOnlyEqSat :: Monad m => CostFun -> [Rule] -> EGraphST m ()
applySingleMergeOnlyEqSat costFun rules =
  do db <- gets (_patDB . _eDB) -- createDB
     let matchSch        = matchWithScheduler 10
         matchAll        = zipWithM matchSch [0..]
         (rls, sch')     = runState (matchAll rules') IntMap.empty
     --matches <- mapM (\rule -> map (rule,) <$> match (source rule)) $ concat rls
     --mapM_ (uncurry (applyMergeOnlyMatch costFun)) $ take 500 $ concat matches
     matches <- getNMatches 500 rls
     rebuild costFun
     -- recalculate heights
     --calculateHeights
      where
        rules' = concatMap replaceEqRules rules

        -- replaces the equality rules with two one-way rules
        replaceEqRules :: Rule -> [Rule]
        replaceEqRules (p1 :=> p2)  = [p1 :=> p2]
        replaceEqRules (p1 :==: p2) = [p1 :=> p2, p2 :=> p1]
        replaceEqRules (r :| cond)  = map (:| cond) $ replaceEqRules r

        getNMatches n []       = pure []
        getNMatches 0 _        = pure []
        getNMatches n ([]:rss) = getNMatches n rss
        getNMatches n ((r:rs):rss) = do matches <- map (r,) <$> match (source r)
                                        let (x, y) = splitAt n matches
                                            m      = length x
                                        if m == n
                                           then pure matches
                                           else do matches' <- getNMatches (n - length x) (rs:rss)
                                                   pure (matches <> matches')


-- | matches the rules given a scheduler
matchWithScheduler :: Int -> Int -> Rule -> Scheduler [Rule] -- [(Rule, (Map ClassOrVar ClassOrVar, ClassOrVar))]
matchWithScheduler it ruleNumber rule =
  do mbBan <- gets (IntMap.!? ruleNumber)
     if mbBan /= Nothing && fromJust mbBan <= it -- check if the rule is banned
        then pure []
        else do -- let matches = match db (source rule)
                modify (IntMap.insert ruleNumber (it+5))
                pure [rule] -- $ map (rule,) matches
