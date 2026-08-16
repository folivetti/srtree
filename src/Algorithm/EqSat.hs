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
import Control.Monad ( zipWithM, forM_ )

-- | The `Scheduler` stores a map with the banned iterations of a certain rule . 
-- TODO: make it more customizable.
type Scheduler a = State (IntMap Int) a

-- to avoid importing
-- | runs equality saturation from an expression tree,
-- a given set of rules, and a cost function.
-- Returns the tree with the smallest cost.
eqSat :: ClassStore m => Fix SRTree -> [Rule] -> CostFun -> Int -> EGraphST m (Fix SRTree)
eqSat expr rules costFun maxIt =
    do root <- fromTree costFun expr
       _ <- runEqSat costFun rules maxIt
       recalculateBest costFun root

type CostMap = Map EClassId (Int, Fix SRTree)

-- | recalculates the costs with a new cost function
recalculateBest :: ClassStore m => CostFun -> EClassId -> EGraphST m (Fix SRTree)
recalculateBest costFun eid =
    do ecls <- allClasses
       let classes = IntMap.fromList [(_eClassId ec, ec) | ec <- ecls]
           costs   = fillUpCosts classes Map.empty
       eid' <- canonical eid
       case Map.lookup eid' costs of
         Just (_, t) -> pure t
         Nothing     -> error $ "EQSAT_RECALC_MISSING eid=" <> show eid'
                              <> " nClasses=" <> show (IntMap.size classes)
                              <> " costSize=" <> show (Map.size costs)
    where
        nodeCost :: CostMap -> ENode -> (Int, Fix SRTree)
        nodeCost costMap enode =
          -- A child that has not been costed yet (a cycle, or a class whose
          -- cost is computed later in this iteration) contributes a large
          -- sentinel instead of 0: a 0 placeholder is cheaper than the real
          -- cost, so the fixpoint below would keep the stale placeholder tree
          -- (e.g. `x * 0.0` for `x * (y + z)`). Real costs always beat it.
          let (cc, nc) = unzip [ maybe (costSentinel, Fix (Const 0)) id (costMap Map.!? cid) | cid <- eChildren enode ]
              c  = case enode of
                     ENAry op _ -> costFun (Bin (toOp op) 0 0)
                     _          -> costFun (replaceChildren cc (fromENode enode))
          in (c + sum cc, Fix $ case enode of
                 ENAry op _ -> unfix (naryTree op nc)
                 _          -> replaceChildren nc (fromENode enode)) -- | missing children (cyclic classes) get cost 0 so every class is costed
        costSentinel :: Int
        costSentinel = 1000000

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

-- | Recompute every e-class's cost-minimal @_best@/_cost@ bottom-up and write
-- it back into the graph. Needed after loading a graph whose best/cost were
-- not persisted (e.g. via srtree-db), where @_best@ may otherwise hold an
-- arbitrary (potentially large) e-node.
recalculateBestAll :: ClassStore m => CostFun -> EGraphST m ()
recalculateBestAll costFun = do
  ecls <- allClasses
  let classes = IntMap.fromList [(_eClassId ec, ec) | ec <- ecls]
      bests = fixpoint classes IntMap.empty
  forM_ (IntMap.toList bests) $ \(eid, (c, en)) ->
    case IntMap.lookup eid classes of
      Nothing -> pure ()
      Just ec -> writeDirect ec { _info = (_info ec) { _cost = c, _best = en } }
  where
    nodeCost :: IntMap (Int, ENode) -> ENode -> (Int, ENode)
    nodeCost cm en =
      let cc = [ maybe costSentinel fst (IntMap.lookup cid cm) | cid <- eChildren en ]
          c  = case en of
                 ENAry op _ -> costFun (Bin (toOp op) 0 0) + sum cc
                 _          -> costFun (replaceChildren cc (fromENode en)) + sum cc
      in (c, en)
    costSentinel :: Int
    costSentinel = 1000000

    fixpoint :: IntMap EClass -> IntMap (Int, ENode) -> IntMap (Int, ENode)
    fixpoint classes0 = go (IntMap.keysSet classes0)
      where
        go dirty m
          | IntSet.null dirty = m
          | otherwise = go dirty' m'
          where
            (dirty', m') = IntSet.foldl' step (IntSet.empty, m) dirty
            step (d, cm) eid = case IntMap.lookup eid classes0 of
              Nothing -> (d, cm)
              Just ecl ->
                let current = IntMap.lookup eid cm
                    minNode = Set.foldl' (\acc en -> let c = nodeCost cm en
                                                     in case acc of
                                                          Nothing  -> Just c
                                                          Just c'  -> Just (if fst c <= fst c' then c else c'))
                                         Nothing (_eNodes ecl)
                    (changed, cm') = case (current, minNode) of
                      (_, Nothing)        -> (False, cm)
                      (Nothing, Just new) -> (True, IntMap.insert eid new cm)
                      (Just old, Just new)
                        | fst old <= fst new -> (False, cm)
                        | otherwise          -> (True, IntMap.insert eid new cm)
                    d' = if changed
                         then Set.foldl' (\acc (pid, _) -> IntSet.insert pid acc) d (_parents ecl)
                          else d
                 in d' `seq` cm' `seq` (d', cm')

-- | Like 'recalculateBestAll' but streamed: each e-class body is fetched on
-- demand through 'ClassStore' (so a paged graph never materializes every body
-- at once) and only the small @(cost, best e-node)@ map is kept resident. The
-- structural worklist fixpoint is identical.
recalculateBestAllStream :: ClassStore m => CostFun -> EGraphST m ()
recalculateBestAllStream costFun = do
  ids <- allKeys
  let idSet = IntSet.fromList ids
      costSentinel = 1000000
      nodeCost cm en =
        let cc = [ maybe costSentinel fst (IntMap.lookup cid cm) | cid <- eChildren en ]
            c  = case en of
                   ENAry op _ -> costFun (Bin (toOp op) 0 0) + sum cc
                   _          -> costFun (replaceChildren cc (fromENode en)) + sum cc
        in (c, en)
      stepEid cm eid = do
        mec <- readDirect eid
        case mec of
          Nothing -> pure (IntSet.empty, cm)
          Just ecl -> do
            let current = IntMap.lookup eid cm
                minNode = Set.foldl' (\acc en -> let c = nodeCost cm en
                                                 in case acc of
                                                      Nothing  -> Just c
                                                      Just c'  -> Just (if fst c <= fst c' then c else c'))
                                    Nothing (_eNodes ecl)
                (changed, cm') = case (current, minNode) of
                  (_, Nothing)        -> (False, cm)
                  (Nothing, Just new) -> (True, IntMap.insert eid new cm)
                  (Just old, Just new)
                    | fst old <= fst new -> (False, cm)
                    | otherwise          -> (True, IntMap.insert eid new cm)
                dirty = if changed
                          then Set.foldl' (\acc (pid, _) -> IntSet.insert pid acc) IntSet.empty (_parents ecl)
                          else IntSet.empty
            pure (dirty, cm')
      fixpoint dirty cm
        | IntSet.null dirty = pure cm
        | otherwise = go (IntSet.toList dirty) IntSet.empty cm
        where
          go [] d acc = fixpoint d acc
          go (e : es) d acc = do
            (d', m') <- stepEid acc e
            go es (IntSet.union d d') m'
  cm <- fixpoint idSet IntMap.empty
  forM_ (IntMap.toList cm) $ \(eid, (c, en)) -> do
    mec <- readDirect eid
    case mec of
      Nothing -> pure ()
      Just ec -> writeDirect ec { _info = (_info ec) { _cost = c, _best = en } }

-- | Streaming variant of 'recalculateBest': computes the cost-minimal tree for a
-- single root without materializing every e-class body at once.
recalculateBestStream :: ClassStore m => CostFun -> EClassId -> EGraphST m (Fix SRTree)
recalculateBestStream costFun eid = do
  ids <- allKeys
  let idSet = IntSet.fromList ids
      costSentinel = 1000000
      nodeCost cm en =
        let (cc, nc) = unzip [ maybe (costSentinel, Fix (Const 0)) id (Map.lookup cid cm) | cid <- eChildren en ]
            c  = case en of
                   ENAry op _ -> costFun (Bin (toOp op) 0 0)
                   _          -> costFun (replaceChildren cc (fromENode en))
        in (c + sum cc, Fix $ case en of
               ENAry op _ -> unfix (naryTree op nc)
               _          -> replaceChildren nc (fromENode en))
      stepEid cm eid' = do
        mec <- lookupClass eid'
        case mec of
          Nothing -> pure (IntSet.empty, cm)
          Just ecl -> do
            let current = Map.lookup eid' cm
                minCost = Set.foldl' (\acc en -> let c = nodeCost cm en
                                                 in case acc of
                                                      Nothing -> Just c
                                                      Just c' -> Just (if fst c <= fst c' then c else c'))
                                   Nothing (_eNodes ecl)
                (changed, cm') = case (current, minCost) of
                  (_, Nothing) -> (False, cm)
                  (Nothing, Just new) -> (True, Map.insert eid' new cm)
                  (Just old, Just new)
                    | fst old <= fst new -> (False, cm)
                    | otherwise -> (True, Map.insert eid' new cm)
                dirty = if changed
                          then Set.foldl' (\acc (pid,_) -> IntSet.insert pid acc) IntSet.empty (_parents ecl)
                          else IntSet.empty
            pure (dirty, cm')
      fixpoint dirty cm
        | IntSet.null dirty = pure cm
        | otherwise = go (IntSet.toList dirty) IntSet.empty cm
        where
          go [] d acc = fixpoint d acc
          go (e : es) d acc = do
            (d', m') <- stepEid acc e
            go es (IntSet.union d d') m'
  cm <- fixpoint idSet Map.empty
  eid' <- canonical eid
  case Map.lookup eid' cm of
    Just (_, t) -> pure t
    Nothing -> error $ "EQSAT_RECALC_MISSING eid=" <> show eid'
                     <> " costSize=" <> show (Map.size cm)

-- | Run equality saturation and stream the final extraction (see
-- 'recalculateBestStream'), so a paged graph is never fully materialized.
eqSatStream :: ClassStore m => Fix SRTree -> [Rule] -> CostFun -> Int -> EGraphST m (Fix SRTree)
eqSatStream expr rules costFun maxIt = do
  root <- fromTree costFun expr
  _ <- runEqSat costFun rules maxIt
  recalculateBestAllStream costFun
  recalculateBestStream costFun root

-- | replaces the equality rules with two one-way rules
replaceEqRules :: Rule -> [Rule]
replaceEqRules (p1 :=> p2)  = [p1 :=> p2]
replaceEqRules (p1 :==: p2) = [p1 :=> p2, p2 :=> p1]
replaceEqRules (r :| cond)  = map (:| cond) $ replaceEqRules r

-- | Compile a rule source into a query, or `Nothing` for n-ary patterns that
-- use the direct multiset matcher instead.
compileSource :: Rule -> Maybe (Query, [ClassOrVar], ClassOrVar)
compileSource r = if hasNAry (source r)
                    then Nothing
                    else Just (compileToQuery (source r))

-- | Cap on the total number of rule matches applied in a single eqsat
-- iteration. Combined with the per-rule caps ('ruleBudget'/'ruleRootVisit' for
-- n-ary, 'ruleMatchBudget' for the cached path) and the persistent
-- mark-on-attempt seen-set (which makes each rule's budget advance to new
-- matches), this bounds a single iteration's apply/rebuild work regardless of
-- graph size.
iterMatchBudget :: Int
iterMatchBudget = 2000

-- | run equality saturation for a number of iterations
runEqSat :: ClassStore m => CostFun -> [Rule] -> Int -> EGraphST m (Bool, Int)
runEqSat costFun rules maxIter = go maxIter IntMap.empty compiledRules
    where
        rules' = concatMap replaceEqRules rules
        compiledRules = map (\r -> (r, compileSource r)) rules'

        go it sch compiled =
          do -- reset dirty flag before processing this iteration
             modify' $ over (eDB . changed) (const False)

             -- step 1: match the rules using cached compiled queries
             let matchSch  = matchWithScheduler it
                 adapted i (r, cq) = map (,cq) <$> matchSch i r
                 matchAll  = zipWithM adapted [0..]
                 (filtered, sch') = runState (matchAll compiled) sch

             -- step 2: apply matches and rebuild
             matches <- mapM (\(rule, cq) -> map (rule,) <$> case cq of
                                Just q  -> matchCachedWith (Just (show (source rule))) q
                                Nothing -> matchSaturated (source rule)) $ concat filtered
             -- bound the total number of matches applied per iteration so a
             -- single iteration's apply/rebuild work stays bounded on huge
             -- graphs (genuine matches; we just process them over more iters).
             mapM_ (uncurry (applyMatch costFun)) (take iterMatchBudget (concat matches))
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
applySingleMergeOnlyEqSat :: ClassStore m => CostFun -> [Rule] -> EGraphST m ()
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
        getNMatches n ((r:rs):rss) = do matches <- map (r,) <$> matchSaturated (source r)
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
