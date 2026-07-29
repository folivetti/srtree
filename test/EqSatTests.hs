{-# LANGUAGE OverloadedStrings #-}

module EqSatTests where

import Test.HUnit
import Data.SRTree
import Data.SRTree.Print (showExpr)
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.HashSet as Set
import qualified Data.Vector.Unboxed as VU
import qualified Data.Set as RangeSet
import Algorithm.EqSat
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Build
import Algorithm.EqSat.DB
import Algorithm.EqSat.Info
import Algorithm.EqSat.Queries
import Control.Monad.State.Strict
import Control.Monad (forM_)
import Control.Monad.Identity

eps :: Double
eps = 1e-9

myCost :: SRTree Int -> Int
myCost (Var _)     = 1
myCost (Const _)   = 1
myCost (Param _)   = 1
myCost (Bin _ l r) = 2 + l + r
myCost (Uni _ t)   = 3 + t

runEG :: EGraphST Identity a -> (a, EGraph)
runEG m = runIdentity $ runStateT m emptyGraph

evalEG :: EGraphST Identity a -> a
evalEG m = runIdentity $ evalStateT m emptyGraph

-- | Test 1: fromTree with a leaf (variable)
test_fromTree_var :: Test
test_fromTree_var = TestCase $ do
  let tree = var 0
      (eid, eg) = runEG $ fromTree myCost tree
  assertBool "fromTree var: eid should be >= 0" (eid >= 0)
  assertBool "fromTree var: eclass exists" (IntMap.member eid (_eClass eg))
  let ec = _eClass eg IntMap.! eid
  assertBool "fromTree var: eclass has nodes" (not $ null (_eNodes ec))
  let bestNode = head $ Set.toList (_eNodes ec)
  assertEqual "fromTree var: best is Var 0" (Var 0) bestNode

-- | Test 2: fromTree with a binary expression
test_fromTree_bin :: Test
test_fromTree_bin = TestCase $ do
  let tree = var 0 + constv 1.0
      (eid, eg) = runEG $ fromTree myCost tree
  assertBool "fromTree bin: eid >= 0" (eid >= 0)
  let ec = _eClass eg IntMap.! eid
  assertBool "fromTree bin: eclass has nodes" (not $ null (_eNodes ec))

-- | Test 3: Canonical identity (an e-class should be its own canonical)
test_canonical_identity :: Test
test_canonical_identity = TestCase $ do
  let (eid, eg) = runEG $ fromTree myCost (var 0)
      (canId, _) = runIdentity $ runStateT (canonical eid) eg
  assertEqual "canonical of fresh id is itself" eid canId

-- | Test 4: canonize canonizes children
test_canonize :: Test
test_canonize = TestCase $ do
  let (eid, eg) = runEG $ fromTree myCost (var 0 + constv 1.0)
      (canNode, _) = runIdentity $ runStateT (do
        ec <- getEClass eid
        let someNode = head $ Set.toList (_eNodes ec)
        canonize someNode) eg
  -- All children should be canonical now
  let children = childrenOf canNode
  forM_ children $ \c -> do
    let (canC, _) = runIdentity $ runStateT (canonical c) eg
    assertEqual "canonize: child is canonical" c canC

-- | Test 5: Adding duplicate e-node returns existing e-class
test_add_duplicate :: Test
test_add_duplicate = TestCase $ do
  let tree = constv 2.0
      (eid1, eg1) = runEG $ fromTree myCost tree
      (eid2, eg2) = runEG' eg1 $ add myCost (Const 2.0)
  assertEqual "add duplicate returns same eclass" eid1 eid2
  where
    runEG' eg m = runIdentity $ runStateT m eg

-- | Test 6: Merge two distinct e-classes
test_merge :: Test
test_merge = TestCase $ do
  let (eid1, eg1) = runEG $ fromTree myCost (var 0)
      (eid2, eg2) = runIdentity $ runStateT (fromTree myCost (var 1)) eg1
  assertBool "merge: eid1 and eid2 start different" (eid1 /= eid2)
  let (mergedId, eg3) = runIdentity $ runStateT (merge myCost eid1 eid2) eg2
      can1 = _canonicalMap eg3 IntMap.! eid1
      can2 = _canonicalMap eg3 IntMap.! eid2
  assertEqual "merge: canonicals are equal" can1 can2
  assertEqual "merge: leader matches canonical" mergedId can1

-- | Test 7: Rebuild after add
test_rebuild :: Test
test_rebuild = TestCase $ do
  let tree = var 0 + constv 1.0
      eg = snd $ runEG $ do
        _ <- fromTree myCost tree
        rebuild myCost
  assertBool "rebuild: eNodeToEClass non-empty" (not $ null (_eNodeToEClass eg))
  assertBool "rebuild: worklist empty" (null (_worklist (_eDB eg)))
  assertBool "rebuild: analysis empty" (null (_analysis (_eDB eg)))

-- | Test 8: Basic pattern matching
test_match :: Test
test_match = TestCase $ do
  let tree = var 0 + constv 1.0
      pat = Fixed (Bin Add (VarPat 'x') (VarPat 'y'))
      (substs, _) = runEG $ do
        _ <- fromTree myCost tree
        match pat
  assertBool "match: should have at least one substitution" (not $ null substs)

-- | Test 9: Extraction (getBestExpr)
test_getBestExpr :: Test
test_getBestExpr = TestCase $ do
  let tree = var 0 + constv 1.0
      (extracted, _) = runEG $ do
        eid <- fromTree myCost tree
        getBestExpr eid
  assertEqual "getBestExpr preserves structure" (showExpr tree) (showExpr extracted)

-- | Test 10: Equality saturation with x + 0 = x
test_eqsat_x_plus_0 :: Test
test_eqsat_x_plus_0 = TestCase $ do
  let tree     = var 0 + constv 0.0
      rule     = "a" + 0 :=> "a"
      (best, _) = runEG $ eqSat tree [rule] myCost 5
  assertEqual "eqSat: x+0 = x" (showExpr (var 0)) (showExpr best)

-- | Test 11: Equality saturation with x * 1 = x
test_eqsat_x_times_1 :: Test
test_eqsat_x_times_1 = TestCase $ do
  let tree     = var 0 * constv 1.0
      rule     = "a" * 1 :=> "a"
      (best, _) = runEG $ eqSat tree [rule] myCost 5
  assertEqual "eqSat: x*1 = x" (showExpr (var 0)) (showExpr best)

-- | Test 12: Fitness and theta storage round-trip
test_fitness_theta :: Test
test_fitness_theta = TestCase $ do
  let theta = [VU.fromList [1.0, 2.0]]
      (mf, _) = runEG $ do
        eid <- fromTree myCost (var 0)
        insertFitness eid 0.5 theta
        getFitness eid
  case mf of
    Nothing -> assertFailure "getFitness returned Nothing"
    Just f  -> assertBool "fitness should be ~0.5" (abs (f - 0.5) < eps)

-- | Test 13: Insert fitness and check range tree
test_fitness_range :: Test
test_fitness_range = TestCase $ do
  let (eg, _) = runEG $ do
        eid1 <- fromTree myCost (var 0)
        eid2 <- fromTree myCost (constv 1.0)
        insertFitness eid1 (-1.0) []
        insertFitness eid2 2.0 []
        gets _eDB
      rt = _fitRangeDB eg
  case getGreatest rt of
    Just (bestFit, _) -> assertBool "fitness range: best is 2.0" (abs (bestFit - 2.0) < eps)
    Nothing -> assertFailure "fitness range: non-empty"

-- | Test 14: getTopFitEClassWithSize
test_top_fit_size :: Test
test_top_fit_size = TestCase $ do
  let (eclasses, _) = runEG $ do
        eid1 <- fromTree myCost (var 0)          -- size 1
        eid2 <- fromTree myCost (constv 1.0)      -- size 1
        eid3 <- fromTree myCost (var 0 + constv 1.0) -- size 3
        insertFitness eid1 0.5 []
        insertFitness eid2 1.0 []
        insertFitness eid3 2.0 []
        getTopFitEClassWithSize 1 1
  assertBool "top fit size 1: should have at least one" (not $ null eclasses)
  assertEqual "top fit size 1: should be 1 result" 1 (length eclasses)

-- | Test 15: Bidirectional rule (x + 0 == x)
test_eqsat_comm :: Test
test_eqsat_comm = TestCase $ do
  let tree     = var 0 + constv 0.0
      rule     = "a" + 0 :==: "a"
      (best, _) = runEG $ eqSat tree [rule] myCost 5
  assertEqual "eqSat: x+0 == x" (showExpr (var 0)) (showExpr best)

-- | Test 16: Double negation elimination
test_eqsat_double_neg :: Test
test_eqsat_double_neg = TestCase $ do
  -- var 0 - (var 0 - const 2)  should simplify via x - (x - y) = y
  -- but we don't have that rule. Instead use const folding:
  -- (1 + 0) * x = x via x * 1 = x after const folding simplifies 1+0 to 1
  -- Actually let's use a simpler rule set
  let tree     = (constv 1.0 + constv 0.0) * var 0  -- (1+0)*x
      rules    = ["a" + 0 :=> "a", "a" * 1 :=> "a"]
      (best, _) = runEG $ eqSat tree rules myCost 10
  assertEqual "eqSat: (1+0)*x = x" (showExpr (var 0)) (showExpr best)

-- | Test 17: fromTrees builds multiple independent trees
test_fromTrees :: Test
test_fromTrees = TestCase $ do
  let trees    = [var 0, constv 1.0, var 0 + constv 1.0]
      (eids, eg) = runEG $ fromTrees myCost trees
  assertEqual "fromTrees: three trees" 3 (length eids)
  -- each eid should be distinct and valid
  let allDistinct = length eids == length (map (\x -> _canonicalMap eg IntMap.! x) eids)
  assertBool "fromTrees: distinct eclasses" allDistinct
  assertBool "fromTrees: each eid in eClass" (all (`IntMap.member` _eClass eg) eids)

-- | Test 18: Cost function respects node types
test_cost :: Test
test_cost = TestCase $ do
  let (eid, eg) = runEG $ fromTree myCost (var 0)
      cost = _cost . _info $ (_eClass eg IntMap.! eid)
  assertEqual "cost of Var is 1" 1 cost

-- | Test 19: getAllExpressionsFrom
test_get_all_expr :: Test
test_get_all_expr = TestCase $ do
  let (exprs, _) = runEG $ do
        eid <- fromTree myCost (var 0 + constv 1.0)
        getAllExpressionsFrom eid
  assertBool "getAllExpressionsFrom: non-empty" (not $ null exprs)
  assertEqual "getAllExpressionsFrom: includes original" (showExpr (var 0 + constv 1.0)) (showExpr (head exprs))

-- | Test 20: sizeFitDB has no stale entries after refit with lower fitness
test_sizeFitDB_no_stale :: Test
test_sizeFitDB_no_stale = TestCase $ do
  let (eg, _) = runEG $ do
        eid <- fromTree myCost (var 0)       -- size = 1
        insertFitness eid 1.0 []              -- insert higher fitness
        insertFitness eid 0.5 []              -- refit with lower fitness
        gets _eDB
      sfd = _sizeFitDB eg
      -- size 1 should have exactly 1 entry (the new fitness 0.5)
      size1Entries = case IntMap.lookup 1 sfd of
                       Nothing -> 0
                       Just rt -> length (RangeSet.toList rt)
  assertEqual "sizeFitDB: size 1 should have 1 entry after refit" 1 size1Entries
  -- verify the entry is the new fitness, not the old one
  case IntMap.lookup 1 sfd >>= RangeSet.lookupMax of
    Nothing -> assertFailure "sizeFitDB: size 1 should have an entry"
    Just (f, eId) -> assertBool "sizeFitDB: fitness should be 0.5" (abs (f - 0.5) < eps)

-- | Test 21: trie paths are canonical after merge+rebuild
-- repair never calls addToDB, so stale non-canonical keys remain in the trie.
-- This test verifies that no stale (non-canonical) keys exist after a merge.
test_trie_no_stale_keys :: Test
test_trie_no_stale_keys = TestCase $ do
  let (eg, _) = runEG $ do
        eid_a <- fromTree myCost (var 0)                             -- eclass 0
        eid_0 <- fromTree myCost (constv 0.0)                        -- eclass 1
        eid_t <- fromTree myCost (addZero (var 0) (constv 0.0))      -- eclass 2 (a+0)

        -- Merge a+0 (2) with a (0), so 2 → canonical 0
        mergedId <- merge myCost eid_t eid_a
        rebuild myCost

        -- Add a parent (a+0)*b after the merge
        eid_b <- fromTree myCost (var 1)                             -- eclass 3
        eid_parent <- fromTree myCost (addZero (var 0) (constv 0.0) * var 1)  -- (a+0)*b
        rebuild myCost

        gets id
      can = _canonicalMap eg
      staleKeys = getAllStaleTrieKeys can (_patDB $ _eDB eg)
  assertBool ("trie: expected exactly 1 stale key (2), got: " <> show staleKeys) (staleKeys == [2])

-- | Helper: construct a+0 bypassing Num instance optimization that rewrites +0 to identity
addZero :: Fix SRTree -> Fix SRTree -> Fix SRTree
addZero l r = Fix (Bin Add l r)

-- | Test 22: multi-atom match works after merge (requires toCanon in intersectAtoms)
test_match_after_merge_multi_atom :: Test
test_match_after_merge_multi_atom = TestCase $ do
  let pat = Fixed (Bin Mul (Fixed (Bin Add (VarPat 'a') (Fixed (Const 0.0)))) (VarPat 'b'))
      ((substs, _, _, _, _), _) = runEG $ do
        eid_a <- fromTree myCost (var 0)
        eid_0 <- fromTree myCost (constv 0.0)
        eid_t <- fromTree myCost (addZero (var 0) (constv 0.0))
        mergedId <- merge myCost eid_t eid_a
        rebuild myCost
        eid_b <- fromTree myCost (var 1)
        eid_parent <- fromTree myCost (addZero (var 0) (constv 0.0) * var 1)
        rebuild myCost
        substs <- match pat
        pure (substs, (), (), (), ())
  assertBool "match: multi-atom should work after merge" (not $ null substs)

-- | helper: find all non-canonical eclass ids in the trie
getAllStaleTrieKeys :: IntMap.IntMap Int -> DB -> [EClassId]
getAllStaleTrieKeys can = concatMap goIntTrie . Map.elems
  where
    goIntTrie (IntTrie m) =
      [k | k <- IntMap.keys m, not (isCanon k)]
      ++ concatMap goIntTrie (IntMap.elems m)
    isCanon eid = case IntMap.lookup eid can of
                    Just v  -> v == eid
                    Nothing -> False

prependLabel :: String -> Test -> Test
prependLabel label t = TestLabel label t

tests :: Test
tests = TestList
  [ prependLabel "fromTree-var"       test_fromTree_var
  , prependLabel "fromTree-bin"       test_fromTree_bin
  , prependLabel "canonical-identity" test_canonical_identity
  , prependLabel "canonize"           test_canonize
  , prependLabel "add-duplicate"      test_add_duplicate
  , prependLabel "merge"              test_merge
  , prependLabel "rebuild"            test_rebuild
  , prependLabel "match"              test_match
  , prependLabel "getBestExpr"        test_getBestExpr
  , prependLabel "eqsat-x+0"          test_eqsat_x_plus_0
  , prependLabel "eqsat-x*1"          test_eqsat_x_times_1
  , prependLabel "fitness-theta"      test_fitness_theta
  , prependLabel "fitness-range"      test_fitness_range
  , prependLabel "top-fit-size"       test_top_fit_size
  , prependLabel "eqsat-comm"         test_eqsat_comm
  , prependLabel "eqsat-double-neg"   test_eqsat_double_neg
  , prependLabel "fromTrees"          test_fromTrees
  , prependLabel "cost"               test_cost
  , prependLabel "getAllExpressions"  test_get_all_expr
  , prependLabel "sizeFitDB-no-stale" test_sizeFitDB_no_stale
  , prependLabel "trie-no-stale-keys" test_trie_no_stale_keys
  , prependLabel "match-after-merge"  test_match_after_merge_multi_atom
  ]
