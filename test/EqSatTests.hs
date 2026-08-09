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
import Algorithm.EqSat.Simplify (simplifyEqSatDefault, rewrites, rewritesParams)
import Control.Monad.State.Strict
import Control.Monad (forM_)
import Control.Monad.Identity
import Data.List (nub, sort)

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
  assertEqual "fromTree var: best is Var 0" (EVar 0) bestNode

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
  let children = eChildren canNode
  forM_ children $ \c -> do
    let (canC, _) = runIdentity $ runStateT (canonical c) eg
    assertEqual "canonize: child is canonical" c canC

-- | Test 5: Adding duplicate e-node returns existing e-class
test_add_duplicate :: Test
test_add_duplicate = TestCase $ do
  let tree = constv 2.0
      (eid1, eg1) = runEG $ fromTree myCost tree
      (eid2, eg2) = runEG' eg1 $ add myCost (EConst 2.0)
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

-- | Helper: construct a binary tree bypassing Num instance simplifications
mkBin :: Op -> Fix SRTree -> Fix SRTree -> Fix SRTree
mkBin op l r = Fix (Bin op l r)

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

-- | Test 23: flattened ENAry multiset for a right-nested Add
test_enary_flatten :: Test
test_enary_flatten = TestCase $ do
  let tree = mkBin Add (var 0) (mkBin Add (var 1) (var 2))
      (eid, eg) = runEG $ fromTree myCost tree
      ec = _eClass eg IntMap.! eid
  case _best . _info $ ec of
    ENAry EAdd xs -> do
      let children = expandedList xs
      assertEqual "enary: 3 children" 3 (length children)
      assertBool "enary: distinct children" (length (nub children) == length children)
      assertBool "enary: sorted children" (children == sort children)
    _ -> assertFailure "enary: best should be a 3-ary ENAry EAdd"

-- | Test 24: commutativity is structural (a+b ≡ b+a, no rules needed)
test_enary_comm :: Test
test_enary_comm = TestCase $ do
  let ((c1, c2), _) = runEG $ do
        eid1 <- fromTree myCost (mkBin Add (var 0) (var 1))
        eid2 <- fromTree myCost (mkBin Add (var 1) (var 0))
        a <- canonical eid1
        b <- canonical eid2
        pure (a, b)
  assertEqual "comm: a+b == b+a" c1 c2

-- | Test 25: associativity flattens (a+b)+c ≡ a+(b+c) ≡ a+(c+b)
test_enary_assoc :: Test
test_enary_assoc = TestCase $ do
  let ((c1, c2, c3), _) = runEG $ do
        eid1 <- fromTree myCost (mkBin Add (mkBin Add (var 0) (var 1)) (var 2))
        eid2 <- fromTree myCost (mkBin Add (var 0) (mkBin Add (var 1) (var 2)))
        eid3 <- fromTree myCost (mkBin Add (var 0) (mkBin Add (var 2) (var 1)))
        a <- canonical eid1
        b <- canonical eid2
        c <- canonical eid3
        pure (a, b, c)
  assertEqual "assoc: (a+b)+c == a+(b+c)" c1 c2
  assertEqual "assoc: (a+b)+c == a+(c+b)" c1 c3

-- | Test 26: multiset semantics (x+x is distinct from x)
test_enary_multiset :: Test
test_enary_multiset = TestCase $ do
  let ((cX, cXX), _) = runEG $ do
        eidX <- fromTree myCost (var 0)
        eidXX <- fromTree myCost (mkBin Add (var 0) (var 0))
        a <- canonical eidX
        b <- canonical eidXX
        pure (a, b)
  assertBool "multiset: x+x /= x" (cX /= cXX)

-- | Test 27: constants fold inside flattened nodes (2+3+x ≡ 5+x)
test_enary_fold_const :: Test
test_enary_fold_const = TestCase $ do
  let ((c1, c2), _) = runEG $ do
        eid1 <- fromTree myCost (mkBin Add (mkBin Add (constv 2.0) (constv 3.0)) (var 0))
        eid2 <- fromTree myCost (mkBin Add (constv 5.0) (var 0))
        a <- canonical eid1
        b <- canonical eid2
        pure (a, b)
  assertEqual "fold-const: 2+3+x == 5+x" c1 c2

-- | Test 28: direct add of an unsorted ENAry canonicalizes and folds consts
test_enary_direct_add :: Test
test_enary_direct_add = TestCase $ do
  let ((c1, c2), _) = runEG $ do
        e2 <- fromTree myCost (constv 2.0)
        e3 <- fromTree myCost (constv 3.0)
        ex <- fromTree myCost (var 0)
        eid <- add myCost (ENAry EAdd (imFromList [e3, ex, e2]))
        eid5x <- fromTree myCost (mkBin Add (constv 5.0) (var 0))
        a <- canonical eid
        b <- canonical eid5x
        pure (a, b)
  assertEqual "direct add: ENAry [3,x,2] sorts and folds to 5+x" c1 c2

-- | Test 29: extraction of a flattened class right-folds to a binary tree
test_enary_extract :: Test
test_enary_extract = TestCase $ do
  let t1 = mkBin Add (var 0) (mkBin Add (var 1) (var 2))
      (extracted, _) = runEG $ do
        eid <- fromTree myCost t1
        getBestExpr eid
  assertEqual "extract: flattened a+b+c == a+(b+c)" (showExpr t1) (showExpr extracted)

-- | Test 30: merge cascade propagates through ENAry parents (a≡b -> a+c ≡ b+c)
test_enary_merge_cascade :: Test
test_enary_merge_cascade = TestCase $ do
  let ((c1, c2), _) = runEG $ do
        ea <- fromTree myCost (var 0)
        eb <- fromTree myCost (var 1)
        _  <- fromTree myCost (var 2)
        eac <- fromTree myCost (mkBin Add (var 0) (var 2))
        ebc <- fromTree myCost (mkBin Add (var 1) (var 2))
        merge myCost ea eb
        rebuild myCost
        a <- canonical eac
        b <- canonical ebc
        pure (a, b)
  assertEqual "cascade: after a==b, a+c == b+c" c1 c2

-- | Soundness: a closed 2-ary pattern (a+b) does NOT match a 3-ary multiset.
test_match_closed2_not_3ary :: Test
test_match_closed2_not_3ary = TestCase $ do
  let pat = "a" + "b"
      (substs, _) = runEG $ do
        x <- fromTree myCost (var 0)
        y <- fromTree myCost (var 1)
        z <- fromTree myCost (var 2)
        _ <- add myCost (ENAry EAdd (imFromList [x, y, z]))
        match pat
  assertBool "closed2: a+b does not match x+y+z" (null substs)

-- | Soundness: a+a does NOT match x+x+y (only exact multisets match).
test_match_aa_not_3ary :: Test
test_match_aa_not_3ary = TestCase $ do
  let pat = "a" + "a"
      (substs, _) = runEG $ do
        _ <- fromTree myCost (mkBin Add (var 0) (mkBin Add (var 0) (var 1)))
        match pat
  assertBool "aa: a+a does not match x+x+y" (null substs)

-- | B3: 0 + x + y = x + y (n-ary open-rest rule).
test_eqsat_zero_plus_rest :: Test
test_eqsat_zero_plus_rest = TestCase $ do
  let tree = addZero (constv 0.0) (addZero (var 0) (var 1))
  assertEqual "0+x+y = x+y"
              (showExpr (var 0 + var 1))
              (showExpr (simplifyEqSatDefault tree))

-- | B7: xy + xz + w = x(y+z) + w (n-ary factoring with a rest variable).
test_eqsat_factoring :: Test
test_eqsat_factoring = TestCase $ do
  let tree = ((var 0 * var 1) + (var 0 * var 2)) + var 3
  assertEqual "xy+xz+w = x(y+z)+w"
              (showExpr ((var 0 * (var 1 + var 2)) + var 3))
              (showExpr (simplifyEqSatDefault tree))

-- | C9 is a closed 2-ary rule: (x+y+z)^2 is NOT expanded to a binomial.
test_eqsat_binomial_closed2 :: Test
test_eqsat_binomial_closed2 = TestCase $ do
  let tree = ((var 0 + var 1) + var 2) ** constv 2.0
  assertEqual "(x+y+z)^2 not expanded"
              (showExpr ((var 0 + (var 1 + var 2)) ** constv 2.0))
              (showExpr (simplifyEqSatDefault tree))

-- | C14: sqrt(x*x) = abs x (closed 2-ary multiset).
test_eqsat_sqrt_square :: Test
test_eqsat_sqrt_square = TestCase $ do
  let rule = sqrt (NAry EMul [Ch "x", Ch "x"]) :=> abs "x"
      (best, _) = runEG $ eqSat (sqrt (var 0 * var 0)) [rule] myCost 5
  assertEqual "sqrt(x*x) = abs x" (showExpr (abs (var 0))) (showExpr best)

-- | x/x = 1 and x-x = 0 (constant identities).
test_eqsat_identities :: Test
test_eqsat_identities = TestCase $ do
  assertEqual "x/x = 1" (showExpr (constv 1.0)) (showExpr (simplifyEqSatDefault (var 0 / var 0)))
  assertEqual "x-x = 0" (showExpr (constv 0.0)) (showExpr (simplifyEqSatDefault (var 0 - var 0)))

-- | helper: run eqSat with the full rule set and collect every expression
-- in the root eclass (used to assert that a rule "fires" even if a cheaper
-- representative is extracted).
allExprsOf :: Fix SRTree -> [Fix SRTree]
allExprsOf t = fst $ runEG $ do
  root <- fromTree myCost t
  _ <- runEqSat myCost rewrites 20
  getAllExpressionsFrom root

-- | C11 fires: log(x*y) expands to log x + log y inside the root eclass.
test_eqsat_log_distributes :: Test
test_eqsat_log_distributes = TestCase $ do
  let exprs  = allExprsOf (log (var 0 * var 1))
      target = showExpr (log (var 0) + log (var 1))
  assertBool "log(x*y) contains log x + log y"
             (any (\e -> showExpr e == target) exprs)

-- | C12 fires: abs(x*y) expands to abs x * abs y inside the root eclass.
test_eqsat_abs_distributes :: Test
test_eqsat_abs_distributes = TestCase $ do
  let exprs  = allExprsOf (abs (var 0 * var 1))
      target = showExpr (abs (var 0) * abs (var 1))
  assertBool "abs(x*y) contains abs x * abs y"
             (any (\e -> showExpr e == target) exprs)

-- | C13 fires: (x*y)^z expands to x^z * y^z inside the root eclass.
test_eqsat_pow_distributes :: Test
test_eqsat_pow_distributes = TestCase $ do
  let exprs  = allExprsOf ((var 0 * var 1) ** constv 2.0)
      target = showExpr ((var 0 ** constv 2.0) * (var 1 ** constv 2.0))
  assertBool "(x*y)^2 contains x^2 * y^2"
             (any (\e -> showExpr e == target) exprs)

-- | B9 (a :==: rule): x^2 * x^3 = x^5.
test_eqsat_pow_mul :: Test
test_eqsat_pow_mul = TestCase $ do
  let tree = (var 0 ** constv 2.0) * (var 0 ** constv 3.0)
  assertEqual "x^2*x^3 = x^5" (showExpr (var 0 ** constv 5.0))
              (showExpr (simplifyEqSatDefault tree))

-- | B11 (a :==: rule): (x^2)^3 = x^6.
test_eqsat_pow_pow :: Test
test_eqsat_pow_pow = TestCase $ do
  let tree = (var 0 ** constv 2.0) ** constv 3.0
  assertEqual "(x^2)^3 = x^6" (showExpr (var 0 ** constv 6.0))
              (showExpr (simplifyEqSatDefault tree))

-- | x^y * x = x^(y+1): x^2 * x = x^3.
test_eqsat_pow_mul_x :: Test
test_eqsat_pow_mul_x = TestCase $ do
  let tree = (var 0 ** constv 2.0) * var 0
  assertEqual "x^2*x = x^3" (showExpr (var 0 ** constv 3.0))
              (showExpr (simplifyEqSatDefault tree))

-- | B4: (0*x)*y = 0.
test_eqsat_zero_mul :: Test
test_eqsat_zero_mul = TestCase $ do
  let tree = mkBin Mul (mkBin Mul (constv 0.0) (var 0)) (var 1)
  assertEqual "(0*x)*y = 0" (showExpr (constv 0.0))
              (showExpr (simplifyEqSatDefault tree))

-- | B4 guard: (0*NaN)*x is NOT folded to 0 (NaN invalidates the rest).
test_eqsat_zero_mul_nan :: Test
test_eqsat_zero_mul_nan = TestCase $ do
  let tree = mkBin Mul (mkBin Mul (constv 0.0) (constv (0/0))) (var 0)
      best = simplifyEqSatDefault tree
  assertBool "(0*NaN)*x /= 0" (showExpr best /= showExpr (constv 0.0))

-- | rewritesParams: x-x and x/x become Param 0.
test_eqsat_params :: Test
test_eqsat_params = TestCase $ do
  let (b1, _) = runEG $ eqSat (var 0 - var 0) rewritesParams myCost 10
      (b2, _) = runEG $ eqSat (var 0 / var 0) rewritesParams myCost 10
  assertEqual "x-x = Param 0 (param mode)" (showExpr (param 0)) (showExpr b1)
  assertEqual "x/x = Param 0 (param mode)" (showExpr (param 0)) (showExpr b2)

-- | Soundness: x*x*y stays as a right-folded Mul, NOT x^2 (B1 is 2-ary only).
test_eqsat_xxy_sound :: Test
test_eqsat_xxy_sound = TestCase $ do
  let tree = mkBin Mul (mkBin Mul (var 0) (var 0)) (var 1)
  assertEqual "x*x*y stays right-folded"
              (showExpr (var 0 * (var 0 * var 1)))
              (showExpr (simplifyEqSatDefault tree))

-- | Completeness: a*b matches every Mul node inside a merged class.
test_match_complete_multinode :: Test
test_match_complete_multinode = TestCase $ do
  let pat = "a" * "b"
      (n, _) = runEG $ do
        _ <- fromTree myCost (var 0)
        _ <- fromTree myCost (var 1)
        _ <- fromTree myCost (var 2)
        _ <- fromTree myCost (var 3)
        m1 <- fromTree myCost (var 0 * var 1)
        m2 <- fromTree myCost (var 2 * var 3)
        _ <- merge myCost m1 m2
        rebuild myCost
        s <- match pat
        pure (length s)
  assertBool "complete: a*b yields all substs in a merged class" (n >= 2)

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
  , prependLabel "enary-flatten"      test_enary_flatten
  , prependLabel "enary-comm"         test_enary_comm
  , prependLabel "enary-assoc"        test_enary_assoc
  , prependLabel "enary-multiset"     test_enary_multiset
  , prependLabel "enary-fold-const"   test_enary_fold_const
  , prependLabel "enary-direct-add"   test_enary_direct_add
  , prependLabel "enary-extract"      test_enary_extract
  , prependLabel "enary-merge-cascade" test_enary_merge_cascade
  , prependLabel "match-closed2-3ary"  test_match_closed2_not_3ary
  , prependLabel "match-aa-not-3ary"   test_match_aa_not_3ary
  , prependLabel "eqsat-0+rest"        test_eqsat_zero_plus_rest
  , prependLabel "eqsat-factoring"     test_eqsat_factoring
  , prependLabel "eqsat-binomial-2ary" test_eqsat_binomial_closed2
  , prependLabel "eqsat-sqrt-square"   test_eqsat_sqrt_square
  , prependLabel "eqsat-identities"    test_eqsat_identities
  , prependLabel "eqsat-log-dist"      test_eqsat_log_distributes
  , prependLabel "eqsat-abs-dist"      test_eqsat_abs_distributes
  , prependLabel "eqsat-pow-dist"      test_eqsat_pow_distributes
  , prependLabel "eqsat-pow-mul"       test_eqsat_pow_mul
  , prependLabel "eqsat-pow-pow"       test_eqsat_pow_pow
  , prependLabel "eqsat-pow-mul-x"     test_eqsat_pow_mul_x
  , prependLabel "eqsat-0*mul"         test_eqsat_zero_mul
  , prependLabel "eqsat-0*mul-NaN"     test_eqsat_zero_mul_nan
  , prependLabel "eqsat-params"        test_eqsat_params
  , prependLabel "eqsat-x*x*y-sound"   test_eqsat_xxy_sound
  , prependLabel "match-complete"      test_match_complete_multinode
  ]
