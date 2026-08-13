{-# LANGUAGE TupleSections #-}

module StoreTests where

import Test.HUnit
import Data.SRTree
import qualified Data.IntMap as IntMap
import qualified Data.HashMap.Strict as HashMap
import Algorithm.EqSat
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Build
import Algorithm.EqSat.DB
import Algorithm.EqSat.Info
import Algorithm.EqSat.Queries
import Algorithm.EqSat.Store
import Control.Monad.State.Strict
import Control.Monad.Identity

myCost :: SRTree Int -> Int
myCost (Var _)     = 1
myCost (Const _)   = 1
myCost (Param _)   = 1
myCost (Bin _ l r) = 2 + l + r
myCost (Uni _ t)   = 3 + t

-- | run a stateful computation on a specific graph
runIn :: EGraph -> EGraphST Identity a -> (a, EGraph)
runIn g m = runIdentity $ runStateT m g

evalIn :: EGraph -> EGraphST Identity a -> a
evalIn g m = runIdentity $ evalStateT m g

-- | graph A: x0, x1, x0+x1 (with fitness on the sum)
buildA :: (EClassId, EGraph)
buildA = runIn emptyGraph $ do
  _      <- fromTree myCost (var 0)
  _      <- fromTree myCost (var 1)
  eidSum <- fromTree myCost (var 0 + var 1)
  insertFitness eidSum 0.5 []
  pure eidSum

-- | graph B: x1, x0+x1, (x0+x1)*x2  (shares x1 and x0+x1 with A)
buildB :: EGraph
buildB = snd $ runIn emptyGraph $ do
  _ <- fromTree myCost (var 1)
  _ <- fromTree myCost (var 0 + var 1)
  _ <- fromTree myCost ((var 0 + var 1) * var 2)
  pure ()

-- | pattern (x0+x1)*x2 = (A + B) * C
prodPattern :: Pattern
prodPattern = Fixed (Bin Mul (Fixed (Bin Add (VarPat 'A') (VarPat 'B'))) (VarPat 'C'))

-- | Test 1: export/import round-trip preserves the rows exactly
test_roundtrip :: Test
test_roundtrip = TestCase $ do
  let (_, g) = runIn emptyGraph $ do
        _ <- fromTree myCost (var 0)
        _ <- fromTree myCost (var 1)
        _ <- fromTree myCost (var 0 + var 1)
        _ <- fromTree myCost ((var 0 + var 1) * var 2)
        pure ()
      rows = exportEGraph g
  case importEGraph rows of
    Left err -> assertFailure ("import failed: " ++ err)
    Right g' -> do
      let rows' = exportEGraph g'
      assertBool "round-trip: rows differ" (rows == rows')
      assertBool "round-trip: class count" (IntMap.size (_grEClasses rows) == IntMap.size (_grEClasses rows'))
      assertBool "round-trip: node count" (HashMap.size (_grENodeToEClass rows) == HashMap.size (_grENodeToEClass rows'))

-- | Test 2: round-trip preserves fitness and rebuilds the range DB
test_roundtrip_fitness :: Test
test_roundtrip_fitness = TestCase $ do
  let (sumEid, g) = runIn emptyGraph $ do
        eidSum <- fromTree myCost (var 0 + var 1)
        insertFitness eidSum 0.42 []
        pure eidSum
      rows = exportEGraph g
  case importEGraph rows of
    Left err -> assertFailure ("import failed: " ++ err)
    Right g' -> do
      let fit = evalIn g' (getFitness sumEid)
      assertEqual "round-trip: fitness" (Just 0.42) fit
      let mx = getGreatest (_fitRangeDB (_eDB g'))
      assertEqual "round-trip: fitRangeDB max" (Just (0.42, sumEid)) mx
      -- a node added *after* import dedups against the loaded graph (no dup class)
      let (eidNew, g'') = runIn g' $ fromTree myCost (var 0 + var 1)
          nClasses = IntMap.size (_eClass g'')
      assertBool "post-import dedup adds no class" (eidNew == sumEid && nClasses == IntMap.size (_eClass g'))

-- | Test 3: import rejects inconsistent rows
test_import_invalid :: Test
test_import_invalid = TestCase $ do
  let (_, g) = runIn emptyGraph $ do
        _ <- fromTree myCost (var 0)
        pure ()
      rows = exportEGraph g
      bad  = rows { _grENodeToEClass = HashMap.insert (EVar 0) 999 (_grENodeToEClass rows) } -- 999 not in canonical map
  case importEGraph bad of
    Left _  -> pure ()
    Right _ -> assertFailure "invalid rows should have been rejected"

-- | Test 4: merge dedups shared structure and adds only new classes
test_merge :: Test
test_merge = TestCase $ do
  let (sumEidA, gA) = buildA
      gM = case mergeEGraph myCost gA buildB of
             Left err  -> error ("merge failed: " ++ err)
             Right g   -> g
      nA = IntMap.size (_eClass gA)
      nM = IntMap.size (_eClass gM)
  assertEqual "merge: adds only classes absent from A (x2, product)" (nA + 2) nM
  -- B's unique expression (x0+x1)*x2 is present and matchable
  let nMatch = length $ evalIn gM (match prodPattern)
  assertBool "merge: B's unique expression present" (nMatch > 0)
  -- A's fitness on the shared sum class is preserved (same canonical id)
  assertEqual "merge: A fitness preserved" (Just 0.5) (evalIn gM (getFitness sumEidA))

-- | Test 5: merge preserves round-trip
test_merge_roundtrip :: Test
test_merge_roundtrip = TestCase $ do
  let (_, gA) = buildA
      gM = case mergeEGraph myCost gA buildB of
             Left err  -> error ("merge failed: " ++ err)
             Right g   -> g
      rows = exportEGraph gM
  case importEGraph rows of
    Left err -> assertFailure ("import failed: " ++ err)
    Right gM' -> assertBool "merge round-trip: rows differ" (exportEGraph gM' == rows)

prependLabel :: String -> Test -> Test
prependLabel label t = TestLabel label t

tests :: Test
tests = TestList
  [ prependLabel "store-roundtrip"       test_roundtrip
  , prependLabel "store-roundtrip-fit"   test_roundtrip_fitness
  , prependLabel "store-import-invalid"  test_import_invalid
  , prependLabel "store-merge"           test_merge
  , prependLabel "store-merge-roundtrip" test_merge_roundtrip
  ]