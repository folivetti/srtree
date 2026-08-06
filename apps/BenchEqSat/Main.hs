{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

import Criterion.Main
import qualified Data.Vector.Unboxed as VU
import qualified Data.IntMap as IntMap
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as Set

import Data.SRTree
import Algorithm.EqSat
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Build
import Algorithm.EqSat.DB
import Algorithm.EqSat.Info
import Algorithm.EqSat.Queries
import Control.Monad.State.Strict
import Control.Monad (replicateM, zipWithM_)
import Control.Monad.Identity

myCost :: SRTree Int -> Int
myCost (Var _)     = 1
myCost (Const _)   = 1
myCost (Param _)   = 1
myCost (Bin _ l r) = 2 + l + r
myCost (Uni _ t)   = 3 + t

evalEG :: EGraphST Identity a -> (a, EGraph)
evalEG m = runIdentity $ runStateT m emptyGraph

runInEG :: EGraph -> EGraphST Identity a -> (a, EGraph)
runInEG eg m = runIdentity $ runStateT m eg

-- Expression generators for benchmarking
chainAdd :: Int -> Fix SRTree
chainAdd 0 = var 0
chainAdd n = chainAdd (n-1) + var n

deepBinTree :: Int -> Fix SRTree
deepBinTree 0 = var 0
deepBinTree n = deepBinTree (n-1) + constv (fromIntegral n)

complexTree :: Int -> Fix SRTree
complexTree n = go n
  where
    go 0 = var 0
    go i = (var i + constv (fromIntegral i)) * (go (i-1) + constv (fromIntegral i))

simplifyRules :: [Rule]
simplifyRules =
  [ "a" + 0 :=> "a"
  , "a" * 1 :=> "a"
  , "a" + "a" :=> 2 * "a"
  , "a" * 0 :=> 0
  , 0 + "a" :=> "a"
  , 1 * "a" :=> "a"
  ]

-- More rules including commutativity (triggers more merges)
moreRules :: [Rule]
moreRules =
  [ "a" + 0 :=> "a"
  , "a" * 1 :=> "a"
  , "a" + "a" :=> 2 * "a"
  , "a" * 0 :=> 0
  , 0 + "a" :=> "a"
  , 1 * "a" :=> "a"
  , "a" + "b" :=> "b" + "a"
  , "a" * "b" :=> "b" * "a"
  ]

addZero :: Fix SRTree -> Fix SRTree -> Fix SRTree
addZero l r = Fix (Bin Add l r)

main :: IO ()
main = do
  putStrLn "Generating benchmark expressions..."
  let smallExpr  = chainAdd 5
      mediumExpr = chainAdd 20
      largeExpr  = chainAdd 100
      complex    = complexTree 8

  putStrLn "Running benchmarks..."
  defaultMain [
    bgroup "E-graph Construction" [
      bench "fromTree (5-leaf chain)" $
        whnf (\e -> evalEG $ fromTree myCost e) smallExpr,
      bench "fromTree (20-leaf chain)" $
        whnf (\e -> evalEG $ fromTree myCost e) mediumExpr,
      bench "fromTree (100-leaf chain)" $
        whnf (\e -> evalEG $ fromTree myCost e) largeExpr,
      bench "fromTree (complex-ternary tree)" $
        whnf (\e -> evalEG $ fromTree myCost e) complex
    ],

    bgroup "E-graph Add" [
      bench "add single e-node (Var)" $
        whnf (\eg -> runInEG eg $ add myCost (EVar 999)) (snd $ evalEG $ fromTree myCost smallExpr),
      bench "add single e-node (Const)" $
        whnf (\eg -> runInEG eg $ add myCost (EConst 42.0)) (snd $ evalEG $ fromTree myCost smallExpr),
      bench "add single e-node (Bin Add)" $
        whnf (\eg -> runInEG eg $ add myCost (ENAry EAdd [0, 1])) (snd $ evalEG $ fromTree myCost mediumExpr)
    ],

    bgroup "Merge" [
      bench "merge two distinct eclasses (size 1)" $
        whnf (\(e1,e2,eg) -> runInEG eg $ merge myCost e1 e2) (makeMergePair 1),
      bench "merge two distinct eclasses (size 3)" $
        whnf (\(e1,e2,eg) -> runInEG eg $ merge myCost e1 e2) (makeMergePair 3)
    ],

    bgroup "Pattern Matching" [
      bench "match simple pattern (a+0)" $
        whnf (\(eg,_) -> runInEG eg $ match ("a" + 0 :: Pattern)) (makeMatchableEG),
      bench "match commutative pattern (a+b)" $
        whnf (\(eg,_) -> runInEG eg $ match ("a" + "b" :: Pattern)) (makeMatchableEG),
      bench "match triple pattern (a+b+c)" $
        whnf (\(eg,_) -> runInEG eg $ match ("a" + "b" + "c" :: Pattern)) (makeMatchableEG)
    ],

    bgroup "Match After Merge" [
      bench "match (a+0) after merge (stale trie keys)" $
        whnf (\(eg,_) -> runInEG eg $ match ("a" + 0 :: Pattern)) (makeMergedEG),
      bench "match (a+b) after merge (stale trie keys)" $
        whnf (\(eg,_) -> runInEG eg $ match ("a" + "b" :: Pattern)) (makeMergedEG)
    ],

    bgroup "Rebuild" [
      bench "rebuild after 5 adds" $
        whnf (\(eg,_) -> runInEG eg $ rebuild myCost) (makeDirtyEG 5),
      bench "rebuild after 20 adds" $
        whnf (\(eg,_) -> runInEG eg $ rebuild myCost) (makeDirtyEG 20),
      bench "rebuild after 100 adds" $
        whnf (\(eg,_) -> runInEG eg $ rebuild myCost) (makeDirtyEG 100)
    ],

    bgroup "Cost Propagation" [
      bench "recalculateBest (10 eclasses)" $
        whnf (\(eids,eg) -> runInEG eg $ mapM_ (recalculateBest myCost) eids) (makeNEclasses 10),
      bench "recalculateBest (100 eclasses)" $
        whnf (\(eids,eg) -> runInEG eg $ mapM_ (recalculateBest myCost) eids) (makeNEclasses 100)
    ],

    bgroup "DB Operations" [
      bench "addToDB single enode" $
        whnf (\(en,eid,eg) -> runInEG eg $ addToDB en eid) (makeDBEntry),
      bench "addToDB 10 enodes" $
        whnf (\(ens,eg) -> runInEG eg $ mapM_ (uncurry addToDB) ens) (makeDBEntries 10)
    ],

    bgroup "Equality Saturation" [
      bench "eqSat small expr (5 rules)" $
        whnf (\(e,r) -> evalEG $ eqSat e r myCost 10) (smallExpr, simplifyRules),
      bench "eqSat medium expr (5 rules)" $
        whnf (\(e,r) -> evalEG $ eqSat e r myCost 10) (mediumExpr, simplifyRules),
      bench "eqSat small expr (8 rules, commutative)" $
        whnf (\(e,r) -> evalEG $ eqSat e r myCost 10) (smallExpr, moreRules),
      bench "eqSat large expr (5 rules)" $
        whnf (\(e,r) -> evalEG $ eqSat e r myCost 10) (largeExpr, simplifyRules)
    ],

    bgroup "Extraction" [
      bench "getBestExpr (5-leaf)" $
        whnf (\(eid,eg) -> runInEG eg $ getBestExpr eid) (makeExtractable 5),
      bench "getBestExpr (20-leaf)" $
        whnf (\(eid,eg) -> runInEG eg $ getBestExpr eid) (makeExtractable 20),
      bench "getBestExpr (100-leaf)" $
        whnf (\(eid,eg) -> runInEG eg $ getBestExpr eid) (makeExtractable 100)
    ],

    bgroup "Fitness Operations" [
      bench "insertFitness single" $
        whnf (\(eid,eg) -> runInEG eg $ insertFitness eid 0.5 []) (makeExtractable 1),
      bench "insertFitness 10 eclasses" $
        whnf (\(eids,eg) -> runInEG eg $ mapM_ (\eid -> insertFitness eid 0.5 []) eids) (makeNEclasses 10),
      bench "getTopFitEClassWithSize" $
        whnf (\(eids,eg) -> runInEG eg $ getTopFitEClassWithSize 1 3) (makeFitnessEG)
    ]
    ]
  where
    addZeroTree = addZero (var 0) (constv 0.0)

    makeMergePair :: Int -> (EClassId, EClassId, EGraph)
    makeMergePair n =
      let tree = deepBinTree n
          (eid1, eg1) = evalEG $ fromTree myCost tree
          (eid2, eg2) = runInEG eg1 $ fromTree myCost tree
      in (eid1, eid2, eg2)

    makeMatchableEG :: (EGraph, EClassId)
    makeMatchableEG =
      let tree = complexTree 4
          (eid, eg) = evalEG $ do
            eid' <- fromTree myCost tree
            _ <- fromTree myCost (var 0 + constv 1.0)
            _ <- fromTree myCost (var 1 * constv 2.0)
            _ <- fromTree myCost (var 0 + constv 0.0)
            _ <- fromTree myCost (var 1 * constv 1.0)
            rebuild myCost
            pure eid'
      in (eg, eid)

    -- E-graph with merges applied, creating stale trie keys
    makeMergedEG :: (EGraph, EClassId)
    makeMergedEG =
      let (_, eg) = evalEG $ do
            eid1 <- fromTree myCost (var 0)
            eid2 <- fromTree myCost (constv 0.0)
            eid3 <- fromTree myCost (var 0 + constv 1.0)
            _ <- fromTree myCost (var 1)
            rebuild myCost
            -- merge to create stale trie entries
            merge myCost eid1 eid2
            merge myCost eid2 eid3
            rebuild myCost
            pure eid1
      in (eg, 0)

    makeDirtyEG :: Int -> (EGraph, EClassId)
    makeDirtyEG n =
      let tree = deepBinTree n
          (eid, eg) = evalEG $ do
            eid' <- fromTree myCost tree
            _ <- fromTree myCost (tree + var 999)
            rebuild myCost
            _ <- fromTree myCost (tree * var 998)
            pure eid'
      in (eg, eid)

    makeExtractable :: Int -> (EClassId, EGraph)
    makeExtractable n =
      let tree = deepBinTree n
      in evalEG $ fromTree myCost tree

    makeNEclasses :: Int -> ([EClassId], EGraph)
    makeNEclasses n =
      evalEG $ replicateM n (fromTree myCost (constv (fromIntegral n)))

    makeFitnessEG :: ([EClassId], EGraph)
    makeFitnessEG = evalEG $ do
      eids <- mapM (fromTree myCost . constv . fromIntegral) [1..10]
      zipWithM_ (\eid i -> insertFitness eid (fromIntegral i) []) eids [1..]
      pure eids

    makeDBEntry :: (ENode, EClassId, EGraph)
    makeDBEntry =
      let (eid, eg) = evalEG $ do
            eid <- fromTree myCost (var 999)
            rebuild myCost
            pure eid
      in (EVar 777, eid, eg)

    makeDBEntries :: Int -> ([(ENode, EClassId)], EGraph)
    makeDBEntries n =
      let (eids, eg) = evalEG $ do
            eids <- mapM (fromTree myCost . var) [999..(999 + n - 1)]
            rebuild myCost
            pure eids
      in (zip (map EVar [1000..]) eids, eg)
