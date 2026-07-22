{-# LANGUAGE BangPatterns #-}

module Main where

import Data.List (foldl', sort)
import Data.Sequence (Seq(..), (><))
import qualified Data.Sequence as FingerTree
import qualified Data.Set as OrdSet
import Data.Foldable (toList)
import System.Random (mkStdGen, randoms, randomR)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)
import Control.DeepSeq (force, NFData)
import Control.Exception (evaluate)

type EClassId = Int

-- | Old Seq-based RangeTree
type RangeTreeOld a = Seq (a, EClassId)

insertRangeOld :: (Ord a, Show a) => EClassId -> a -> RangeTreeOld a -> RangeTreeOld a
insertRangeOld eid x Empty                      = FingerTree.singleton (x, eid)
insertRangeOld eid x (y :<| _xs) | (x, eid) < y = (x, eid) :<| y :<| _xs
insertRangeOld eid x (_xs :|> y) | (x, eid) > y = _xs :|> y :|> (x, eid)
insertRangeOld eid x rt = go rt
  where
    entry   = (x, eid)
    go root = case FingerTree.splitAt (n `div` 2) root of
                (Empty, Empty)    -> FingerTree.singleton entry
                (Empty, z :<| zs) | entry < z -> entry :<| z :<| zs
                                  | otherwise -> z :<| (go zs)
                (ys :|> y, Empty) | entry > y -> ys :|> y :|> entry
                                  | otherwise -> (go ys) :|> y
                (ys :|> y, z :<| zs)
                     | entry > y && entry < z -> (ys :|> y :|> entry) >< (z :<| zs)
                     | entry > z              -> (ys :|> y) >< go (z :<| zs)
                     | entry < y              -> go (ys :|> y) >< (z :<| zs)
                     | otherwise              -> root
      where
        n = FingerTree.length root

removeRangeOld :: (Ord a, Show a) => EClassId -> a -> RangeTreeOld a -> RangeTreeOld a
removeRangeOld eid x Empty                  = Empty
removeRangeOld eid x (y :<| _xs) | (x, eid) < y = (y :<| _xs)
removeRangeOld eid x (_xs :|> y) | (x, eid) > y = (_xs :|> y)
removeRangeOld eid x rt = go rt
  where
    entry   = (x, eid)
    go root = case FingerTree.splitAt (n `div` 2) root of
                (Empty, Empty)    -> root
                (Empty, z :<| zs)
                            | entry < z  -> z :<| zs
                            | entry == z -> zs
                            | otherwise  -> z :<| (go zs)
                (ys :|> y, Empty)
                            | entry > y  -> ys :|> y
                            | entry == y -> ys
                            | otherwise  -> (go ys) :|> y
                (ys :|> y, z :<| zs)
                     | entry > y && entry < z -> root
                     | entry > z              -> (ys :|> y) >< go (z :<| zs)
                     | entry < y              -> go (ys :|> y) >< (z :<| zs)
                     | otherwise              -> root
      where
        n = FingerTree.length root

getWithinRangeOld :: Ord a => a -> a -> RangeTreeOld a -> [EClassId]
getWithinRangeOld lb ub rt = map snd . toList $ go rt
  where
    go Empty = Empty
    go root = case FingerTree.splitAt (n `div` 2) root of
                (Empty, Empty)    -> Empty
                (ys :|> y, Empty)
                     | fst y < lb    -> Empty
                     | otherwise -> go (ys :|> y)
                (Empty, z :<| zs)
                            | fst z > ub    -> Empty
                            | otherwise -> go (z :<| zs)
                (ys :|> y, z :<| zs)
                     | fst y < lb -> go (z :<| zs)
                     | fst z > ub -> go (ys :|> y)
                     | otherwise -> go (ys :|> y) >< go (z :<| zs)
      where
        n = FingerTree.length root

getSmallestOld :: Ord a => RangeTreeOld a -> (a, EClassId)
getSmallestOld rt = case rt of
                     Empty -> error "empty finger"
                     x :<| t -> x

getGreatestOld :: Ord a => RangeTreeOld a -> (a, EClassId)
getGreatestOld rt = case rt of
                     Empty -> error "empty finger"
                     t :|> x -> x

-- | New Set-based RangeTree
type RangeTreeNew a = OrdSet.Set (a, EClassId)

insertRangeNew :: (Ord a, Show a) => EClassId -> a -> RangeTreeNew a -> RangeTreeNew a
insertRangeNew eid x = OrdSet.insert (x, eid)
{-# INLINE insertRangeNew #-}

removeRangeNew :: (Ord a, Show a) => EClassId -> a -> RangeTreeNew a -> RangeTreeNew a
removeRangeNew eid x = OrdSet.delete (x, eid)
{-# INLINE removeRangeNew #-}

getWithinRangeNew :: Ord a => a -> a -> RangeTreeNew a -> [EClassId]
getWithinRangeNew lb ub rt =
  let (_, ge)  = OrdSet.split (lb, minBound) rt
      (inR, _) = OrdSet.split (ub, maxBound) ge
  in map snd (OrdSet.toList inR)

getSmallestNew :: Ord a => RangeTreeNew a -> (a, EClassId)
getSmallestNew = maybe (error "empty finger") id . OrdSet.lookupMin
{-# INLINE getSmallestNew #-}

getGreatestNew :: Ord a => RangeTreeNew a -> (a, EClassId)
getGreatestNew = maybe (error "empty finger") id . OrdSet.lookupMax
{-# INLINE getGreatestNew #-}

------------------------------------------------------------------------------
-- Benchmark harness
------------------------------------------------------------------------------

timeIt :: String -> Int -> (a -> b) -> a -> IO ()
timeIt label n fn input = do
  -- warmup
  let !_ = fn input
  t0 <- getCPUTime
  let go 0 acc = pure acc
      go !i !acc = do
        let !res = fn input
        go (i - 1) (acc + res)
  result <- go n (0 :: Int)
  t1 <- getCPUTime
  let total  = fromIntegral (t1 - t0) / 1e9 :: Double
      perOp  = total / fromIntegral n
  printf "%-30s %6d iterations  %9.2f ms total  %9.3f us/op\n"
    label n total perOp
  -- prevent optimisation from discarding result
  evaluate (force result)
  pure ()

mkTimeIO :: String -> Int -> IO a -> IO ()
mkTimeIO label n action = do
  t0 <- getCPUTime
  let go 0 = pure ()
      go i = action >> go (i - 1)
  go n
  t1 <- getCPUTime
  let total  = fromIntegral (t1 - t0) / 1e9 :: Double
      perOp  = total / fromIntegral n
  printf "%-30s %6d iterations  %9.2f ms total  %9.3f us/op\n"
    label n total perOp

------------------------------------------------------------------------------
-- Generate test data
------------------------------------------------------------------------------

genData :: Int -> IO [(Double, Int)]
genData n = do
  let g = mkStdGen 42
      vals = take n (randoms g :: [Double])
      eids = take n (randoms g :: [Int])
  pure $ zip vals eids

------------------------------------------------------------------------------
-- Benchmark sequences
------------------------------------------------------------------------------

benchInsert :: Int -> IO ()
benchInsert n = do
  items <- genData n
  let itemsList = take n items
  printf "\n--- Insert (%d elements) ---\n" n
  -- Old
  do
    let go acc (v, eid) = insertRangeOld eid v acc
    timeIt ("old insert") 50 (\xs -> foldl' go Empty xs) itemsList
  -- New
  do
    let go acc (v, eid) = insertRangeNew eid v acc
    timeIt ("new insert") 50 (\xs -> foldl' go OrdSet.empty xs) itemsList

benchInsertThenRemove :: Int -> IO ()
benchInsertThenRemove n = do
  items <- genData n
  let itemsList = take n items
  printf "\n--- Insert then Remove (%d elements) ---\n" n
  let buildOld = foldl' (\acc (v, eid) -> insertRangeOld eid v acc) Empty itemsList
      buildNew = foldl' (\acc (v, eid) -> insertRangeNew eid v acc) OrdSet.empty itemsList
  -- Remove all
  do
    let go acc (v, eid) = removeRangeOld eid v acc
    timeIt ("old remove all") 50 (\xs -> foldl' go xs itemsList) buildOld
  do
    let go acc (v, eid) = removeRangeNew eid v acc
    timeIt ("new remove all") 50 (\xs -> foldl' go xs itemsList) buildNew

benchRangeQuery :: Int -> IO ()
benchRangeQuery n = do
  items <- genData n
  let itemsList = take n items
      buildOld = foldl' (\acc (v, eid) -> insertRangeOld eid v acc) Empty itemsList
      buildNew = foldl' (\acc (v, eid) -> insertRangeNew eid v acc) OrdSet.empty itemsList
  printf "\n--- Range Query (%d elements) ---\n" n
  let queries = [(0.25, 0.75), (0.0, 0.5), (0.5, 1.0)]
  forM_ queries $ \(lb, ub) -> do
    timeIt (printf "old range [%.2f,%.2f]" lb ub) 200
      (\rt -> length (getWithinRangeOld lb ub rt)) buildOld
    timeIt (printf "new range [%.2f,%.2f]" lb ub) 200
      (\rt -> length (getWithinRangeNew lb ub rt)) buildNew
  where
    forM_ = mapM_

benchMinMax :: Int -> IO ()
benchMinMax n = do
  items <- genData n
  let itemsList = take n items
      buildOld = foldl' (\acc (v, eid) -> insertRangeOld eid v acc) Empty itemsList
      buildNew = foldl' (\acc (v, eid) -> insertRangeNew eid v acc) OrdSet.empty itemsList
  printf "\n--- Min/Max (%d elements) ---\n" n
  timeIt "old min" 5000 getSmallestOld buildOld
  timeIt "new min" 5000 getSmallestNew buildNew
  timeIt "old max" 5000 getGreatestOld buildOld
  timeIt "new max" 5000 getGreatestNew buildNew

benchMixedWorkload :: Int -> IO ()
benchMixedWorkload n = do
  let g = mkStdGen 12345
      rands = take (n * 2) (randoms g :: [Double])
      ids   = take (n * 2) (randoms g :: [Int])
      pairs = zip rands ids
      inserts = take n pairs
      queries = drop n pairs
  printf "\n--- Mixed workload: %d inserts + %d lookups/range-queries ---\n" n n
  let stepsOld = foldl' (\acc (v, eid) -> insertRangeOld eid v acc) Empty inserts
      stepsNew = foldl' (\acc (v, eid) -> insertRangeNew eid v acc) OrdSet.empty inserts
  -- Interleave: for each query element, do a range query
  do
    let go rt ((v, _eid) : rest) =
          let !res = getWithinRangeOld (v - 0.1) (v + 0.1) rt
          in (res, rt)
        go rt [] = ([], rt)
        doit rt = Prelude.foldl' (\(_, rt) p -> go rt [p]) ([], rt) queries
    timeIt "old mixed (insert + range)" 30 (fst . doit) stepsOld
  do
    let go rt ((v, _eid) : rest) =
          let !res = getWithinRangeNew (v - 0.1) (v + 0.1) rt
          in (res, rt)
        go rt [] = ([], rt)
        doit rt = Prelude.foldl' (\(_, rt) p -> go rt [p]) ([], rt) queries
    timeIt "new mixed (insert + range)" 30 (fst . doit) stepsNew

------------------------------------------------------------------------------

main :: IO ()
main = do
  printf "RangeTree Performance Comparison: Seq vs Data.Set\n"
  printf "=================================================\n"
  -- Warm up
  benchInsert 100
  -- Real benchmarks at various sizes
  mapM_ benchInsert [100, 1000, 10000]
  mapM_ benchInsertThenRemove [100, 1000, 10000]
  mapM_ benchRangeQuery [100, 1000, 10000]
  mapM_ benchMinMax [100, 1000, 10000]
  mapM_ benchMixedWorkload [100, 1000, 5000]
  printf "\nDone.\n"