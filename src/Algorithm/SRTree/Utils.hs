{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Algorithm.SRTree.Utils where

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Control.Monad
import Control.Monad.Catch
import Control.Monad.Primitive
import Control.Monad.IO.Class
import System.IO.Unsafe

-- taken from https://hackage.haskell.org/package/cubicspline-0.1.2
import Control.Arrow
import Data.List (unfoldr)

import Data.SRTree.Eval

-- | Internal helper to get dimensions (rows, columns)
matSize :: Columns -> (Int, Int)
matSize [] = (0, 0)
matSize cs@(c:_) = (U.length c, length cs)

getRows :: Columns -> [Target]
getRows mtx
  | n == 0 = []
  | otherwise = [ U.fromListN n [ c U.! i | c <- mtx ] | i <- [0 .. m - 1] ]
  where (m, n) = matSize mtx
{-# INLINE getRows #-}

getCols :: Columns -> [Target]
getCols = id
{-# INLINE getCols #-}

appendRow :: MonadThrow m => Columns -> Target -> m Columns
appendRow xs v = pure $ zipWith U.snoc xs (U.toList v)
{-# INLINE appendRow #-}

appendCol :: MonadThrow m => Columns -> Target -> m Columns
appendCol xs v = pure $ xs ++ [v]
{-# INLINE appendCol #-}

updateS :: Target -> [(Int, Double)] -> Target
updateS vec new = vec U.// new

linSpace :: Int -> (Double, Double) -> [Double]
linSpace num (lo, hi) = Prelude.take num $ iterate (\x -> x + step) lo
  where step = (hi - lo) / (fromIntegral num - 1)
{-# INLINE linSpace #-}

outer :: (MonadThrow m) => Target -> Target -> m Columns
outer arr1 arr2
  | U.null arr1 || U.null arr2 = pure []
  | otherwise = pure [ U.map (* (arr2 U.! j)) arr1 | j <- [0 .. U.length arr2 - 1] ]
{-# INLINE outer #-}

-- | Flatten list of column vectors to a row-major U.Vector Double
toRowMajor :: Columns -> U.Vector Double
toRowMajor cols = U.generate (m * n) (\ix -> let (i, j) = ix `divMod` n in (cols !! j) U.! i)
  where (m, n) = matSize cols

-- | Restore a row-major continuous U.Vector Double back to Columns
fromRowMajor :: Int -> Int -> U.Vector Double -> Columns
fromRowMajor m n vec = [ U.generate m (\i -> vec U.! (i * n + j)) | j <- [0 .. n - 1] ]

unsafeRead :: PrimMonad m => Int -> UM.MVector (PrimState m) Double -> (Int, Int) -> m Double
unsafeRead stride arr (i, j) = UM.unsafeRead arr (i * stride + j)
{-# INLINE unsafeRead #-}

unsafeWrite :: PrimMonad m => Int -> UM.MVector (PrimState m) Double -> (Int, Int) -> Double -> m ()
unsafeWrite stride arr (i, j) val = UM.unsafeWrite arr (i * stride + j) val
{-# INLINE unsafeWrite #-}

det :: Columns -> Double
det mtx
  | m == 0 || n == 0 = 1
  | otherwise = (^2) $ product [ (toRowMajor l) U.! (i * n + i) | i <- [0 .. m - 1] ]
  where
    (m, n) = matSize mtx
    (l, _) = unsafePerformIO (lu mtx)

detChol :: Columns -> Double
detChol mtx
  | m == 0 || n == 0 = 1
  | otherwise = (^2) $ product [ (toRowMajor cho) U.! (i * m + i) | i <- [0 .. m - 1] ]
  where
    (m, n) = matSize mtx
    cho = unsafePerformIO (cholesky mtx)
{-# INLINE det #-}

rangedLinearDotProd :: PrimMonad m => Int -> Int -> Int -> UM.MVector (PrimState m) Double -> m Double
rangedLinearDotProd r1 r2 len arr = go 0 0
  where
    go !acc k
      | k < len = do
          x <- UM.unsafeRead arr (r1 + k)
          y <- UM.unsafeRead arr (r2 + k)
          go (acc + x * y) (k + 1)
      | otherwise = pure acc
{-# INLINE rangedLinearDotProd #-}

data NegDef = NegDef deriving Show
instance Exception NegDef

cholesky :: (PrimMonad m, MonadThrow m, MonadIO m) => Columns -> m Columns
cholesky arr
  | m /= n = error $ "cholesky dimension mismatch " <> show m <> " X " <> show n
  | m == 0 = pure []
  | otherwise = do
      l <- UM.new (m * m)
      let orig = toRowMajor arr
      forM_ [0 .. m - 1] $ \i ->
        forM_ [0 .. m - 1] $ \j ->
          if i < j then unsafeWrite m l (i, j) 0
          else do
            let cur = orig U.! (i * m + j)
                rowI = i * m
                rowJ = j * m
            xjj <- UM.unsafeRead l (rowJ + j)
            tot <- rangedLinearDotProd rowI rowJ j l
            let delta = cur - tot
            if i == j
              then if delta <= 0
                   then throwM NegDef
                   else UM.unsafeWrite l (rowI + j) (sqrt delta)
              else UM.unsafeWrite l (rowI + j) (delta / xjj)
      frozen <- U.unsafeFreeze l
      pure $ fromRowMajor m m frozen
  where (m, n) = matSize arr
{-# INLINE cholesky #-}

invChol :: (PrimMonad m, MonadThrow m, MonadIO m) => Columns -> m Columns
invChol arr = do
  lMtx <- cholesky arr
  let (m, _) = matSize arr
  mtx <- U.thaw (toRowMajor lMtx)
  forM_ [0 .. m - 1] $ \i -> do
    lII <- unsafeRead m mtx (i, i)
    unsafeWrite m mtx (i, i) (1 / lII)
    forM_ [0 .. i - 1] $ \j -> do
      tot <- rangedLinearDotProd (i * m + j) (j * m + j) (i - j) mtx
      unsafeWrite m mtx (j, i) ((-tot) / lII)
      unsafeWrite m mtx (i, j) 0

  mm <- UM.replicate (m * m) 0
  forM_ [0 .. m - 1] $ \i -> do
    dii <- rangedLinearDotProd (i * m + i) (i * m + i) (m - i) mtx
    unsafeWrite m mm (i, i) dii
    forM_ [i + 1 .. m - 1] $ \j -> do
      dij <- rangedLinearDotProd (i * m + j) (j * m + j) (m - j) mtx
      unsafeWrite m mm (i, j) dij
      unsafeWrite m mm (j, i) dij
  frozen <- U.unsafeFreeze mm
  pure $ fromRowMajor m m frozen
{-# INLINE invChol #-}

lu :: (PrimMonad m, MonadThrow m, MonadIO m) => Columns -> m (Columns, Columns)
lu mtx = do
  let (m, n) = matSize mtx
      orig = toRowMajor mtx
  u <- UM.replicate (m * n) 0
  forM_ [0 .. min m n - 1] $ \i -> unsafeWrite n u (i, i) 1
  l <- UM.replicate (m * n) 0

  let buildLVal !i !j = do
        let go !k !s
              | k == j = pure s
              | otherwise = do
                  lik <- unsafeRead n l (i, k)
                  ukj <- unsafeRead n u (k, j)
                  go (k+1) (s + lik * ukj)
        s' <- go 0 0
        unsafeWrite n l (i, j) ((orig U.! (i * n + j)) - s')

      buildL !i !j = when (i /= m) $ do
        buildLVal i j
        buildL (i+1) j

      buildUVal !i !j = do
        let go !k !s
              | k == j = pure s
              | otherwise = do
                  ljk <- unsafeRead n l (j, k)
                  uki <- unsafeRead n u (k, i)
                  go (k+1) (s + ljk * uki)
        s' <- go 0 0
        ljj <- unsafeRead n l (j, j)
        unsafeWrite n u (j, i) (((orig U.! (j * n + i)) - s') / ljj)

      buildU !i !j = when (i /= n) $ do
        buildUVal i j
        buildU (i+1) j

      buildLU !j = when (j /= n && j /= m) $ do
        buildL j j
        buildU j j
        buildLU (j+1)

  buildLU 0
  finalL <- U.unsafeFreeze l
  finalU <- U.unsafeFreeze u
  pure (fromRowMajor m n finalL, fromRowMajor m n finalU)

forwardSub :: (PrimMonad m, MonadThrow m, MonadIO m) => Columns -> Target -> m Target
forwardSub a b = do
  let m = U.length b
      n = length a
      aMat = toRowMajor a
  x <- UM.replicate m 0
  let coeff !i !j !s
        | j == i = pure s
        | otherwise = do
            let aij = aMat U.! (i * n + j)
            xj <- UM.unsafeRead x j
            coeff i (j+1) (s + aij * xj)
      go !i = when (i /= m) $ do
        let bi = b U.! i
            aii = aMat U.! (i * n + i)
        c <- coeff i 0 0
        UM.unsafeWrite x i ((bi - c) / aii)
        go (i+1)
  go 0
  U.unsafeFreeze x

backwardSub :: (PrimMonad m, MonadThrow m, MonadIO m) => Columns -> Target -> m Target
backwardSub a b = do
  let m = U.length b
      n = length a
      aMat = toRowMajor a
  x <- UM.replicate m 0
  let coeff !i !j !s
        | j == m = pure s
        | otherwise = do
            let aij = aMat U.! (i * n + j)
            xj <- UM.unsafeRead x j
            coeff i (j+1) (s + aij * xj)
      go !i = when (i >= 0) $ do
        let bi = b U.! i
            aii = aMat U.! (i * n + i)
        c <- coeff i (i+1) 0
        UM.unsafeWrite x i ((bi - c) / aii)
        go (i-1)
  go (m-1)
  U.unsafeFreeze x

luSolve :: (PrimMonad m, MonadThrow m, MonadIO m) => Columns -> Target -> m Target
luSolve a b = do
  (l, u) <- lu a
  forwardSub l b >>= backwardSub u

type PolyCos = (Double, Double, Double)

cubicSplineCoefficients :: [(Double, Double)] -> [PolyCos]
cubicSplineCoefficients xs = Prelude.zip3 x y z'
  where
    x = map fst xs
    y = map snd xs
    xdiff = zipWith (-) (tail x) x
    xdiff' = U.fromList xdiff

    dydx :: U.Vector Double
    dydx = U.fromList $ Prelude.zipWith3 (\y0 y1 xd -> (y0 - y1) / xd) (tail y) y xdiff

    n = length x

    w :: [Double]
    w = 0 : nextW 1 w
      where
        nextW ix (wi : t)
          | ix == n - 1 = []
          | otherwise =
              let m = (xdiff' U.! (ix - 1)) * (2 - wi) + 2 * (xdiff' U.! ix)
                  wn = (xdiff' U.! ix) / m
              in wn : nextW (ix + 1) t

    z :: [Double]
    z = 0 : nextZ 1 z
      where
        nextZ ix (zi : t)
          | ix == n - 1 = [0]
          | otherwise =
              let m = (xdiff' U.! (ix - 1)) * (2 - (w !! (ix - 1))) + 2 * (xdiff' U.! ix)
                  zn = (6 * ((dydx U.! ix) - (dydx U.! (ix - 1))) - (xdiff' U.! (ix - 1)) * zi) / m
              in zn : nextZ (ix + 1) t

    z' :: [Double]
    z' = Prelude.reverse $ 0 : [z !! i - w !! i * z !! (i + 1) | i <- [n - 2, n - 3 .. 0]]

chunkBy :: Int -> [t] -> [[t]]
chunkBy n = unfoldr go
  where
    go [] = Nothing
    go x = Just $ splitAt n x

genSplineFun :: [(Double, Double)] -> Double -> Double
genSplineFun pts x
  | length xs < 2 = x
  | x < head xs   = y1 + (x - x1) * (y2 - y1) / (x2 - x1)
  | x > last xs   = y_1 + (x - x_1) * (y_n - y_1) / (x_n - x_1)
  | otherwise     = go xs $ zip coefs (tail coefs)
  where
    xs = map fst pts
    ys = map snd pts
    coefs = cubicSplineCoefficients pts
    x1 = head xs;  y1 = head ys
    x2 = xs !! 1;  y2 = ys !! 1
    x_1 = xs !! (len - 2);  y_1 = ys !! (len - 2)
    x_n = last xs;          y_n = last ys
    len = length xs

    evalAt (a1, b1, c1) (a2, b2, c2) y =
      let hi1 = a2 - a1
      in c1 / (6 * hi1) * (a2 - y)^3 + c2 / (6 * hi1) * (y - a1)^3 +
         (b2 / hi1 - c2 * hi1 / 6) * (y - a1) + (b1 / hi1 - c1 * hi1 / 6) * (a2 - y)

    go [x1, x2] [(c1, c2)] = evalAt c1 c2 x
    go (x1 : x2 : xs') ((c1, c2) : cs)
      | x >= x1 && x <= x2 = evalAt c1 c2 x
      | otherwise          = go (x2 : xs') cs
