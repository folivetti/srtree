{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Algorithm.Massiv.Utils where

import Data.Massiv.Array hiding ( forM_, unzip, map, init, zipWith, zip, tail, replicate, take )
import qualified Data.Massiv.Array as A
import qualified Data.Massiv.Array.Unsafe as UMA
import qualified Data.Massiv.Array.Mutable as MMA
import Control.Monad
import Data.Vector.Storable ((//))
import System.IO.Unsafe

-- taken from https://hackage.haskell.org/package/cubicspline-0.1.2
import Control.Arrow
import Data.List(unfoldr)

import Data.SRTree.Eval

type MMassArray m = MMA.MArray (PrimState m) S Ix2 Double

getRows :: SRMatrix -> Array B Ix1 PVector
getRows = computeAs B . outerSlices
{-# INLINE getRows #-}
getCols :: SRMatrix -> Array B Ix1 PVector
getCols = computeAs B . A.map (computeAs S) . innerSlices
{-# INLINE getCols #-}

appendRow :: MonadThrow m => SRMatrix -> PVector -> m SRMatrix
appendRow xs v = computeAs S <$> (stackOuterSlicesM . toList . computeAs B $ snoc (outerSlices xs) v)
{-# INLINE appendRow #-}

appendCol :: MonadThrow m => SRMatrix -> PVector -> m SRMatrix
appendCol xs v = computeAs S <$> (stackInnerSlicesM . toList . computeAs B $ snoc (A.map (computeAs S) $ innerSlices xs) v)
{-# INLINE appendCol #-}

updateS :: Array S Ix1 Double -> [(Int, Double)] -> Array S Ix1 Double
updateS vec new = fromStorableVector Seq $ toStorableVector vec // new

linSpace :: Int -> (Double, Double) -> [Double]
linSpace num (lo, hi) = Prelude.take num $ iterate (\x -> x + step) lo
  where
    step = (hi - lo) / (fromIntegral num - 1)
{-# INLINE linSpace #-}

outer :: (MonadThrow m)
  => PVector
  -> PVector
  -> m SRMatrix
outer arr1 arr2
  | isEmpty arr1 || isEmpty arr2 = pure $ setComp comp empty
  | otherwise =
      pure $ makeArray comp (Sz2 m1 m2) $ \(i :. j) ->
          UMA.unsafeIndex arr1 i * UMA.unsafeIndex arr2 j
  where
      comp   = getComp arr1 <> getComp arr2
      Sz1 m1 = size arr1
      Sz1 m2 = size arr2
{-# INLINE outer #-}

det :: SRMatrix -> Double 
det mtx
  | m==0 || n==0 = 1
  | otherwise    = (^2) $ Prelude.product [l ! (i :. i) | i <- [0 .. m-1]]
  where
    Sz (m :. n)  = size mtx
    (l, _) = unsafePerformIO (lu mtx)
      
detChol :: SRMatrix -> Double
detChol mtx
  | m==0 || n==0 = 1
  | otherwise    = (^2) $ Prelude.product [cho ! (i :. i) | i <- [0 .. m-1]]
  where
    Sz (m :. n)  = size mtx
    cho = unsafePerformIO (cholesky mtx)
{-# INLINE det #-}

rangedLinearDotProd :: PrimMonad m => Int -> Int -> Int -> MMassArray m -> m Double
rangedLinearDotProd r1 r2 len arr = go 0 0
  where
    go !acc k
      | k < len   = do x <- UMA.unsafeLinearRead arr (r1 + k)
                       y <- UMA.unsafeLinearRead arr (r2 + k)
                       go (acc + x*y) (k + 1)
      | otherwise = pure acc
{-# INLINE rangedLinearDotProd #-}

data NegDef = NegDef
    deriving Show

instance Exception NegDef

cholesky :: (PrimMonad m, MonadThrow m, MonadIO m)
  => SRMatrix
  -> m SRMatrix
cholesky arr
  | m /= n       = throwM $ SizeMismatchException (size arr) (size arr)
  | isEmpty arr  = pure $ setComp comp empty
  | otherwise    = MMA.createArrayS_ (size arr) create
  where
    comp      = getComp arr
    (Sz2 m n) = size arr
    create l  = Prelude.mapM_ (update l) [i :. j | i <- [0..m-1], j <- [0..m-1]]

    update l ix@(i :. j)
      | i < j     = UMA.unsafeWrite l ix 0
      | otherwise = do let cur  = UMA.unsafeIndex arr ix
                           rowI = i*m
                           rowJ = j*m
                       xjj <- UMA.unsafeLinearRead l (rowJ + j)
                       tot <- rangedLinearDotProd rowI rowJ j l
                       let delta = cur - tot
                       if i == j
                          then if delta <= 0
                                 then throwM NegDef -- SizeMismatchException (size arr) (size arr) -- look at a better exception
                                 else UMA.unsafeLinearWrite l (rowI + j) (sqrt delta)
                          else UMA.unsafeLinearWrite l (rowI + j) (delta / xjj)
{-# INLINE cholesky #-}

invChol :: (PrimMonad m, MonadThrow m, MonadIO m) => SRMatrix -> m SRMatrix
invChol arr = do l <- cholesky arr -- lower diag
                 mtx <- thawS l
                 forM_ [0 .. m-1] $ \i -> do
                     lII <- UMA.unsafeRead mtx (i :. i)
                     UMA.unsafeWrite mtx (i :. i) (1 / lII)
                     forM_ [0 .. i-1] $ \j -> do
                         tot <- rangedLinearDotProd (i*m + j) (j*m + j) (i-j) mtx
                         UMA.unsafeWrite mtx (j :. i) ((-tot)/lII)
                         UMA.unsafeWrite mtx (i :. j) 0
                 mm <- newMArray (Sz2 m m) 0
                 forM_ [0 .. m-1] $ \i -> do
                     dii <- rangedLinearDotProd (i*m + i) (i*m + i) (m - i) mtx
                     UMA.unsafeWrite mm (i :. i) dii
                     forM_ [i+1 .. m-1] $ \j -> do
                          dij <- rangedLinearDotProd (i*m + j) (j*m + j) (m - j) mtx
                          UMA.unsafeWrite mm (i :. j) dij
                          UMA.unsafeWrite mm (j :. i) dij
                 freezeS mm

  where
    Sz2 m _ = size arr
{-# INLINE invChol #-}

-- LU decomposition and solver taken from https://hackage.haskell.org/package/linear-1.23/docs/src/Linear.Matrix.html
lu :: (PrimMonad m, MonadThrow m, MonadIO m) => SRMatrix -> m (SRMatrix, SRMatrix)
lu mtx = do
    let (Sz2 m n) = size mtx
    u <- thawS $ computeAs S $ identityMatrix (Sz m)
    l <- thawS $ A.replicate Seq (Sz2 m n) 0

    let buildLVal !i !j = do
            let go !k !s
                    | k == j    = pure s
                    | otherwise = do lik <- UMA.unsafeRead l (i :. k)
                                     ukj <- UMA.unsafeRead u (k :. j)
                                     go (k+1) ( s + (lik * ukj) )
            s' <- go 0 0
            UMA.unsafeWrite l (i :. j) ((mtx ! (i :. j)) - s')
            -- pure l
        buildL !i !j
            = when (i /= n) $ do buildLVal i j
                                 buildL (i+1) j
        buildUVal !i !j = do
            let go !k !s
                    | k == j = pure s
                    | otherwise = do ljk <- UMA.unsafeRead l (j :. k)
                                     uki <- UMA.unsafeRead u (k :. i)
                                     go (k+1) (s + ljk * uki)

            s' <- go 0 0
            ljj <- UMA.unsafeRead l (j :. j)
            UMA.unsafeWrite u (j :. i) (((mtx ! (j :. i)) - s') / (ljj))
            -- pure u

        buildU !i !j
            = when (i /= n) $ do buildUVal i j
                                 buildU (i+1) j
        buildLU !j
            = when (j /= n) $
                 do buildL j j
                    buildU j j
                    buildLU (j+1)
    buildLU 0
    finalL <- freezeS l
    finalU <- freezeS u
    pure (finalL, finalU)

forwardSub :: (PrimMonad m, MonadThrow m, MonadIO m) => SRMatrix -> PVector -> m PVector
forwardSub a b = do
    let (Sz m) = size b
    x <- thawS $ A.replicate Seq (Sz1 m) 0
    let coeff !i !j !s
            | j == i = pure s
            | otherwise = do let aij = a ! (i :. j)
                             xj  <- UMA.unsafeRead x j
                             coeff i (j+1) (s + aij * xj)
        go !i = when (i/= m) $
                   do let bi = b ! i
                          aii = a ! (i :. i)
                      c <- coeff i 0 0
                      UMA.unsafeWrite x i ((bi - c)/aii)
                      go (i+1)
    go 0
    freezeS x

backwardSub :: (PrimMonad m, MonadThrow m, MonadIO m) => SRMatrix -> PVector -> m PVector
backwardSub a b = do
    let (Sz m) = size b
    x <- thawS $ A.replicate Seq (Sz1 m) 0
    let coeff !i !j !s
            | j == m = pure s
            | otherwise = do let aij = a ! (i :. j)
                             xj  <- UMA.unsafeRead x j
                             coeff i (j+1) (s + aij * xj)
        go !i = when (i >= 0) $
                        do let bi  = b ! i
                               aii = a ! (i :. i)
                           c <- coeff i (i+1) 0
                           UMA.unsafeWrite x i ((bi - c)/aii)
                           go (i-1)
    go (m-1)
    freezeS x

luSolve :: (PrimMonad m, MonadThrow m, MonadIO m) => SRMatrix -> PVector -> m PVector
luSolve a b = do (l, u) <- lu a
                 forwardSub l b >>= backwardSub u

type PolyCos = (Double, Double, Double)

-- | Given a list of (x,y) co-ordinates, produces a list of coefficients to cubic equations, with knots at each of the initially provided x co-ordinates. Natural cubic spline interpololation is used. See: <http://en.wikipedia.org/wiki/Spline_interpolation#Interpolation_using_natural_cubic_spline>.
cubicSplineCoefficients :: [(Double, Double)] -> [PolyCos]
cubicSplineCoefficients xs = Prelude.zip3 x y z'
    where
      x = map fst xs
      y = map snd xs
      xdiff = zipWith (-) (tail x) x
      xdiff' = fromList Seq xdiff :: Vector S Double
      dydx :: Vector S Double
      dydx  = fromList Seq $ Prelude.zipWith3 (\y0 y1 xd -> (y0-y1)/xd) (tail y) y xdiff
      n = length x

      w :: [Double]
      w = 0 : nextW 1 w
        where
          nextW ix (wi : t)
            | ix == n-1 = []
            | otherwise = let m  = (xdiff' ! (ix-1)) * (2 - wi) + 2 * (xdiff' ! ix)
                              wn = (xdiff' ! ix) / m
                           in wn : nextW (ix+1) t
      z :: [Double]
      z = 0 : nextZ 1 z
        where
          nextZ ix (zi : t)
            | ix == n-1 = [0]
            | otherwise = let m  = (xdiff' ! (ix-1)) * (2 - (w !! (ix-1))) + 2 * (xdiff' ! ix)
                              zn = (6*((dydx ! ix) - (dydx ! (ix-1))) - (xdiff' ! (ix-1)) * zi) / m
                          in zn : nextZ (ix+1) t

      z' :: [Double]
      z' = Prelude.reverse $ 0 : [z !! i - w !! i * z !! (i+1) | i <- [n-2,n-3 .. 0]]

chunkBy :: Int -> [t] -> [[t]]
chunkBy n = unfoldr go
    where go [] = Nothing
          go x  = Just $ splitAt n x

genSplineFun :: [(Double, Double)] -> Double -> Double
genSplineFun pts x = go xs $ zip coefs (tail coefs)
  where
    xs    = map fst pts
    coefs = cubicSplineCoefficients pts
    evalAt (a1,b1,c1) (a2,b2,c2) y = let hi1 = a2 - a1
                                     in c1/(6*hi1)*(a2-y)^3 + c2/(6*hi1)*(y-a1)^3 + (b2/hi1 - c2*hi1/6)*(y-a1) + (b1/hi1 - c1*hi1/6)*(a2-y)

    go [x1,x2] [(c1,c2)] = evalAt c1 c2 x
    go (x1:x2:xs) ((c1,c2):cs)
      | x < x1 = evalAt c1 c2 x
      | x >= x1 && x <= x2 = evalAt c1 c2 x
      | otherwise          = go (x2:xs) cs
