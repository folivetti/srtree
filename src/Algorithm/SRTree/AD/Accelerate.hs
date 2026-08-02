{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Algorithm.SRTree.AD.Accelerate
  ( compileAccelerateTree
  ) where

import Data.SRTree
import Data.Array.Accelerate as A
import Data.Array.Accelerate.LLVM.Native as CPU
import Data.IntMap.Strict qualified as IntMap
import Data.Vector.Unboxed qualified as VU
import Data.Vector.Generic qualified as VG
import Data.Vector qualified as VB
import Data.Vector.Storable qualified as VS
import Prelude hiding (zipWith, replicate, sum, map, log, abs, sqrt, recip)
import Algorithm.SRTree.AD.CompiledAD

import Data.IORef (IORef, newIORef, readIORef, modifyIORef', writeIORef)
import System.IO.Unsafe (unsafePerformIO)
import System.CPUTime (getCPUTime)
import Data.Time.Clock.POSIX (getPOSIXTime, POSIXTime)
import Control.Exception (evaluate)
import System.IO (stderr, hPutStrLn, openBinaryFile, hFileSize, hClose, IOMode(..))
import Control.Monad (when)
import System.Directory (getXdgDirectory, XdgDirectory(..), listDirectory, doesFileExist, removeFile)
import System.FilePath ((</>))

{-# INLINE diffPureAcc #-}
diffPureAcc :: Op -> Exp Double -> Exp Double -> Exp Double -> Exp Double -> Exp (Double, Double)
diffPureAcc Add dx _  _  _  = A.lift (dx, dx)
diffPureAcc Sub dx _  _  _  = A.lift (dx, -dx)
diffPureAcc Mul dx fx gy _  = A.lift (dx * gy, dx * fx)
diffPureAcc Div dx _  gy fg = A.lift (dx / gy, dx * (-(fg / gy)))
diffPureAcc Power dx fx gy fg =
    A.lift ( fixNaN (dx * gy * fg / fx)
           , fixNaN (dx * fg * A.log fx) )
diffPureAcc PowerAbs dx fx gy fg =
    let v2 = A.abs fx
    in A.lift ( fixNaN (dx * (fx * gy) * fg / (v2 * v2))
              , fixNaN (dx * fg * A.log (A.abs fx)) )
diffPureAcc AQ dx fx gy _ =
    let dxl = dx * (recip (sqrt (1 + gy * gy)))
        dxy = fx * gy * (dxl ** 3)
    in A.lift (dxl, dxy)

{-# INLINE fixNaN #-}
fixNaN :: Exp Double -> Exp Double
fixNaN x = A.isNaN x ? (0, x)

-- You will need to map your specific Enum types to Accelerate's math functions
evalFunAcc :: Function -> Exp Double -> Exp Double
evalFunAcc Id = id
evalFunAcc Abs = A.abs
evalFunAcc Sin = A.sin
evalFunAcc Cos = A.cos
evalFunAcc Tan = A.tan
evalFunAcc Sinh = A.sinh
evalFunAcc Cosh = A.cosh
evalFunAcc Tanh = A.tanh
evalFunAcc ASin = A.asin
evalFunAcc ACos = A.acos
evalFunAcc ATan = A.atan
evalFunAcc ASinh = A.asinh
evalFunAcc ACosh = A.acosh
evalFunAcc ATanh = A.atanh
evalFunAcc Sqrt = A.sqrt
evalFunAcc SqrtAbs = A.sqrt . A.abs
evalFunAcc Cbrt = cbrt where cbrt x = A.signum x * A.abs x ** (1/3)
evalFunAcc Square = (A.^(2 :: Exp Int))
evalFunAcc Log = A.log
evalFunAcc LogAbs = A.log . A.abs
evalFunAcc Exp = A.exp
evalFunAcc Recip = A.recip
evalFunAcc Cube = (A.^(3 :: Exp Int))
{-# INLINE evalFunAcc #-}


evalOpAcc :: Op -> Exp Double -> Exp Double -> Exp Double
evalOpAcc Add l r      = l + r
evalOpAcc Sub l r      = l - r
evalOpAcc Mul l r      = l * r
evalOpAcc Div l r      = l / r
evalOpAcc Power l r    = l ** r
evalOpAcc PowerAbs l r = A.abs l ** r
evalOpAcc AQ l r       = l / A.sqrt (1 + r*r)
{-# INLINE evalOpAcc #-}

derivativeAcc :: Function -> Exp Double -> Exp Double
derivativeAcc Id      = const 1
derivativeAcc Abs     = \x -> x / A.abs x
derivativeAcc Sin     = A.cos
derivativeAcc Cos     = A.negate . A.sin
derivativeAcc Tan     = A.recip . (**2.0) . A.cos
derivativeAcc Sinh    = A.cosh
derivativeAcc Cosh    = A.sinh
derivativeAcc Tanh    = (1-) . (**2.0) . A.tanh
derivativeAcc ASin    = A.recip . A.sqrt . (1-) . (A.^(2 :: Exp Int))
derivativeAcc ACos    = A.negate . A.recip . A.sqrt . (1-) . (A.^(2 :: Exp Int))
derivativeAcc ATan    = A.recip . (1+) . (A.^(2 :: Exp Int))
derivativeAcc ASinh   = A.recip . A.sqrt . (1+) . (A.^(2 :: Exp Int))
derivativeAcc ACosh   = \x -> 1 / (A.sqrt (x-1) * A.sqrt (x+1))
derivativeAcc ATanh   = A.recip . (1-) . (A.^(2 :: Exp Int))
derivativeAcc Sqrt    = A.recip . (2*) . A.sqrt
derivativeAcc SqrtAbs = \x -> x / (2.0 * A.abs x ** (3.0/2.0))
derivativeAcc Cbrt    = A.recip . (3*) . (**(1/3)) . (A.^(2 :: Exp Int))
derivativeAcc Square  = (2*)
derivativeAcc Exp     = A.exp
derivativeAcc Log     = A.recip
derivativeAcc LogAbs  = A.recip
derivativeAcc Recip   = A.negate . A.recip . (A.^(2 :: Exp Int))
derivativeAcc Cube    = (3*) . (A.^(2 :: Exp Int))
{-# INLINE derivativeAcc #-}

-- Profiling counters (CPU time)
{-# NOINLINE compileTime #-}
compileTime :: IORef Integer
compileTime = unsafePerformIO (newIORef 0)

{-# NOINLINE compileCount #-}
compileCount :: IORef Int
compileCount = unsafePerformIO (newIORef 0)

{-# NOINLINE evalTime #-}
evalTime :: IORef Integer
evalTime = unsafePerformIO (newIORef 0)

{-# NOINLINE evalCount #-}
evalCount :: IORef Int
evalCount = unsafePerformIO (newIORef 0)

-- Profiling counters (wall time)
{-# NOINLINE compileWall #-}
compileWall :: IORef Double
compileWall = unsafePerformIO (newIORef 0)

{-# NOINLINE evalWall #-}
evalWall :: IORef Double
evalWall = unsafePerformIO (newIORef 0)

-- | One-time flag so the zero-byte cache sweep runs only once per process.
{-# NOINLINE cacheCleaned #-}
cacheCleaned :: IORef Bool
cacheCleaned = unsafePerformIO (newIORef False)

-- | Single-worker target: exactly 1 thread, bypasses the env-var-based
-- defaultTarget (which is a CAF initialized before setEnv takes effect).
{-# NOINLINE singleWorker #-}
singleWorker :: CPU.Native
singleWorker = unsafePerformIO (CPU.createTarget [0])

-- | accelerate-llvm-native caches each JIT-compiled kernel as <hash>.o and
-- <hash>.so in the XDG cache dir, but the cache is not crash-safe: hits are
-- validated only by 'doesFileExist', and the .so is written non-atomically by
-- the system linker. An interrupted or concurrent link step leaves a zero-byte
-- .so, which dlopen then rejects with "file too short" on every later run.
-- A valid .so is never zero bytes, so we heal the cache by deleting zero-byte
-- .so/.o files once per process before compiling.
{-# NOINLINE cleanZeroByteCache #-}
cleanZeroByteCache :: IO ()
cleanZeroByteCache = do
  dir <- getXdgDirectory XdgCache "accelerate"
  emptyFiles <- walkZeroByte dir
  Prelude.mapM_ removeFile emptyFiles
  when (Prelude.not (Prelude.null emptyFiles)) $
    hPutStrLn stderr ("accelerate: removed " Prelude.++ show (Prelude.length emptyFiles) Prelude.++ " corrupt (zero-byte) cache file(s)")

walkZeroByte :: FilePath -> IO [FilePath]
walkZeroByte dir = do
  entries <- listDirectory dir
  results <- Prelude.mapM go entries
  pure (Prelude.concat results)
  where
    go e = do
      let p = dir </> e
      isFile <- doesFileExist p
      if isFile
        then do
          sz <- fileSize p
          pure [ p | sz Prelude.== 0 ]
        else walkZeroByte p
    fileSize :: FilePath -> IO Integer
    fileSize p = do
      h <- openBinaryFile p ReadMode
      s <- hFileSize h
      hClose h
      pure s

-- | Run the one-time cache sweep; guarded so it only walks the (possibly very
-- large) cache directory once per process.
{-# NOINLINE ensureCleanCache #-}
ensureCleanCache :: IORef Bool -> IO ()
ensureCleanCache done = do
  already <- readIORef done
  when (Prelude.not already) $ do
    cleanZeroByteCache
    writeIORef done True

-- | Compiles the AST into an LLVM JIT closure.
-- Call this exactly ONCE before your NLopt optimization loop.
compileAccelerateTree :: CompiledTree -> [VU.Vector Double] -> VU.Vector Double -> (VS.Vector Double -> (Double, VS.Vector Double))
compileAccelerateTree ct xss ys =
    let
        jittedFunc = unsafePerformIO $ do
            ensureCleanCache cacheCleaned
            t0cpu <- getCPUTime
            t0wal <- getPOSIXTime
            let !jf = CPU.run1With singleWorker (buildAccGraph ct xss ys)
            t1cpu <- getCPUTime
            t1wal <- getPOSIXTime
            modifyIORef' compileTime (+ (t1cpu - t0cpu))
            modifyIORef' compileWall (+ realToFrac (t1wal - t0wal))
            modifyIORef' compileCount (+ 1)
            pure jf

    in \theta -> unsafePerformIO $ do
        t0cpu <- getCPUTime
        t0wal <- getPOSIXTime
        let thetaArr = A.fromList (Z :. VS.length theta) (VS.toList theta)
            (objArr, gradArr) = jittedFunc thetaArr
            obj  = A.indexArray objArr Z
            grad = VS.fromList (A.toList gradArr)
        evaluate obj
        evaluate (VS.length grad)
        t1cpu <- getCPUTime
        t1wal <- getPOSIXTime
        modifyIORef' evalTime (+ (t1cpu - t0cpu))
        modifyIORef' evalWall (+ realToFrac (t1wal - t0wal))
        modifyIORef' evalCount (+ 1)
        cnt <- readIORef evalCount

        pure (obj, grad)


-- | Builds the AST in the Accelerate EDSL
buildAccGraph :: CompiledTree
              -> [VU.Vector Double]
              -> VU.Vector Double
              -> Acc (Array DIM1 Double)
              -> Acc (Scalar Double, Vector Double)
buildAccGraph ct xss ys theta = A.lift (obj, gradPacked)
  where
    root  = ctRoot ct
    m     = ctM ct
    p     = VU.length (ctDyn ct) -- Approximation, count actual params below
    nodes = ctNodes ct
    dyn   = ctDyn ct

    mShape = A.constant (Z :. m)

    -- 1. FORWARD PASS
    -- We build a static map of array expressions.
    -- Static data is baked directly into the graph via A.use
    forward :: IntMap.IntMap (Acc (Array DIM1 Double))
    forward = foldl' step IntMap.empty [0 .. root]
      where
        step acc key
              | Prelude.not (dyn VU.! key) =
                  let statVec = VU.slice (key * m) m (ctStatic ct)
                  in IntMap.insert key (A.use (A.fromList (Z :. m) (VU.toList statVec))) acc
          | otherwise =
              IntMap.insert key (evalNode key acc) acc

        evalNode key acc = case nodes VB.! key of
            Param ix -> A.fill mShape (theta A.!! A.constant ix)
            Uni f t  -> A.map (evalFunAcc f) (acc IntMap.! t)
            Bin op l r -> A.zipWith (evalOpAcc op) (acc IntMap.! l) (acc IntMap.! r)
            Var ix   -> A.use (A.fromList (Z :. m) (VU.toList (xss Prelude.!! ix)))
            Const c  -> A.fill mShape (A.constant c)

    -- 2. BACKWARD PASS (Adjoints)
    initAdjoints = IntMap.singleton root (A.fill mShape 1.0)

    adjoints :: IntMap.IntMap (Acc (Array DIM1 Double))
    adjoints = foldl' bwdStep initAdjoints [root, root - 1 .. 0]
      where
        bwdStep adj key
          | Prelude.not (dyn VU.! key) = adj
          | otherwise = case nodes VB.! key of
              Bin op l r ->
                  let v  = IntMap.findWithDefault (A.fill mShape 0.0) key adj
                      xl = forward IntMap.! l
                      xr = forward IntMap.! r
                      fg = forward IntMap.! key

                      -- Fused inner loop across the 4 arrays
                      zipped = A.zip4 v xl xr fg
                      dl = A.map (\t -> A.fst (diffPureAcc op (fst4 t) (snd4 t) (thd4 t) (fth4 t))) zipped
                      dr = A.map (\t -> A.snd (diffPureAcc op (fst4 t) (snd4 t) (thd4 t) (fth4 t))) zipped

                      adjL = IntMap.insertWith (A.zipWith (+)) l dl adj
                  in IntMap.insertWith (A.zipWith (+)) r dr adjL

              Uni f t ->
                  let v  = IntMap.findWithDefault (A.fill mShape 0.0) key adj
                      x  = forward IntMap.! t
                      dt = A.zipWith (*) v (A.map (derivativeAcc f) x)
                  in IntMap.insertWith (A.zipWith (+)) t dt adj

              _ -> adj

    -- 3. EXTRACTION

    -- Total objective is the sum of the root node's forward array
    obj = A.sum (forward IntMap.! root)

    -- Pre-calculate the scalar gradient for every Param node.
    -- We use findWithDefault to safely handle "dead" branches of the AST
    -- that were optimized out and never received an adjoint.
    paramAdjoints :: [(Int, Exp Double)]
    paramAdjoints = [ (ix, A.the (A.sum (IntMap.findWithDefault (A.fill mShape 0.0) k adjoints)))
                    | (k, Param ix) <- Prelude.zip [0..] (VB.toList nodes) ]

    -- Generate a gradient array that EXACTLY matches the shape of the input theta.
    -- For each parameter index `i`, we fold over the known Param nodes and sum
    -- their gradients. Accelerate compiles this into a highly optimized select block.
    gradPacked = A.generate (A.shape theta) $ \(I1 i) ->
        foldr (\(ix, val) acc -> i A.== A.constant ix ? (acc + val, acc)) 0.0 paramAdjoints

-- Helper tuple extractors for zip4
fst4 (T4 a _ _ _) = a
snd4 (T4 _ b _ _) = b
thd4 (T4 _ _ c _) = c
fth4 (T4 _ _ _ d) = d
