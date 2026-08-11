{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Algorithm.SRTree.AD.Accelerate
  ( compileAccelerateTree
  , encodeTree, Encoded(..)
  , multiWorker
  ) where

import Data.SRTree
import Data.Array.Accelerate as A
import Data.Array.Accelerate.LLVM.Native as CPU
import Data.Array.Accelerate.Sugar.Array (Array(..))
import qualified Data.Array.Accelerate.Representation.Array as R
import Data.Array.Accelerate.Array.Unique (newUniqueArray)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as ISet
import Data.Vector.Unboxed qualified as VU
import Data.Vector.Unboxed.Mutable qualified as VUM
import Data.Vector qualified as VB
import Data.Vector.Storable qualified as VS
import Prelude hiding (zipWith, replicate, sum, map, log, abs, sqrt, recip)
import Algorithm.SRTree.AD.CompiledAD

import Data.IORef (IORef, newIORef, readIORef, modifyIORef', atomicModifyIORef', writeIORef)
import System.IO.Unsafe (unsafePerformIO)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Control.Exception (evaluate)
import Control.Concurrent (getNumCapabilities)
import System.IO (stderr, hPutStrLn, openBinaryFile, hFileSize, hClose, IOMode(..))
import Control.Monad (when)
import System.Environment (lookupEnv)
import System.Directory (getXdgDirectory, XdgDirectory(..), listDirectory, doesFileExist, removeFile)
import System.FilePath ((</>))
import Data.List (foldl', init)
import qualified Data.List
import qualified Data.Map.Strict as Map

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

-- ----------------------------------------------------------------------------
-- Fixed-shape interpreter (design E): one compiled kernel handles every tree.
-- The kernel AST depends only on the shape constants below; all per-tree
-- structure arrives as runtime inputs (metaF / widthF / parentF). Padding is
-- chosen from the measured shape distribution (data.tsv, maxSize 30): max
-- level width 9, max depth 15, max in-degree 3. Trees that overflow fall back
-- to the Phase-2 JIT.
-- ----------------------------------------------------------------------------
maxDepth, maxWidth, maxParents :: Int
maxDepth  = 16   -- levels, >= observed depth 15
maxWidth  = 16   -- nodes per level, >= observed max width 9
maxParents = 4   -- parents per node, > observed max in-degree 3

-- metaF field offsets (one Int per node slot per field)
kKind, kGid, kArg, kArg2, kFcode, kOcode, kDyn, kFields :: Int
kKind   = 0
kGid    = 1
kArg    = 2
kArg2   = 3
kFcode  = 4
kOcode  = 5
kDyn    = 6
kFields = 7

-- Node kind codes (mirror compileTree in Unboxed.hs)
kVar, kParam, kConst, kUni, kBin, kNop :: Int
kVar   = 0
kParam = 1
kConst = 2
kUni   = 3
kBin   = 4
kNop   = 5

-- | Runtime dispatch over Function code (fromEnum), select chain.
evalFunCode :: Exp Int -> Exp Double -> Exp Double
evalFunCode c x = go [Id .. Cube]
  where
    go []       = 0
    go (f : fs) = (c A.== A.constant (fromEnum f)) ? (evalFunAcc f x, go fs)

-- | Runtime dispatch over Op code (fromEnum), select chain.
evalOpCode :: Exp Int -> Exp Double -> Exp Double -> Exp Double
evalOpCode c l r = go [Add .. AQ]
  where
    go []       = 0
    go (o : os) = (c A.== A.constant (fromEnum o)) ? (evalOpAcc o l r, go os)

-- | Runtime dispatch over Function code for the unary derivative.
derivFunCode :: Exp Int -> Exp Double -> Exp Double
derivFunCode c x = go [Id .. Cube]
  where
    go []       = 0
    go (f : fs) = (c A.== A.constant (fromEnum f)) ? (derivativeAcc f x, go fs)

-- | Runtime dispatch over Op code for both binary partials (dx applied).
diffOpCode :: Exp Int -> Exp Double -> Exp Double -> Exp Double -> Exp Double -> Exp (Double, Double)
diffOpCode c dx fx gy fg = go [Add .. AQ]
  where
    go []       = A.lift (A.constant 0, A.constant 0)
    go (o : os) = (c A.== A.constant (fromEnum o)) ? (diffPureAcc o dx fx gy fg, go os)

-- Profiling counters (wall clock)
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

-- | One-time flag so the zero-byte cache sweep runs only once per process.
{-# NOINLINE cacheCleaned #-}
cacheCleaned :: IORef Bool
cacheCleaned = unsafePerformIO (newIORef False)

-- | Multi-worker target spanning all RTS capabilities (respects the -N flag;
-- no setNumCapabilities hijack, unlike the env-var-based defaultTarget which
-- is a CAF initialized before setEnv takes effect).
{-# NOINLINE multiWorker #-}
multiWorker :: CPU.Native
multiWorker = unsafePerformIO $ do
  ncaps <- getNumCapabilities
  CPU.createTarget [0 .. ncaps - 1]

-- | Wrap an offset-0 'VU.Vector' into an Accelerate 'Vector' without copying.
-- The 'Array' newtype constructor and the internal 'R.Array'/'newUniqueArray'
-- constructors are exposed by the accelerate package, so we can share the same
-- ForeignPtr the vector already owns (the ctStatic columns are immutable, so
-- sharing is safe). If the vector has a non-zero offset we fall back to a copy.
mkAccVector :: VU.Vector Double -> Array DIM1 Double
mkAccVector v = Array (R.Array ((), len) (unsafePerformIO (newUniqueArray fp')))
  where
    vs = VS.convert v
    (fp, off, len) = VS.unsafeToForeignPtr vs
    fp' = case off of
            0 -> fp
            _ -> let (f, _, _) = VS.unsafeToForeignPtr (VS.fromList (VS.toList vs)) in f

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
--
-- The static columns (data, precomputed subexpressions, loss wrap inputs) are
-- no longer baked into the LLVM IR as constants. Instead the entire padded
-- ctStatic column block is passed as a single zero-copy array input, and the
-- evaluation is split into chunks of `chunkSize` rows. Each chunk runs the same
-- compiled kernel (base row and chunk length arrive as scalar inputs, so the
-- AST is identical across chunks and the JIT happens exactly once per tree).
-- This removes the ~25MB of per-tree LLVM constants (the dominant compile
-- cost) and keeps the working set of each kernel cache-resident.
compileAccelerateTree :: CompiledTree -> [VU.Vector Double] -> VU.Vector Double -> (VS.Vector Double -> (Double, VS.Vector Double))
compileAccelerateTree ct _xss _ys
    | interpEnabled = compileAccelerateInterp ct _xss _ys
    | otherwise     = compileAccelerateTreeJIT ct _xss _ys

-- | Compiled per-tree kernel. The graph 'buildAccGraph' closes over the tree's
-- structure and 'ctM' (row stride), with the static columns arriving at runtime,
-- so two 'CompiledTree's with the same structure and 'm' compile to the same
-- kernel and can safely share one.
type CompiledKernel = A.Array DIM1 Double -> A.Array DIM1 Double -> A.Scalar Int -> A.Scalar Int -> A.Array DIM1 Double -> (A.Scalar Double, A.Array DIM1 Double)

-- | Bounded process-wide cache from a canonical tree signature to its compiled
-- kernel. Per-tree-structure reuse (not cross-tree sharing, which was the
-- unstable interpreter) avoids repeated LLVM JIT for repeated trees, and the
-- reuse is exactly the same object reuse that the Phase-2 path already relies on.
{-# NOINLINE kernelCache #-}
kernelCache :: IORef (Map.Map String CompiledKernel)
kernelCache = unsafePerformIO (newIORef Map.empty)

{-# NOINLINE kernelCacheLimit #-}
kernelCacheLimit :: Int
kernelCacheLimit = 2048

kernelSig :: CompiledTree -> String
kernelSig ct = show (VU.toList (ctDyn ct), VB.toList (ctNodes ct), ctRoot ct, ctM ct)

-- | Look up a compiled kernel for this tree, compiling and caching it on a miss.
getKernel :: CompiledTree -> CompiledKernel
getKernel ct = unsafePerformIO $ do
    let sig = kernelSig ct
    c <- readIORef kernelCache
    case Map.lookup sig c of
      Just jf -> pure jf
      Nothing -> do
          logTreeStats ct
          ensureCleanCache cacheCleaned
          w0 <- getCurrentTime
          let !jf = CPU.runNWith multiWorker (buildAccGraph ct)
          w1 <- getCurrentTime
          let dt = realToFrac (diffUTCTime w1 w0) :: Double
          debug ("[acc] compile " Prelude.++ show dt Prelude.++ " s")
          modifyIORef' compileTime (Prelude.round (dt * 1e9) +)
          modifyIORef' compileCount (+ 1)
          atomicModifyIORef' kernelCache $ \m ->
              let m' = if Map.size m Prelude.>= kernelCacheLimit
                         then Map.insert sig jf (Map.deleteMin m)
                         else Map.insert sig jf m
              in (m', ())
          pure jf

compileAccelerateTreeJIT :: CompiledTree -> [VU.Vector Double] -> VU.Vector Double -> (VS.Vector Double -> (Double, VS.Vector Double))
compileAccelerateTreeJIT ct _xss _ys =
    let
        m          = ctM ct
        chunkSize  = readChunkSize
        nchunks    = Prelude.max 1 (Prelude.div (m + chunkSize - 1) chunkSize)
        chunkSizes = [ if k Prelude.< nchunks - 1 then chunkSize else m - (nchunks - 1) * chunkSize
                     | k <- [0 .. nchunks - 1] ]
        bases      = Data.List.scanl (+) 0 (Data.List.init chunkSizes)

        staticA    = mkAccVector (ctStatic ct)
        leafA      = mkAccVector (VU.concat (VB.toList (ctVars ct)))

        jittedFunc = getKernel ct

        runChunk :: VS.Vector Double -> Vector Double -> Int -> Int -> IO (Double, VS.Vector Double)
        runChunk theta thetaArr base cs = do
            let baseS = A.fromList Z [base]   :: Scalar Int
                csS   = A.fromList Z [cs]     :: Scalar Int
                (objArr, gradArr) = jittedFunc leafA staticA baseS csS thetaArr
                obj  = A.indexArray objArr Z
                grad = VS.fromList (A.toList gradArr)
            evaluate obj
            evaluate (VS.length grad)
            pure (obj, grad)

    in \theta -> unsafePerformIO $ do
        w0 <- getCurrentTime
        let thetaArr = A.fromList (Z :. VS.length theta) (VS.toList theta)
        results <- Prelude.mapM (Prelude.uncurry (runChunk theta thetaArr)) (Prelude.zip bases chunkSizes)
        let obj  = foldl' (+) 0 (Prelude.fmap Prelude.fst results)
            grads = Prelude.fmap Prelude.snd results
            grad = case grads of
                     []     -> VS.empty
                     g : gs -> foldl' (VS.zipWith (+)) g gs
        evaluate obj
        evaluate (VS.length grad)
        w1 <- getCurrentTime
        let dt = realToFrac (diffUTCTime w1 w0) :: Double
        debug ("[acc] eval " Prelude.++ show dt Prelude.++ " s")
        modifyIORef' evalTime (Prelude.round (dt * 1e9) +)
        modifyIORef' evalCount (+ 1)

        pure (obj, grad)

-- | Chunk size (rows per kernel run), overridable via ACC_CHUNK for sweeps.
-- 25974 (m/4) measured best on data.tsv (103896 rows): 4 chunks keeps the
-- working set cache-resident without per-launch overhead dominating.
{-# NOINLINE readChunkSize #-}
readChunkSize :: Int
readChunkSize = unsafePerformIO $ do
    m <- lookupEnv "ACC_CHUNK"
    case m of
        Just s -> case reads s of
                    [(n, "")] | n Prelude.> 0 -> pure n
                    _                 -> pure 25974
        Nothing -> pure 25974

-- | Print diagnostics to stderr when the ACC_DEBUG environment variable is set.
{-# NOINLINE debug #-}
debug :: String -> IO ()
debug msg = do
  m <- lookupEnv "ACC_DEBUG"
  case m of
    Just _  -> hPutStrLn stderr msg
    Nothing -> pure ()

-- | Per-tree shape statistics: BFS levels from the root, level widths, depth,
-- and the child-count / in-degree histograms. Used to size the fixed-shape
-- interpreter's per-level arrays and to validate the per-parent child-count
-- gather (design E) against real trees.
data TreeStats = TreeStats
  { tsNodes      :: !Int
  , tsDepth      :: !Int
  , tsWidths     :: [Int]
  , tsMaxWidth   :: !Int
  , tsChildHist  :: !(VU.Vector Int)  -- index = #children, value = #nodes
  , tsParentHist :: !(VU.Vector Int)  -- index = #parents, value = #nodes
  }

treeStats :: CompiledTree -> TreeStats
treeStats ct = TreeStats n d ws mw ch ph
  where
    nodes = ctNodes ct
    root  = ctRoot ct
    n     = ctNPred ct
    levels = bfsLevels nodes root
    d     = Prelude.length levels
    ws    = Data.List.map Prelude.length levels
    mw    = Prelude.maximum ws

    -- child count per node (arity), from the node structure
    chVec = VU.fromList (Data.List.map (\k -> Prelude.length (children (nodes VB.! k))) [0 .. n - 1])
    ch    = histogram (Prelude.maximum (VU.toList chVec)) chVec
    -- in-degree per node, from the child relation of the node structure only
    -- (NOT ctArg/ctArg2: for Var leaves ctArg holds the *variable index*, which
    -- collides with the node-id range and would fabricate spurious parents).
    indeg = Prelude.foldl' bump (VU.replicate n (0 :: Int)) edgeList
      where
        edgeList = [ (c, k) | k <- [0 .. n - 1], c <- children (nodes VB.! k) ]
        bump v (c, _) = v VU.// [(c, (v VU.! c) + 1)]
    ph    = histogram (Prelude.maximum (VU.toList indeg)) indeg

    histogram :: Int -> VU.Vector Int -> VU.Vector Int
    histogram maxK xs = VU.create $ do
        v <- VUM.replicate (maxK + 1) 0
        VU.forM_ xs $ \x -> VUM.modify v (+ 1) x
        pure v

    children :: SRTree Int -> [Int]
    children nd = case nd of
        Var _     -> []
        Param _   -> []
        Const _   -> []
        Uni _ t   -> [t]
        Bin _ l r -> [l, r]

-- | BFS levels (each level is the list of node ids in row-major order).
bfsLevels :: VB.Vector (SRTree Int) -> Int -> [[Int]]
bfsLevels nodes root = go [root] ISet.empty
  where
    go [] _     = []
    go cur seen = cur : go next seen'
      where
        next = [ c | k <- cur, c <- childrenOf (nodes VB.! k), ISet.notMember c seen ]
        seen' = Prelude.foldl' (flip ISet.insert) seen next
    childrenOf nd = case nd of
        Var _     -> []
        Param _   -> []
        Const _   -> []
        Uni _ t   -> [t]
        Bin _ l r -> [l, r]

showTreeStats :: TreeStats -> String
showTreeStats (TreeStats n d ws mw ch ph) =
    "nodes=" Prelude.++ show n
    Prelude.++ " lenNodes=" Prelude.++ show n
    Prelude.++ " depth=" Prelude.++ show d
    Prelude.++ " maxwidth=" Prelude.++ show mw
    Prelude.++ " widths=" Prelude.++ show ws
    Prelude.++ " childHist=" Prelude.++ show (VU.toList ch)
    Prelude.++ " parentHist=" Prelude.++ show (VU.toList ph)

-- | Append one line per compiled tree when SRTREE_ACC_STATS is set (value is
-- the log path, or the default /tmp/trees.log when empty / "1"). The steady
-- compile happens once per tree, so this is at most ~a few hundred lines.
logTreeStats :: CompiledTree -> IO ()
logTreeStats ct = do
  m <- lookupEnv "SRTREE_ACC_STATS"
  case m of
    Nothing -> pure ()
    Just v  -> do
      let path = case v of
                   ""  -> "/tmp/trees.log"
                   "1" -> "/tmp/trees.log"
                   _   -> v
      appendFile path (showTreeStats (treeStats ct) Prelude.++ "\n")

-- | Per-tree runtime metadata for the fixed-shape interpreter. All vectors are
-- padded to the fixed shape; overflow slots are NOP (kind kNop, arg 0).
data Encoded = Encoded
  { encMeta   :: !(VU.Vector Int)   -- [(slot * kFields) + field], len maxDepth*maxWidth*kFields
  , encWidth  :: !(VU.Vector Int)   -- [level] actual node count, len maxDepth
  , encParent :: !(VU.Vector Int)   -- [((level*maxWidth+pos)*maxParents)+k] = parentPos*4+slot, -1 if none
  }

-- | Encode a 'CompiledTree' into fixed-shape runtime metadata. Returns 'Nothing'
-- when the tree exceeds the fixed shape (falls back to the Phase-2 JIT).
encodeTree :: CompiledTree -> Maybe Encoded
encodeTree ct
    | d Prelude.> maxDepth Prelude.|| Prelude.any (Prelude.> maxWidth) widths Prelude.|| VU.any (Prelude.> maxParents) indeg = Nothing
    | otherwise = Just Encoded { encMeta = meta, encWidth = widthV, encParent = parentV }
  where
    nodes  = ctNodes ct
    root   = ctRoot ct
    n      = ctNPred ct
    levels = bfsLevels nodes root
    d      = Prelude.length levels
    widths = Data.List.map Prelude.length levels

    -- node id -> (level, position in level)
    posMap :: IntMap.IntMap (Int, Int)
    posMap = IntMap.fromList [ (nodeId, (ℓ, i)) | (ℓ, lvl) <- Prelude.zip [0 ..] levels
                                                , (i, nodeId) <- Prelude.zip [0 ..] lvl ]

    lvlWidth :: Int -> Int
    lvlWidth ℓ = if ℓ Prelude.< d then widths Prelude.!! ℓ else 0
    nodeAt :: Int -> Int -> Int
    nodeAt ℓ i = (levels Prelude.!! ℓ) Prelude.!! i

    kindOf :: Int -> Int -> Int
    kindOf ℓ i = if i Prelude.< lvlWidth ℓ then ctKind ct VU.! nodeAt ℓ i else kNop
    gidOf  ℓ i = if i Prelude.< lvlWidth ℓ then nodeAt ℓ i else 0
    dynOf  ℓ i = if i Prelude.< lvlWidth ℓ then (if ctDyn ct VU.! nodeAt ℓ i then 1 else 0) else 0

    -- arg: Var->var ix, Param->param ix, Const->0, Uni->child pos in level+1,
    -- Bin->left child pos in level+1
    argOf ℓ i
      | i Prelude.>= lvlWidth ℓ = 0
      | otherwise = case ctKind ct VU.! k of
          0 -> ctArg ct VU.! k          -- kVar: variable index
          1 -> ctArg ct VU.! k          -- kParam: param index
          2 -> 0                        -- kConst
          3 -> Prelude.snd (posMap IntMap.! (ctArg ct VU.! k))  -- kUni: child pos
          4 -> Prelude.snd (posMap IntMap.! (ctArg ct VU.! k))  -- kBin: left child pos
          _ -> 0
      where k = nodeAt ℓ i
    arg2Of ℓ i
      | i Prelude.>= lvlWidth ℓ = 0
      | otherwise = case ctKind ct VU.! k of
          4 -> Prelude.snd (posMap IntMap.! (ctArg2 ct VU.! k))  -- kBin: right child pos
          _ -> 0
      where k = nodeAt ℓ i
    fcodeOf ℓ i = if i Prelude.< lvlWidth ℓ Prelude.&& ctKind ct VU.! nodeAt ℓ i Prelude.== kUni
                      then ctFcode ct VU.! nodeAt ℓ i else 0
    ocodeOf ℓ i = if i Prelude.< lvlWidth ℓ Prelude.&& ctKind ct VU.! nodeAt ℓ i Prelude.== kBin
                      then ctOcode ct VU.! nodeAt ℓ i else 0

    meta :: VU.Vector Int
    meta = VU.generate (maxDepth * maxWidth * kFields) $ \ix ->
        let (slot, field) = ix `quotRem` kFields
            (ℓ, i)       = slot `quotRem` maxWidth
        in case field of
             f | f Prelude.== kKind  -> kindOf ℓ i
               | f Prelude.== kGid   -> gidOf ℓ i
               | f Prelude.== kArg   -> argOf ℓ i
               | f Prelude.== kArg2  -> arg2Of ℓ i
               | f Prelude.== kFcode -> fcodeOf ℓ i
               | f Prelude.== kOcode -> ocodeOf ℓ i
               | otherwise           -> dynOf ℓ i

    widthV :: VU.Vector Int
    widthV = VU.fromList (Data.List.map lvlWidth [0 .. maxDepth - 1])

    -- in-degree per node (number of parents), used for the overflow check.
    indeg :: VU.Vector Int
    indeg = Prelude.foldl' bump (VU.replicate n (0 :: Int)) edgeList
      where
        edgeList = [ (c, k) | k <- [0 .. n - 1], c <- childrenIds (nodes VB.! k) ]
        bump v (c, _) = v VU.// [(c, (v VU.! c) + 1)]
    childrenIds :: SRTree Int -> [Int]
    childrenIds nd = case nd of
        Uni _ t   -> [t]
        Bin _ l r -> [l, r]
        _         -> []

    -- per-child parent list: [(parentPos, slotCode)] with slotCode
    -- 0 = Uni child, 1 = Bin left, 2 = Bin right.
    parentList :: Int -> [(Int, Int)]
    parentList c =
        [ (Prelude.snd (posMap IntMap.! p), slot)
        | p <- [0 .. n - 1]
        , (slot) <- childSlots (nodes VB.! p) c ]
      where
        childSlots :: SRTree Int -> Int -> [Int]
        childSlots nd ch = case nd of
            Uni _ t   -> [0 | t Prelude.== ch]
            Bin _ l r -> [1 | l Prelude.== ch] Prelude.++ [2 | r Prelude.== ch]
            _         -> []

    parentV :: VU.Vector Int
    parentV = VU.generate (maxDepth * maxWidth * maxParents) $ \ix ->
        let (slot, k) = ix `quotRem` maxParents
            (ℓ, i)   = slot `quotRem` maxWidth
        in if i Prelude.< lvlWidth ℓ
             then case Data.List.drop k (parentList (nodeAt ℓ i)) of
                    (p, s) : _ -> p * 4 + s
                    []         -> -1
             else -1


-- | Builds the AST in the Accelerate EDSL. The static column block is a kernel
-- input (not baked constants), and the row range comes in as scalar inputs, so
-- the same compiled kernel can be run over any contiguous chunk of rows.
-- `leafVals` is the flat concatenation of the run-fixed leaf columns
-- (ctVars = xss ++ [y, yErr]); a static Var leaf reads its value there instead
-- of from `staticIn` (its slot is no longer materialized).
buildAccGraph :: CompiledTree
              -> Acc (Vector Double)   -- leaf columns, flat [colIdx * m + row]
              -> Acc (Vector Double)   -- static columns, compact [slot * m + row]
              -> Acc (Scalar Int)       -- first row of this chunk
              -> Acc (Scalar Int)       -- number of rows in this chunk
              -> Acc (Vector Double)    -- theta
              -> Acc (Scalar Double, Vector Double)
buildAccGraph ct leafVals staticIn baseIn csIn theta = A.lift (obj, gradPacked)
  where
    root  = ctRoot ct
    nodes = ctNodes ct
    dyn   = ctDyn ct

    base :: Exp Int
    base = A.the baseIn
    cs   :: Exp Int
    cs   = A.the csIn

    csShape :: Exp (Z :. Int)
    csShape = A.lift (Z :. cs)

    -- column for a static node key: rows [base, base + cs). Var leaves read
    -- from the flat leafVals at (leaf column)*m; everything else from
    -- staticIn at ctStaticBase.
    statCol :: Int -> Acc (Vector Double)
    statCol k = if VU.unsafeIndex (ctKind ct) k Prelude.== 0
                  then A.generate csShape (\ix -> leafVals A.!! (A.constant (leafBaseOf k) + base + A.indexHead ix))
                  else A.generate csShape (\ix -> staticIn A.!! (A.constant (ctStaticBase ct VU.! k) + base + A.indexHead ix))
      where
        leafBaseOf k = leafSrcIdx (VB.length (ctVars ct) - 2) (VU.unsafeIndex (ctArg ct) k) * ctM ct

    -- 1. FORWARD PASS
    forward :: IntMap.IntMap (Acc (Array DIM1 Double))
    forward = foldl' step IntMap.empty [0 .. root]
      where
        step acc key
              | Prelude.not (dyn VU.! key) = IntMap.insert key (statCol key) acc
              | otherwise = IntMap.insert key (evalNode key acc) acc

        evalNode key acc = case nodes VB.! key of
            Param ix   -> A.fill csShape (theta A.!! A.constant ix)
            Uni f t    -> A.map (evalFunAcc f) (acc IntMap.! t)
            Bin op l r -> A.zipWith (evalOpAcc op) (acc IntMap.! l) (acc IntMap.! r)
            Var _      -> Prelude.error "buildAccGraph: Var node is static (unreachable)"
            Const _    -> Prelude.error "buildAccGraph: Const node is static (unreachable)"

    -- 2. BACKWARD PASS (Adjoints)
    initAdjoints = IntMap.singleton root (A.fill csShape 1.0)

    adjoints :: IntMap.IntMap (Acc (Array DIM1 Double))
    adjoints = foldl' bwdStep initAdjoints [root, root - 1 .. 0]
      where
        bwdStep adj key
          | Prelude.not (dyn VU.! key) = adj
          | otherwise = case nodes VB.! key of
              Bin op l r ->
                  let v  = IntMap.findWithDefault (A.fill csShape 0.0) key adj
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
                  let v  = IntMap.findWithDefault (A.fill csShape 0.0) key adj
                      x  = forward IntMap.! t
                      dt = A.zipWith (*) v (A.map (derivativeAcc f) x)
                  in IntMap.insertWith (A.zipWith (+)) t dt adj

              _ -> adj

    -- 3. EXTRACTION

    -- Total objective is the sum of the root node's forward array
    obj = A.sum (forward IntMap.! root)

    -- Pre-calculate the scalar gradient for every Param node.
    paramAdjoints :: [(Int, Exp Double)]
    paramAdjoints = [ (ix, A.the (A.sum (IntMap.findWithDefault (A.fill csShape 0.0) k adjoints)))
                    | (k, Param ix) <- Prelude.zip [0..] (VB.toList nodes) ]

    -- Generate a gradient array that EXACTLY matches the shape of the input theta.
    gradPacked = A.generate (A.shape theta) $ \(I1 i) ->
        foldr (\(ix, val) acc -> i A.== A.constant ix ? (acc + val, acc)) 0.0 paramAdjoints

-- Helper tuple extractors for zip4
fst4 (T4 a _ _ _) = a
snd4 (T4 _ b _ _) = b
thd4 (T4 _ _ c _) = c
fth4 (T4 _ _ _ d) = d

-- ----------------------------------------------------------------------------
-- Fixed-shape interpreter kernel (design E). The AST depends only on the shape
-- constants, NOT on the tree: every tree arrives as runtime inputs (staticIn /
-- metaF / widthF / parentF), so the kernel compiles exactly once per process
-- and every tree runs the same native executable.
-- ----------------------------------------------------------------------------
buildAccInterpGraph
  :: Acc (Vector Double)   -- staticIn: ctStatic compact [slot * m + row]
  -> Acc (Vector Int)      -- staticBaseF: gid -> slot * m
  -> Acc (Vector Double)   -- leafVals: flat leaf columns [colIdx * m + row]
  -> Acc (Vector Int)      -- leafBaseF: gid -> leaf column * m, or -1 if not a Var leaf
  -> Acc (Scalar Int)      -- base: first row of this chunk
  -> Acc (Scalar Int)      -- cs: rows in this chunk
  -> Acc (Vector Double)   -- theta
  -> Acc (Vector Int)      -- metaF: per-slot node metadata
  -> Acc (Vector Int)      -- widthF: per-level actual node count
  -> Acc (Vector Int)      -- parentF: per-slot parent list (pos*4+slot, -1 none)
  -> Acc (Scalar Double, Vector Double)
buildAccInterpGraph staticIn staticBaseF leafVals leafBaseF baseIn csIn theta metaF widthF parentF = A.lift (obj, gradPacked)
  where
    base = A.the baseIn
    cs   = A.the csIn

    -- width of a level (runtime)
    wAt :: Int -> Exp Int
    wAt ℓ = widthF A.!! A.constant ℓ

    -- static value of a node with global id gid, for chunk row
    staticVal :: Exp Int -> Exp Int -> Exp Double
    staticVal gid row =
        let lb = leafBaseF A.!! gid
        in (lb A.>= A.constant 0)
             ? (leafVals A.!! (lb + base + row)
               , staticIn A.!! (staticBaseF A.!! gid + base + row))

    -- read a metadata field for a slot
    metaAt :: Exp Int -> Int -> Exp Int
    metaAt slot field = metaF A.!! (slot*7 + A.constant field)

    -- 1. FORWARD PASS (leaves upward): fwdVals !! ℓ is level ℓ; level ℓ reads
    -- its children from level ℓ+1 (they are one BFS level below by definition).
    fwdVals :: [Acc (Matrix Double)]
    fwdVals = Data.List.map fwdLevel [0 .. maxDepth]
      where
        fwdLevel ℓ
          | ℓ Prelude.== maxDepth = A.fill (A.lift (Z :. A.constant 0 :. cs)) (A.constant 0)
          | otherwise             = buildFwd ℓ (fwdVals Prelude.!! (ℓ+1))

        buildFwd :: Int -> Acc (Matrix Double) -> Acc (Matrix Double)
        buildFwd ℓ fwdNext =
            A.generate (A.lift (Z :. wAt ℓ :. cs)) $ \(I2 i row) ->
              let slot = A.constant (ℓ*maxWidth) + i
                  kind  = metaAt slot kKind
                  gid   = metaAt slot kGid
                  arg   = metaAt slot kArg
                  arg2  = metaAt slot kArg2
                  fcode = metaAt slot kFcode
                  ocode = metaAt slot kOcode
                  dyn   = metaAt slot kDyn A.== A.constant 1

                  -- gather a child value from level ℓ+1 (runtime position pos)
                  childVal :: Exp Int -> Exp Double
                  childVal pos =
                      let cslot = A.constant ((ℓ+1)*maxWidth) + pos
                          cDyn  = metaF A.!! (cslot*7 + A.constant kDyn) A.== A.constant 1
                          cGid  = metaF A.!! (cslot*7 + A.constant kGid)
                          dynVal  = fwdNext A.!! (pos*cs + row)
                          statVal = staticVal cGid row
                      in cDyn ? (dynVal, statVal)

                  paramVal = theta A.!! arg
                  uniVal   = evalFunCode fcode (childVal arg)
                  binVal   = evalOpCode ocode (childVal arg) (childVal arg2)
                  dynamicVal = (kind A.== A.constant kParam) ? (paramVal,
                               (kind A.== A.constant kUni) ? (uniVal,
                               (kind A.== A.constant kBin) ? (binVal, 0)))
              in dyn ? (dynamicVal, staticVal gid row)

    -- 2. BACKWARD PASS (root downward): adjVals !! ℓ is the adjoint of level ℓ.
    adjVals :: [Acc (Matrix Double)]
    adjVals = Data.List.map adjLevel [0 .. maxDepth - 1]
      where
        adjLevel 0 = A.fill (A.lift (Z :. wAt 0 :. cs)) (A.constant 1)
        adjLevel ℓ = buildAdj ℓ (adjVals Prelude.!! (ℓ-1))

        buildAdj :: Int -> Acc (Matrix Double) -> Acc (Matrix Double)
        buildAdj ℓ adjPrev =
            A.generate (A.lift (Z :. wAt ℓ :. cs)) $ \(I2 i row) ->
              let slot = A.constant (ℓ*maxWidth) + i
                  c0 = parentF A.!! (slot*4 + A.constant 0)
                  c1 = parentF A.!! (slot*4 + A.constant 1)
                  c2 = parentF A.!! (slot*4 + A.constant 2)
                  c3 = parentF A.!! (slot*4 + A.constant 3)

                  contrib :: Exp Int -> Exp Double
                  contrib c = (c A.>= A.constant 0) ? ( (adjPrev A.!! (cpos*cs + row)) * partial, 0)
                    where
                      cpos  = c `A.quot` A.constant 4
                      cslot = c `A.rem` A.constant 4
                      partial = partialCode cpos cslot

                  partialCode :: Exp Int -> Exp Int -> Exp Double
                  partialCode ppos slot =
                      let pbase = A.constant ((ℓ-1)*maxWidth) + ppos
                          pKind  = metaF A.!! (pbase*7 + A.constant kKind)
                          pFcode = metaF A.!! (pbase*7 + A.constant kFcode)
                          pOcode = metaF A.!! (pbase*7 + A.constant kOcode)
                          pArg   = metaF A.!! (pbase*7 + A.constant kArg)
                          pArg2  = metaF A.!! (pbase*7 + A.constant kArg2)
                          fwdSelf = (fwdVals Prelude.!! ℓ) A.!! (i*cs + row)
                          fwdL    = (fwdVals Prelude.!! ℓ) A.!! (pArg*cs + row)
                          fwdR    = (fwdVals Prelude.!! ℓ) A.!! (pArg2*cs + row)
                          fwdP    = (fwdVals Prelude.!! (ℓ-1)) A.!! (ppos*cs + row)
                          t12     = diffOpCode pOcode (A.constant 1) fwdL fwdR fwdP
                          dl      = A.fst t12
                          dr      = A.snd t12
                          uniP = (pKind A.== A.constant kUni) ? (derivFunCode pFcode fwdSelf, 0)
                          binP = (pKind A.== A.constant kBin) ? ((slot A.== A.constant 1) ? (dl, dr), 0)
                      in uniP + binP

              in (contrib c0) + (contrib c1) + (contrib c2) + (contrib c3)

    -- 3. EXTRACTION
    -- per-level per-node forward row sums (fold innermost / row dimension)
    fwdSums :: [Acc (Vector Double)]
    fwdSums = Data.List.map (\fwdL -> A.fold (+) (A.constant 0) fwdL) fwdVals
    -- objective = total sum of root's forward values
    obj = A.sum (fwdSums Prelude.!! 0)

    -- per-level per-node adjoint row sums (fold innermost / row dimension)
    nodeSums :: [Acc (Vector Double)]
    nodeSums = Data.List.map (\adjL -> A.fold (+) (A.constant 0) adjL) adjVals
    -- scalar sum of adjoints of a given (level, pos) node
    slotSum :: Int -> Int -> Exp Double
    slotSum ℓ i = (A.constant i A.< wAt ℓ) ? ((nodeSums Prelude.!! ℓ) A.!! A.constant i, 0)

    gradPacked = A.generate (A.shape theta) $ \(I1 ix) ->
        foldr (step ix) (A.constant 0) [ (ℓ, i) | ℓ <- [0 .. maxDepth - 1], i <- [0 .. maxWidth - 1] ]
      where
        step ix (ℓ, i) acc =
            let slot = A.constant (ℓ*maxWidth + i)
                kind = metaF A.!! (slot*7 + A.constant kKind)
                arg  = metaF A.!! (slot*7 + A.constant kArg)
                isParam = (kind A.== A.constant kParam) A.&& (arg A.== ix)
            in isParam ? (acc + slotSum ℓ i, acc)

-- | The interpreter kernel compiled once per process (tree-independent AST).
{-# NOINLINE interpKernel #-}
interpKernel
  :: Vector Double -> Vector Int -> Vector Double -> Vector Int
  -> Scalar Int -> Scalar Int
  -> Vector Double -> Vector Int -> Vector Int -> Vector Int
  -> (Scalar Double, Vector Double)
interpKernel = unsafePerformIO $ do
    ensureCleanCache cacheCleaned
    w0 <- getCurrentTime
    let !jf = CPU.runNWith multiWorker buildAccInterpGraph
    w1 <- getCurrentTime
    let dt = realToFrac (diffUTCTime w1 w0) :: Double
    debug ("[acc-interp] compile " Prelude.++ show dt Prelude.++ " s")
    modifyIORef' compileTime (Prelude.round (dt * 1e9) +)
    modifyIORef' compileCount (+ 1)
    pure jf

-- | One-time gate for the interpreter backend (ACC_INTERP=1); cached per process.
{-# NOINLINE interpEnabled #-}
interpEnabled :: Bool
interpEnabled = unsafePerformIO (do m <- lookupEnv "ACC_INTERP"; pure (m Prelude.== Just "1"))

-- | Build a fixed-length 'Array DIM1 Int' from an unboxed Int vector (copies).
mkAccIVector :: VU.Vector Int -> Vector Int
mkAccIVector v = A.fromList (Z :. VU.length v) (VU.toList v)

-- | Map a Var leaf's arg (feature ix, or -1 = y, -2 = yErr) to an index into
-- ctVars = xss ++ [y, yErr].
leafSrcIdx :: Int -> Int -> Int
leafSrcIdx nFeats a | a Prelude.>= 0   = a
                    | a Prelude.== -1  = nFeats
                    | otherwise = nFeats + 1
{-# INLINE leafSrcIdx #-}

-- | Per-gid flat base into ctVars for a Var leaf (leaf column * m), or -1 for
-- any other node (which reads from ctStatic instead).
leafBases :: CompiledTree -> VU.Vector Int
leafBases ct =
    let nFeats = VB.length (ctVars ct) - 2
        kind   = ctKind ct
        arg    = ctArg ct
        m      = ctM ct
    in VU.generate (ctRoot ct + 1) $ \k ->
        if VU.unsafeIndex kind k Prelude.== 0
          then leafSrcIdx nFeats (VU.unsafeIndex arg k) * m
          else -1

-- | Interpreter entry point: encodes the tree, then runs every chunk through
-- the single compiled kernel. Falls back to the Phase-2 JIT if the tree
-- exceeds the fixed shape (e.g. an unusually deep/wide tree).
compileAccelerateInterp :: CompiledTree -> [VU.Vector Double] -> VU.Vector Double -> (VS.Vector Double -> (Double, VS.Vector Double))
compileAccelerateInterp ct _xss _ys =
    case encodeTree ct of
      Nothing -> compileAccelerateTree ct _xss _ys
      Just enc ->
        let m         = ctM ct
            chunkSize = readChunkSize
            nchunks   = Prelude.max 1 (Prelude.div (m + chunkSize - 1) chunkSize)
            chunkSizes = [ if k Prelude.< nchunks - 1 then chunkSize else m - (nchunks - 1) * chunkSize
                         | k <- [0 .. nchunks - 1] ]
            bases     = Data.List.scanl (+) 0 (Data.List.init chunkSizes)

            staticA = mkAccVector (ctStatic ct)
            staticBaseF = mkAccIVector (ctStaticBase ct)
            leafA   = mkAccVector (VU.concat (VB.toList (ctVars ct)))
            leafBaseF = mkAccIVector (leafBases ct)
            metaF   = mkAccIVector (encMeta enc)
            widthF  = mkAccIVector (encWidth enc)
            parentF = mkAccIVector (encParent enc)

            runChunk :: VS.Vector Double -> Vector Double -> Int -> Int -> IO (Double, VS.Vector Double)
            runChunk _theta thetaArr base cs = do
                let baseS = A.fromList Z [base] :: Scalar Int
                    csS   = A.fromList Z [cs]   :: Scalar Int
                wK0 <- getCurrentTime
                let (objArr, gradArr) = interpKernel staticA staticBaseF leafA leafBaseF baseS csS thetaArr metaF widthF parentF
                    obj  = A.indexArray objArr Z
                evaluate obj
                wK1 <- getCurrentTime
                let kt = realToFrac (diffUTCTime wK1 wK0) :: Double
                wG0 <- getCurrentTime
                let grad = VS.fromList (A.toList gradArr)
                evaluate (VS.length grad)
                wG1 <- getCurrentTime
                let gt = realToFrac (diffUTCTime wG1 wG0) :: Double
                debug ("[acc-interp] chunk base=" Prelude.++ show base Prelude.++ " cs=" Prelude.++ show cs
                       Prelude.++ " kernel=" Prelude.++ show kt Prelude.++ " s grad=" Prelude.++ show gt Prelude.++ " s")
                pure (obj, grad)

        in \theta -> unsafePerformIO $ do
            w0 <- getCurrentTime
            wT0 <- getCurrentTime
            let thetaArr = A.fromList (Z :. VS.length theta) (VS.toList theta)
            wT1 <- getCurrentTime
            let tht = realToFrac (diffUTCTime wT1 wT0) :: Double
            debug ("[acc-interp] thetaMarsh " Prelude.++ show tht Prelude.++ " s (n=" Prelude.++ show (VS.length theta) Prelude.++ ")")
            results <- Prelude.mapM (Prelude.uncurry (runChunk theta thetaArr)) (Prelude.zip bases chunkSizes)
            let obj  = foldl' (+) 0 (Prelude.fmap Prelude.fst results)
                grads = Prelude.fmap Prelude.snd results
                grad = case grads of
                         []     -> VS.empty
                         g : gs -> foldl' (VS.zipWith (+)) g gs
            evaluate obj
            evaluate (VS.length grad)
            w1 <- getCurrentTime
            let dt = realToFrac (diffUTCTime w1 w0) :: Double
            debug ("[acc-interp] eval " Prelude.++ show dt Prelude.++ " s")
            modifyIORef' evalTime (Prelude.round (dt * 1e9) +)
            modifyIORef' evalCount (+ 1)
            pure (obj, grad)
