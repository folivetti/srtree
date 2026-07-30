{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
{-# language FlexibleContexts #-}
{-# language BangPatterns #-}
{-# language TypeApplications #-}
{-# language MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.AD 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Automatic Differentiation for Expression trees
--
-----------------------------------------------------------------------------

module Algorithm.SRTree.AD.Unboxed
         ( compileTree
         , compileTreeMulti
         , evalGradMulti
         , evalGrad
         , CompiledTree(..)
         ) where

import Control.Monad (forM_, foldM, when, unless)
import Control.Monad.ST
import Data.STRef (newSTRef, readSTRef, modifySTRef')
import Data.Bifunctor (bimap, first, second)
import Data.SRTree.Derivative ( derivative )
import Data.SRTree.Eval
    ( Target, Theta, Columns, evalFun, evalOp, replicateAs )
import Data.SRTree.Internal
import Data.SRTree.Print (showExpr)
import Data.SRTree.Recursion ( cataM, cata, accu )
import qualified Data.Vector.Storable as V
import qualified Data.Vector.Storable.Mutable as VM
import qualified Data.Vector.Unboxed          as VU
import qualified Data.Vector.Unboxed.Mutable  as VUM
import qualified Data.Vector as VB
import qualified Data.Vector.Mutable as VMB
import Debug.Trace (trace, traceShow)
import qualified Data.IntMap.Strict as IntMap
import Data.List ( foldl', foldl1' )
import Data.Maybe ( fromJust, isJust, fromMaybe )

import Control.Monad.State.Strict
import Control.Monad.Identity


import Data.List (transpose)
import System.IO.Unsafe (unsafePerformIO)
import Control.Concurrent (getNumCapabilities)
import Control.Concurrent.Async (forConcurrently)
import Control.Exception (evaluate)

import qualified Data.Map.Strict as Map
import Algorithm.SRTree.AD.CompiledAD

compileTree :: [VU.Vector Double] -> VU.Vector Double -> Maybe (VU.Vector Double) -> Fix SRTree -> CompiledTree
compileTree xss ys mYErr tree =
    CompiledTree { ctNodes = nodes, ctRoot = root, ctDyn = dynArr, ctStatic = staticArr, ctM = m, ctNPred = root + 1 }
  where
    yErr = fromJust mYErr
    m    = VU.length ys

    -- state: (structural CSE map, id -> node, id -> isDynamic, id -> static value, counter)
    (_, int2key, dynMap, static, (subtract 1) -> root) =
        cataM leftToRight alg tree
          `execState` (Map.empty, IntMap.empty, IntMap.empty, IntMap.empty, 0)

    nodes     = VB.fromList (IntMap.elems int2key)
    dynArr    = VU.fromList (IntMap.elems dynMap)
    -- flat [node * m + row]; built with one memcpy per static node instead
    -- of stride*m individual quotRem + IntMap lookups.
    stride    = root + 1
    staticArr = VU.create $ do
        arr <- VUM.replicate (stride * m) 0
        forM_ (IntMap.toList static) $ \(key, vec) ->
            VU.copy (VUM.slice (key * m) m arr) vec
        pure arr

    leftToRight (Uni f mt)    = Uni f <$> mt
    leftToRight (Bin f ml mr) = Bin f <$> ml <*> mr
    leftToRight (Var ix)      = pure (Var ix)
    leftToRight (Param ix)    = pure (Param ix)
    leftToRight (Const c)     = pure (Const c)

    alg = insertKey

    graph      (a, _, _, _, _) = a
    getKeyS  k (a, _, _, _, _) = a Map.! k
    isDynSt  k (_, _, d, _, _) = d IntMap.! k
    getStat  k (_, _, _, s, _) = s IntMap.! k

    insEntry key isD mv (a, b, d, s, c) =
        ( Map.insert key c a
        , IntMap.insert c key b
        , IntMap.insert c isD d
        , maybe s (\v -> IntMap.insert c v s) mv
        , c + 1 )

    -- a node depends on theta iff it IS a Param, or any child does
    nodeIsDynamic (Param _)   = pure True
    nodeIsDynamic (Var _)     = pure False
    nodeIsDynamic (Const _)   = pure False
    nodeIsDynamic (Uni _ t)   = gets (isDynSt t)
    nodeIsDynamic (Bin _ l r) = (||) <$> gets (isDynSt l) <*> gets (isDynSt r)

    -- only ever called on nodes already known to be non-dynamic,
    -- so children's static values are guaranteed present
    evalStatic (Var ix)
      | ix == -1  = pure ys
      | ix == -2  = pure yErr
      | otherwise = pure (xss !! ix)
    evalStatic (Const v)    = pure (VU.replicate m v)
    evalStatic (Uni f t)    = VU.map (evalFun f) <$> gets (getStat t)
    evalStatic (Bin op l r) = VU.zipWith (evalOp op) <$> gets (getStat l) <*> gets (getStat r)
    evalStatic (Param _)    = error "compileTree: evalStatic called on a Param node (unreachable)"

    insertKey key = do
        isCached <- gets ((key `Map.member`) . graph)
        if isCached
          then gets (getKeyS key)
          else do
            d  <- nodeIsDynamic key
            mv <- if d then pure Nothing else Just <$> evalStatic key
            modify' (insEntry key d mv)
            gets (getKeyS key)

-- ---------------------------------------------------------------------
-- Per-theta evaluation: the hot path, called once per NLopt objective/
-- gradient call. Forward pass only recomputes dynamic nodes (ids are
-- already topologically ordered, so a single left-to-right fold works).
-- Backward pass is the same recursive shape as the original calcGrad,
-- except it stops immediately on any non-dynamic node -- that subtree
-- has no Param in it, so it can never contribute to the gradient.
-- ---------------------------------------------------------------------

-- Row-fused evaluation: instead of storing one full length-m array per
-- node (which meant ~2 * #nodes large allocations per objective/gradient
-- call), we walk the m data rows one at a time and, for each row, run the
-- forward pass and the reverse-mode backward pass over small per-node
-- scratch arrays of Double (length root+1). This mirrors what the fused
-- Accelerate/LLVM kernel does (one pass per row, no big intermediate
-- arrays) while staying in plain ST: allocation drops from O(nodes * m)
-- to O(nodes + params), and the tight inner loops are all unboxed.
evalGrad :: CompiledTree -> V.Vector Double -> (Double, V.Vector Double)
evalGrad ct theta = runST $ do
    fwd   <- VUM.new (root + 1)   -- node id -> forward value, current row
    adj   <- VUM.new (root + 1)   -- node id -> adjoint (dL/dnode), current row
    gradM <- VUM.replicate p 0    -- accumulated per-parameter gradient
    objRef <- newSTRef 0

    let -- forward pass for a single row: fills `fwd` for ids 0..root
        forwardLoop !row !key
          | key > root = pure ()
          | otherwise  = do
              v <- if not (VU.unsafeIndex dyn key)
                     then pure (VU.unsafeIndex static (key * stride + row))
                     else case VB.unsafeIndex nodes key of
                            Param ix   -> pure (V.unsafeIndex theta ix)
                            Uni f t    -> evalFun f <$> VUM.unsafeRead fwd t
                            Bin op l r -> evalOp op <$> VUM.unsafeRead fwd l <*> VUM.unsafeRead fwd r
                            _          -> error "evalGrad: unreachable"
              VUM.unsafeWrite fwd key v
              forwardLoop row (key + 1)

        -- backward pass for a single row: ids are visited from root down
        -- to 0, which is a valid reverse-topological order since every
        -- child id is smaller than its parent's id by construction.
        backwardLoop !key
          | key < 0 = pure ()
          | otherwise = do
              when (VU.unsafeIndex dyn key) $ do
                v <- VUM.unsafeRead adj key
                case VB.unsafeIndex nodes key of
                  Bin op l r -> do
                    xl <- VUM.unsafeRead fwd l
                    xr <- VUM.unsafeRead fwd r
                    fg <- VUM.unsafeRead fwd key
                    let (dl, dr) = diffScalar op v xl xr fg
                    VUM.unsafeModify adj (+ dl) l
                    VUM.unsafeModify adj (+ dr) r
                  Uni f t -> do
                    x <- VUM.unsafeRead fwd t
                    VUM.unsafeModify adj (+ v * derivative f x) t
                  Param ix -> VUM.unsafeModify gradM (+ v) ix
                  _        -> pure ()
              backwardLoop (key - 1)

        rowLoop !row
          | row >= m = pure ()
          | otherwise = do
              forwardLoop row 0
              rootVal <- VUM.unsafeRead fwd root
              modifySTRef' objRef (+ rootVal)
              when (VU.unsafeIndex dyn root) $ do
                VUM.set adj 0
                VUM.unsafeWrite adj root 1
                backwardLoop root
              rowLoop (row + 1)

    rowLoop 0

    obj        <- readSTRef objRef
    gradFrozen <- VU.unsafeFreeze gradM
    pure (obj, V.convert gradFrozen)
  where
    root   = ctRoot ct
    m      = ctM ct
    p      = V.length theta
    nodes  = ctNodes ct
    dyn    = ctDyn ct
    static = ctStatic ct
    stride = ctNPred ct

-- Pure local-derivative rules, scalar version (same math as the original
-- vectorized `diffPure`, applied per-row in the fused loop above).
diffScalar :: Op -> Double -> Double -> Double -> Double -> (Double, Double)
diffScalar Add dx _  _  _  = (dx, dx)
diffScalar Sub dx _  _  _  = (dx, negate dx)
diffScalar Mul dx fx gy _  = (dx * gy, dx * fx)
diffScalar Div dx _  gy fg = (dx / gy, dx * (negate fg / gy))
diffScalar Power dx fx gy fg =
    ( fixNaN (dx * gy * fg / fx)
    , fixNaN (dx * fg * log fx) )
diffScalar PowerAbs dx fx gy fg =
    let v2 = abs fx
    in ( fixNaN (dx * (fx * gy) * fg / (v2 * v2))
       , fixNaN (dx * fg * log (abs fx)) )
diffScalar AQ dx fx gy _ =
    let dxl = dx * (recip . sqrt . (+1) . (^(2::Int))) gy
        dxy = fx * gy * dxl ^ (3::Int)
    in (dxl, dxy)
{-# INLINE diffScalar #-}

fixNaN :: Double -> Double
fixNaN x = if isNaN x then 0 else x
{-# INLINE fixNaN #-}

-- ---------------------------------------------------------------------
-- Drop-in-compatible wrapper -- same signature as your original function.
-- Use this ONLY to verify correctness against your existing implementation
-- (e.g. QuickCheck / golden tests comparing outputs). It gets you ZERO
-- speedup on its own, since it calls compileTree fresh every time, same
-- as before. The actual win requires changing the NLopt-facing call site.
-- ---------------------------------------------------------------------

--reverseModeGraphO :: [V.Vector Double] -> V.Vector Double -> Maybe (V.Vector Double) -> V.Vector Double -> Fix SRTree -> (V.Vector Double, V.Vector Double)
--reverseModeGraphO xss ys mYErr theta tree = evalGrad (compileTree xss ys mYErr tree) theta

-- | Safely chunk an unboxed vector into 'n' roughly equal parts.
chunkVector :: Int -> VU.Vector Double -> [VU.Vector Double]
chunkVector numChunks v
  | VU.null v = []
  | otherwise =
      let n = VU.length v
          chunkSize = max 1 (n `div` numChunks)
          go vec | VU.null vec = []
                 | VU.length vec <= chunkSize = [vec]
                 | otherwise = let (h, t) = VU.splitAt chunkSize vec
                               in h : go t
      in go v

-- | Compiles the tree for multiple data chunks independently.
compileTreeMulti :: [VU.Vector Double]
                 -> VU.Vector Double
                 -> Maybe (VU.Vector Double)
                 -> Fix SRTree
                 -> [CompiledTree]
compileTreeMulti xss ys mYErr tree =
    let nRows     = VU.length ys
        minChunkSize = 2000
        numChunks = max 1 (min numCapabilities (nRows `div` minChunkSize))
        numCapabilities = unsafePerformIO getNumCapabilities
        ysChunks  = chunkVector numChunks ys
        -- transpose groups the chunks by slice rather than by feature
        xssChunks = Data.List.transpose (map (chunkVector numChunks) xss)
        errChunks = case mYErr of
                      Just e  -> map Just (chunkVector numChunks e)
                      Nothing -> replicate (length ysChunks) Nothing
    in [ compileTree xs y err tree | (xs, y, err) <- zip3 xssChunks ysChunks errChunks ]

-- | Evaluates the gradient across all compiled chunks in parallel.
evalGradMulti :: [CompiledTree] -> V.Vector Double -> (Double, V.Vector Double)
evalGradMulti [ct] theta = evalGrad ct theta
evalGradMulti cts theta = unsafePerformIO $ do
    results <- forConcurrently cts $ \ct -> evaluate (evalGrad ct theta)
    let totalObj   = sum $ map fst results
        totalGrad  = foldl1' (V.zipWith (+)) (map snd results)
    pure (totalObj, totalGrad)
