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
         , evalGradVec
         , evalLossVec
         , CompiledTree(..)
         , setMTPopParallel
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
import Data.IORef (IORef, newIORef, writeIORef, readIORef)

import qualified Data.Map.Strict as Map
import Algorithm.SRTree.AD.CompiledAD

compileTree :: [VU.Vector Double] -> VU.Vector Double -> Maybe (VU.Vector Double) -> Fix SRTree -> CompiledTree
compileTree xss ys mYErr tree =
    CompiledTree { ctNodes = nodes, ctRoot = root, ctDyn = dynArr, ctStatic = staticArr, ctM = m, ctNPred = root + 1
                 , ctKind = kindArr, ctArg = argArr, ctArg2 = arg2Arr, ctFcode = fcodeArr, ctOcode = ocodeArr }
  where
    yErr = fromJust mYErr
    m    = VU.length ys

    -- Rewrite x ** 2.0 into the unary Square kernel (x*x, fcode 17):
    -- the loss wrap ((tree - y) ** 2) / m is the single hottest subgraph in
    -- every NLopt call, and replacing the per-element pow with a multiply
    -- avoids the slow ** (x**2.0 == x*x exactly, and the derivative 2x
    -- matches), so no numerical semantics change.
    tree' = rewritePowSq tree

    -- state: (structural CSE map, id -> node, id -> isDynamic, id -> static value, counter)
    (_, int2key, dynMap, static, (subtract 1) -> root) =
        cataM leftToRight alg tree'
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

    -- compact unboxed per-id code arrays (length root+1) so the hot row loop
    -- never touches the boxed `nodes` vector nor dispatches through the
    -- function-returning evalOp/evalFun
    kindArr  = VU.generate (root + 1) $ \k -> case int2key IntMap.! k of
        Var _     -> 0
        Param _   -> 1
        Const _   -> 2
        Uni _ _   -> 3
        Bin _ _ _ -> 4
    argArr   = VU.generate (root + 1) $ \k -> case int2key IntMap.! k of
        Var ix    -> ix
        Param ix  -> ix
        Uni _ t   -> t
        Bin _ l _ -> l
        Const _   -> 0
    arg2Arr  = VU.generate (root + 1) $ \k -> case int2key IntMap.! k of
        Bin _ _ r -> r
        _         -> 0
    fcodeArr = VU.generate (root + 1) $ \k -> case int2key IntMap.! k of
        Uni f _   -> fromEnum f
        _         -> 0
    ocodeArr = VU.generate (root + 1) $ \k -> case int2key IntMap.! k of
        Bin op _ _ -> fromEnum op
        _          -> 0

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

-- Rewrite (a) Bin Power t (Const 2.0) into the unary Square kernel and
-- (b) Bin Div t (Const c) into Bin Mul t (Const (1/c)). Both are exact at
-- the Double level (x ** 2.0 == x * x; x / c == x * (1/c) up to one ulp)
-- and replace the slow per-element pow()/div with a multiply. The loss
-- wrap ((tree - y) ** 2) / m appears in every NLopt objective/gradient
-- call, so these two rewrites are worth a measurable fraction of the AD
-- time.
rewritePowSq :: Fix SRTree -> Fix SRTree
rewritePowSq = cata alg
  where
    alg :: SRTree (Fix SRTree) -> Fix SRTree
    alg (Bin Power t (Fix (Const 2.0))) = Fix (Uni Square t)
    alg (Bin Div t (Fix (Const c)))     | c /= 0 = Fix (Bin Mul t (Fix (Const (recip c))))
    alg n                                = Fix n

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
                     then pure (VU.unsafeIndex static (key * m + row))
                     else case VU.unsafeIndex kind key of
                            1 -> pure (V.unsafeIndex theta (VU.unsafeIndex arg key))
                            3 -> do x <- VUM.unsafeRead fwd (VU.unsafeIndex arg key)
                                    pure (evalFunCode (VU.unsafeIndex fcode key) x)
                            4 -> do xl <- VUM.unsafeRead fwd (VU.unsafeIndex arg key)
                                    xr <- VUM.unsafeRead fwd (VU.unsafeIndex arg2 key)
                                    pure (evalOpCode (VU.unsafeIndex ocode key) xl xr)
                            _ -> error "evalGrad: unreachable"
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
                case VU.unsafeIndex kind key of
                  4 -> do
                    let l = VU.unsafeIndex arg key
                        r = VU.unsafeIndex arg2 key
                    xl <- VUM.unsafeRead fwd l
                    xr <- VUM.unsafeRead fwd r
                    fg <- VUM.unsafeRead fwd key
                    let (dl, dr) = diffScalarCode (VU.unsafeIndex ocode key) v xl xr fg
                    VUM.unsafeModify adj (+ dl) l
                    VUM.unsafeModify adj (+ dr) r
                  3 -> do
                    let t = VU.unsafeIndex arg key
                    x <- VUM.unsafeRead fwd t
                    VUM.unsafeModify adj (+ v * derivFunCode (VU.unsafeIndex fcode key) x) t
                  1 -> VUM.unsafeModify gradM (+ v) (VU.unsafeIndex arg key)
                  _ -> pure ()
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
    kind   = ctKind ct
    arg    = ctArg ct
    arg2   = ctArg2 ct
    fcode  = ctFcode ct
    ocode  = ctOcode ct
    dyn    = ctDyn ct
    static = ctStatic ct

-- ---------------------------------------------------------------------
-- Node-outer (vectorized-over-rows) evaluation: mirrors reverseModeGraph's
-- shape (one full length-m column per node, node-major loops) so the inner
-- loops are fused per node over all rows, with the static/dynamic pattern
-- decided once per node instead of once per row. Uses the same flat
-- [node * m + row] layout and compact op-code dispatch as `evalGrad`, but
-- trades the O(nodes + params) scratch of the row-fused version for the
-- O(nodes * m) fwd/adj columns of the massiv-style whole-column kernel.
evalGradVec :: CompiledTree -> V.Vector Double -> (Double, V.Vector Double)
evalGradVec ct theta = runST $ do
    -- Per-chunk buffers of O(stride * chunk) instead of one O(stride * m)
    -- allocation per call: the fwd/adj matrices are streamed one chunk of
    -- `chunk` rows at a time, so the per-call allocation drops ~m/chunk x
    -- (and the working set stays L3-resident). The chunk partition does not
    -- change any value: each row is independent, the objective row sums
    -- accumulate in order and the gradient accumulates row-sums per chunk.
    fwd   <- VUM.new (stride * chunk)   -- [node * nb + i]; dynamic columns written before read
    adj   <- VUM.replicate (stride * chunk) 0   -- [node * nb + i]
    gradM <- VUM.replicate p 0

    let go !start !acc
          | start >= m = do
              gradFrozen <- VU.unsafeFreeze gradM
              pure (acc, V.convert gradFrozen)
          | otherwise = do
              let nb = min chunk (m - start)
                  s0 = start
              forwardPassRange ct theta fwd s0 nb
              -- objective contribution = sum over this chunk's rows of root
              s <- if VU.unsafeIndex dyn root
                     then {-# SCC "objSumFwd" #-} sumCol fwd (root * nb) nb
                     else {-# SCC "objSumStatic" #-} sumStatic (root * m + s0) nb
              -- seed the root adjoint: d(obj)/d(root value) = 1 per row
              unless (s0 == 0) $ VUM.set adj 0   -- reuse the buffer; keep it clean
              when (VU.unsafeIndex dyn root) $ {-# SCC "seedAdj" #-} VUM.set (VUM.slice (root * nb) nb adj) 1
              -- backward: nodes from root down to 0 (valid reverse-topological order)
              let goBwd !key
                    | key < 0 = pure ()
                    | otherwise = do
                        bwdNode key
                        goBwd (key - 1)

                  bwdNode key
                    | not (VU.unsafeIndex dyn key) = pure ()  -- no Param in subtree
                    | otherwise = case VU.unsafeIndex kind key of
                        4 -> do
                          let l  = VU.unsafeIndex arg key
                              r  = VU.unsafeIndex arg2 key
                              oc = VU.unsafeIndex ocode key
                              dl = VU.unsafeIndex dyn l
                              dr = VU.unsafeIndex dyn r
                              kb = key * nb
                              lb = l * nb
                              rb = r * nb
                              ls = l * m + s0
                              rs = r * m + s0
                          case (dl, dr) of
                            (True, True)   -> {-# SCC "bwdBinTT" #-} bwdBin nb static fwd adj 0 oc kb lb rb ls rs
                            (True, False)  -> {-# SCC "bwdBinTS" #-} bwdBin nb static fwd adj 1 oc kb lb rb ls rs
                            (False, True)  -> {-# SCC "bwdBinST" #-} bwdBin nb static fwd adj 2 oc kb lb rb ls rs
                            (False, False) -> pure ()  -- no dynamic children to propagate to
                        3 -> do
                          let t  = VU.unsafeIndex arg key
                              fc = VU.unsafeIndex fcode key
                              kb = key * nb
                              tb = t * nb
                          if VU.unsafeIndex dyn t
                            then {-# SCC "bwdUni" #-} bwdUni nb fwd adj fc kb tb
                            else pure ()  -- static child: no Param below, nothing to accumulate
                        1 -> do
                          let a  = VU.unsafeIndex arg key
                              kb = key * nb
                          {-# SCC "bwdParam" #-} do
                            s' <- sumCol adj kb nb
                            VUM.unsafeModify gradM (+ s') a
                        _ -> pure ()
              goBwd root
              go (start + nb) (acc + s)

    go 0 0
  where
    root   = ctRoot ct
    m      = ctM ct
    p      = V.length theta
    stride = root + 1
    chunk  = 1024
    kind   = ctKind ct
    arg    = ctArg ct
    arg2   = ctArg2 ct
    fcode  = ctFcode ct
    ocode  = ctOcode ct
    dyn    = ctDyn ct
    static = ctStatic ct

    sumCol v vbase !n = go 0 0
      where go !i !acc | i >= n = pure acc
                       | otherwise = VUM.unsafeRead v (vbase + i) >>= \vv -> go (i + 1) (acc + vv)
    sumStatic sbase !n = go 0 0
      where go !i !acc | i >= n = pure acc
                       | otherwise = go (i + 1) (acc + VU.unsafeIndex static (sbase + i))

-- ---------------------------------------------------------------------
-- Forward-only objective evaluation: runs the forward pass and the row
-- sum but skips the adjoint/backward pass. Used where only the objective
-- value is needed (reporting loss / R2 metrics, the validation fitness in
-- the search), avoiding the ~2/3 of evalGradVec's work that computes the
-- gradient.
-- ---------------------------------------------------------------------
-- Chunked loss evaluation: runs the same node-outer forward pass as
-- `evalGradVec` (static columns precomputed in `ctStatic`, op codes
-- dispatched once per node into INLINE kernels) but only over a chunk of
-- `chunk` rows at a time with a per-call buffer of O(stride * chunk)
-- instead of O(stride * m). The chunk partition does not change any value
-- (each row is computed independently, the row sums accumulate in order),
-- but it cuts the per-call allocation ~30x so this is cheap enough for the
-- val-eval hot path that runs once per explored expression.
evalLossVec :: CompiledTree -> V.Vector Double -> Double
evalLossVec ct theta = runST $ do
    buf <- VUM.new (stride * chunk)
    go buf 0 0
  where
    root     = ctRoot ct
    m        = ctM ct
    stride   = root + 1
    dyn      = ctDyn ct
    static   = ctStatic ct
    chunk    = 4096

    go :: VUM.MVector s Double -> Int -> Double -> ST s Double
    go buf !start !acc
      | start >= m = pure acc
      | otherwise = do
          let nb = min chunk (m - start)
          forwardPassRange ct theta buf start nb
          s <- if VU.unsafeIndex dyn root
                 then sumCol buf (root * nb) nb
                 else sumStatic (root * m + start) nb
          go buf (start + nb) (acc + s)

    sumCol buf vbase !n = go 0 0
      where go !i !acc | i >= n = pure acc
                       | otherwise = VUM.unsafeRead buf (vbase + i) >>= \vv -> go (i + 1) (acc + vv)
    sumStatic sbase !n = go 0 0
      where go !i !acc | i >= n = pure acc
                       | otherwise = go (i + 1) (acc + VU.unsafeIndex static (sbase + i))

-- Forward pass shared by evalGradVec and evalLossVec: fills the `fwd`
-- columns of every dynamic node (ids are topologically ordered, so one
-- left-to-right sweep computes all of them; static columns are already in
-- `ctStatic`). The op/function codes are dispatched once per node and the
-- INLINE loop helpers run a tight fused kernel over the rows.
--
-- `s0`/`nb` select a range of rows [start, start+nb): with nb = m, start = 0
-- this is the full-matrix pass used by evalGradVec; evalLossVec calls it on
-- chunks of rows with a stride*nb buffer. The fwd buffer is indexed
-- [key * nb + i], static columns are read at [key * m + s0 + i].
forwardPassRange :: CompiledTree -> V.Vector Double -> VUM.MVector s Double -> Int -> Int -> ST s ()
forwardPassRange ct theta fwd s0 nb = goFwd 0
  where
    root   = ctRoot ct
    m      = ctM ct
    kind   = ctKind ct
    arg    = ctArg ct
    arg2   = ctArg2 ct
    fcode  = ctFcode ct
    ocode  = ctOcode ct
    dyn    = ctDyn ct
    static = ctStatic ct

    goFwd !key
      | key > root = pure ()
      | otherwise  = do
          if VU.unsafeIndex dyn key
            then case VU.unsafeIndex kind key of
              1 -> {-# SCC "fwdParam" #-} VUM.set (VUM.slice (key * nb) nb fwd) (V.unsafeIndex theta (VU.unsafeIndex arg key))
              3 -> do
                let t  = VU.unsafeIndex arg key
                    fc = VU.unsafeIndex fcode key
                    kb = key * nb
                    tb = t * nb
                if VU.unsafeIndex dyn t
                  then {-# SCC "fwdUniD" #-} fwdUniD nb fwd fc kb tb
                  else pure ()  -- a dynamic Uni always has a dynamic child
              4 -> do
                let l  = VU.unsafeIndex arg key
                    r  = VU.unsafeIndex arg2 key
                    oc = VU.unsafeIndex ocode key
                    dl = VU.unsafeIndex dyn l
                    dr = VU.unsafeIndex dyn r
                    kb = key * nb
                    lb = l * nb
                    rb = r * nb
                    ls = l * m + s0
                    rs = r * m + s0
                case (dl, dr) of
                  (True, True)   -> {-# SCC "fwdBinTT" #-} fwdBin nb static fwd 0 oc kb lb rb ls rs
                  (True, False)  -> {-# SCC "fwdBinTS" #-} fwdBin nb static fwd 1 oc kb lb rb ls rs
                  (False, True)  -> {-# SCC "fwdBinST" #-} fwdBin nb static fwd 2 oc kb lb rb ls rs
                  (False, False) -> pure ()  -- unreachable: a dynamic Bin always has a dynamic child
              _ -> pure ()
            else pure ()  -- static node: column already in `static`
          goFwd (key + 1)

    -- Forward binary kernels: `combo` 0=TT, 1=TS, 2=ST (SS is unreachable
    -- for dynamic nodes). The opcode is dispatched ONCE per node; the loop
    -- helpers are INLINE with the literal operator so each row iteration
    -- is a tight fused kernel with no per-element `case oc of` dispatch.
    -- `ls`/`rs` are the static column bases (already offset by s0), used by
    -- the TS/ST variants; `nb` is the number of rows in this chunk.
fwdBin :: Int -> VU.Vector Double -> VUM.MVector s Double -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> ST s ()
fwdBin nb static fwd combo oc kb lb rb ls rs = case (combo, oc) of
  (0, 0) -> fwdTT nb fwd (+) kb lb rb
  (0, 1) -> fwdTT nb fwd (-) kb lb rb
  (0, 2) -> fwdTT nb fwd (*) kb lb rb
  (0, 3) -> fwdTT nb fwd (/) kb lb rb
  (0, 4) -> fwdTT nb fwd (**) kb lb rb
  (0, 5) -> fwdTT nb fwd (\l r -> abs l ** r) kb lb rb
  (0, 6) -> fwdTT nb fwd (\l r -> l / sqrt (1 + r * r)) kb lb rb
  (1, 0) -> fwdTS nb static fwd (+) kb lb rs
  (1, 1) -> fwdTS nb static fwd (-) kb lb rs
  (1, 2) -> fwdTS nb static fwd (*) kb lb rs
  (1, 3) -> fwdTS nb static fwd (/) kb lb rs
  (1, 4) -> fwdTS nb static fwd (**) kb lb rs
  (1, 5) -> fwdTS nb static fwd (\l r -> abs l ** r) kb lb rs
  (1, 6) -> fwdTS nb static fwd (\l r -> l / sqrt (1 + r * r)) kb lb rs
  (2, 0) -> fwdST nb static fwd (+) kb ls rb
  (2, 1) -> fwdST nb static fwd (-) kb ls rb
  (2, 2) -> fwdST nb static fwd (*) kb ls rb
  (2, 3) -> fwdST nb static fwd (/) kb ls rb
  (2, 4) -> fwdST nb static fwd (**) kb ls rb
  (2, 5) -> fwdST nb static fwd (\l r -> abs l ** r) kb ls rb
  (2, 6) -> fwdST nb static fwd (\l r -> l / sqrt (1 + r * r)) kb ls rb
  _      -> pure ()
{-# INLINE fwdBin #-}

-- Backward binary kernels: same dispatch structure, `diff` is the local
-- (dl/dchild, dr/dchild) rule keyed on the opcode. `nb` is the number of
-- rows in this chunk, `ls`/`rs` are the static column bases already offset
-- by the chunk start (used by the TS/ST variants).
bwdBin :: Int -> VU.Vector Double -> VUM.MVector s Double -> VUM.MVector s Double -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> ST s ()
bwdBin nb static fwd adj combo oc kb lb rb ls rs = case (combo, oc) of
  (0, 0) -> bwdTT nb fwd adj (\dx _ _ _ -> (dx, dx)) kb lb rb
  (0, 1) -> bwdTT nb fwd adj (\dx _ _ _ -> (dx, negate dx)) kb lb rb
  (0, 2) -> bwdTT nb fwd adj (\dx fx gy _ -> (dx * gy, dx * fx)) kb lb rb
  (0, 3) -> bwdTT nb fwd adj (\dx _ gy fg -> (dx / gy, dx * (negate fg / gy))) kb lb rb
  (0, 4) -> bwdTT nb fwd adj (\dx fx gy fg -> (fixNaN (dx * gy * fg / fx), fixNaN (dx * fg * log fx))) kb lb rb
  (0, 5) -> bwdTT nb fwd adj (\dx fx gy fg ->
             let v2 = abs fx in (fixNaN (dx * (fx * gy) * fg / (v2 * v2)), fixNaN (dx * fg * log (abs fx)))) kb lb rb
  (0, 6) -> bwdTT nb fwd adj (\dx fx gy _ ->
             let dxl = dx * (recip . sqrt . (+1) . (^(2::Int))) gy
                 dxy = fx * gy * dxl ^ (3::Int)
             in (dxl, dxy)) kb lb rb
  (1, 0) -> bwdTS nb static fwd adj (\dx _ _ _ -> (dx, dx)) kb lb rs
  (1, 1) -> bwdTS nb static fwd adj (\dx _ _ _ -> (dx, negate dx)) kb lb rs
  (1, 2) -> bwdTS nb static fwd adj (\dx fx gy _ -> (dx * gy, dx * fx)) kb lb rs
  (1, 3) -> bwdTS nb static fwd adj (\dx _ gy fg -> (dx / gy, dx * (negate fg / gy))) kb lb rs
  (1, 4) -> bwdTS nb static fwd adj (\dx fx gy fg -> (fixNaN (dx * gy * fg / fx), fixNaN (dx * fg * log fx))) kb lb rs
  (1, 5) -> bwdTS nb static fwd adj (\dx fx gy fg ->
             let v2 = abs fx in (fixNaN (dx * (fx * gy) * fg / (v2 * v2)), fixNaN (dx * fg * log (abs fx)))) kb lb rs
  (1, 6) -> bwdTS nb static fwd adj (\dx fx gy _ ->
             let dxl = dx * (recip . sqrt . (+1) . (^(2::Int))) gy
                 dxy = fx * gy * dxl ^ (3::Int)
             in (dxl, dxy)) kb lb rs
  (2, 0) -> bwdST nb static fwd adj (\dx _ _ _ -> (dx, dx)) kb ls rb
  (2, 1) -> bwdST nb static fwd adj (\dx _ _ _ -> (dx, negate dx)) kb ls rb
  (2, 2) -> bwdST nb static fwd adj (\dx fx gy _ -> (dx * gy, dx * fx)) kb ls rb
  (2, 3) -> bwdST nb static fwd adj (\dx _ gy fg -> (dx / gy, dx * (negate fg / gy))) kb ls rb
  (2, 4) -> bwdST nb static fwd adj (\dx fx gy fg -> (fixNaN (dx * gy * fg / fx), fixNaN (dx * fg * log fx))) kb ls rb
  (2, 5) -> bwdST nb static fwd adj (\dx fx gy fg ->
             let v2 = abs fx in (fixNaN (dx * (fx * gy) * fg / (v2 * v2)), fixNaN (dx * fg * log (abs fx)))) kb ls rb
  (2, 6) -> bwdST nb static fwd adj (\dx fx gy _ ->
             let dxl = dx * (recip . sqrt . (+1) . (^(2::Int))) gy
                 dxy = fx * gy * dxl ^ (3::Int)
             in (dxl, dxy)) kb ls rb
  _      -> pure ()
{-# INLINE bwdBin #-}

fwdTT nb fwd op kb lb rb = forRows nb $ \i -> do
  xl <- VUM.unsafeRead fwd (lb + i)
  xr <- VUM.unsafeRead fwd (rb + i)
  VUM.unsafeWrite fwd (kb + i) (op xl xr)
{-# INLINE fwdTT #-}

fwdTS nb static fwd op kb lb rb = forRows nb $ \i -> do
  xl <- VUM.unsafeRead fwd (lb + i)
  VUM.unsafeWrite fwd (kb + i) (op xl (VU.unsafeIndex static (rb + i)))
{-# INLINE fwdTS #-}

fwdST nb static fwd op kb lb rb = forRows nb $ \i -> do
  xr <- VUM.unsafeRead fwd (rb + i)
  VUM.unsafeWrite fwd (kb + i) (op (VU.unsafeIndex static (lb + i)) xr)
{-# INLINE fwdST #-}

bwdTT nb fwd adj diff kb lb rb = forRows nb $ \i -> do
  v  <- VUM.unsafeRead adj (kb + i)
  xl <- VUM.unsafeRead fwd (lb + i)
  xr <- VUM.unsafeRead fwd (rb + i)
  fg <- VUM.unsafeRead fwd (kb + i)
  let (gl, gr) = diff v xl xr fg
  a <- VUM.unsafeRead adj (lb + i)
  VUM.unsafeWrite adj (lb + i) (a + gl)
  b <- VUM.unsafeRead adj (rb + i)
  VUM.unsafeWrite adj (rb + i) (b + gr)
{-# INLINE bwdTT #-}

bwdTS nb static fwd adj diff kb lb rs = forRows nb $ \i -> do
  v  <- VUM.unsafeRead adj (kb + i)
  xl <- VUM.unsafeRead fwd (lb + i)
  fg <- VUM.unsafeRead fwd (kb + i)
  let (gl, _) = diff v xl (VU.unsafeIndex static (rs + i)) fg
  a <- VUM.unsafeRead adj (lb + i)
  VUM.unsafeWrite adj (lb + i) (a + gl)
{-# INLINE bwdTS #-}

bwdST nb static fwd adj diff kb ls rb = forRows nb $ \i -> do
  v  <- VUM.unsafeRead adj (kb + i)
  xr <- VUM.unsafeRead fwd (rb + i)
  fg <- VUM.unsafeRead fwd (kb + i)
  let (_, gr) = diff v (VU.unsafeIndex static (ls + i)) xr fg
  b <- VUM.unsafeRead adj (rb + i)
  VUM.unsafeWrite adj (rb + i) (b + gr)
{-# INLINE bwdST #-}

-- Forward unary kernels (dynamic child): the function code is dispatched
-- ONCE per node and the loop helper is INLINE with the literal function,
-- so each row iteration is a tight fused kernel with no per-element
-- `case fc of` / closure build (a dynamic Uni node always has a dynamic
-- child, so there is no static-child variant here).
fwdUniD :: Int -> VUM.MVector s Double -> Int -> Int -> Int -> ST s ()
fwdUniD nb fwd fc kb tb = case fc of
  0  -> fwdUniD' nb fwd (\x -> x) kb tb
  1  -> fwdUniD' nb fwd abs kb tb
  2  -> fwdUniD' nb fwd sin kb tb
  3  -> fwdUniD' nb fwd cos kb tb
  4  -> fwdUniD' nb fwd tan kb tb
  5  -> fwdUniD' nb fwd sinh kb tb
  6  -> fwdUniD' nb fwd cosh kb tb
  7  -> fwdUniD' nb fwd tanh kb tb
  8  -> fwdUniD' nb fwd asin kb tb
  9  -> fwdUniD' nb fwd acos kb tb
  10 -> fwdUniD' nb fwd atan kb tb
  11 -> fwdUniD' nb fwd asinh kb tb
  12 -> fwdUniD' nb fwd acosh kb tb
  13 -> fwdUniD' nb fwd atanh kb tb
  14 -> fwdUniD' nb fwd sqrt kb tb
  15 -> fwdUniD' nb fwd (\x -> sqrt (abs x)) kb tb
  16 -> fwdUniD' nb fwd (\x -> signum x * abs x ** (1 / 3)) kb tb
  17 -> fwdUniD' nb fwd (\x -> x * x) kb tb
  18 -> fwdUniD' nb fwd log kb tb
  19 -> fwdUniD' nb fwd (\x -> log (abs x)) kb tb
  20 -> fwdUniD' nb fwd exp kb tb
  21 -> fwdUniD' nb fwd recip kb tb
  22 -> fwdUniD' nb fwd (\x -> x * x * x) kb tb
  _  -> pure ()
{-# INLINE fwdUniD #-}

fwdUniD' nb fwd f kb tb = forRows nb $ \i -> do
  x <- VUM.unsafeRead fwd (tb + i)
  VUM.unsafeWrite fwd (kb + i) (f x)
{-# INLINE fwdUniD' #-}

-- Backward unary kernel: derivative of the function, dispatched once per
-- node and inlined into the accumulation loop. `nb` is the number of rows
-- in the current chunk.
bwdUni :: Int -> VUM.MVector s Double -> VUM.MVector s Double -> Int -> Int -> Int -> ST s ()
bwdUni nb fwd adj fc kb tb = case fc of
  0  -> bwdUni' nb fwd adj (\_ -> 1) kb tb
  1  -> bwdUni' nb fwd adj (\x -> x / abs x) kb tb
  2  -> bwdUni' nb fwd adj cos kb tb
  3  -> bwdUni' nb fwd adj (negate . sin) kb tb
  4  -> bwdUni' nb fwd adj (\x -> 1 / (cos x * cos x)) kb tb
  5  -> bwdUni' nb fwd adj cosh kb tb
  6  -> bwdUni' nb fwd adj sinh kb tb
  7  -> bwdUni' nb fwd adj (\x -> 1 - tanh x * tanh x) kb tb
  8  -> bwdUni' nb fwd adj (\x -> 1 / sqrt (1 - x * x)) kb tb
  9  -> bwdUni' nb fwd adj (\x -> -1 / sqrt (1 - x * x)) kb tb
  10 -> bwdUni' nb fwd adj (\x -> 1 / (1 + x * x)) kb tb
  11 -> bwdUni' nb fwd adj (\x -> 1 / sqrt (1 + x * x)) kb tb
  12 -> bwdUni' nb fwd adj (\x -> 1 / (sqrt (x - 1) * sqrt (x + 1))) kb tb
  13 -> bwdUni' nb fwd adj (\x -> 1 / (1 - x * x)) kb tb
  14 -> bwdUni' nb fwd adj (\x -> 1 / (2 * sqrt x)) kb tb
  15 -> bwdUni' nb fwd adj (\x -> x / (2 * abs x ** (3 / 2))) kb tb
  16 -> bwdUni' nb fwd adj (\x -> 1 / (3 * (x * x) ** (1 / 3))) kb tb
  17 -> bwdUni' nb fwd adj (\x -> 2 * x) kb tb
  18 -> bwdUni' nb fwd adj recip kb tb
  19 -> bwdUni' nb fwd adj recip kb tb
  20 -> bwdUni' nb fwd adj exp kb tb
  21 -> bwdUni' nb fwd adj (\x -> -1 / (x * x)) kb tb
  22 -> bwdUni' nb fwd adj (\x -> 3 * x * x) kb tb
  _  -> pure ()
{-# INLINE bwdUni #-}

bwdUni' nb fwd adj f kb tb = forRows nb $ \i -> do
  v <- VUM.unsafeRead adj (kb + i)
  x <- VUM.unsafeRead fwd (tb + i)
  c <- VUM.unsafeRead adj (tb + i)
  VUM.unsafeWrite adj (tb + i) (c + v * f x)
{-# INLINE bwdUni' #-}
-- Unboxed ST loop over the m data rows; always inlined so the per-node
-- bodies above are fused into a single tail-recursive kernel per node.
forRows :: Int -> (Int -> ST s ()) -> ST s ()
forRows !n f = go 0
  where
    go !i | i >= n    = pure ()
          | otherwise = f i >> go (i + 1)
{-# INLINE forRows #-}
evalOpCode :: Int -> Double -> Double -> Double
evalOpCode 0 = (+)
evalOpCode 1 = (-)
evalOpCode 2 = (*)
evalOpCode 3 = (/)
evalOpCode 4 = (**)
evalOpCode 5 = \l r -> abs l ** r
evalOpCode 6 = \l r -> l / sqrt (1 + r * r)
evalOpCode _ = error "evalOpCode: bad op code"
{-# INLINE evalOpCode #-}

evalFunCode :: Int -> Double -> Double
evalFunCode 0  = id
evalFunCode 1  = abs
evalFunCode 2  = sin
evalFunCode 3  = cos
evalFunCode 4  = tan
evalFunCode 5  = sinh
evalFunCode 6  = cosh
evalFunCode 7  = tanh
evalFunCode 8  = asin
evalFunCode 9  = acos
evalFunCode 10 = atan
evalFunCode 11 = asinh
evalFunCode 12 = acosh
evalFunCode 13 = atanh
evalFunCode 14 = sqrt
evalFunCode 15 = \x -> sqrt (abs x)
evalFunCode 16 = \x -> signum x * abs x ** (1 / 3)
evalFunCode 17 = \x -> x * x
evalFunCode 18 = log
evalFunCode 19 = \x -> log (abs x)
evalFunCode 20 = exp
evalFunCode 21 = recip
evalFunCode 22 = \x -> x * x * x
evalFunCode _  = error "evalFunCode: bad function code"
{-# INLINE evalFunCode #-}

derivFunCode :: Int -> Double -> Double
derivFunCode 0  = const 1
derivFunCode 1  = \x -> x / abs x
derivFunCode 2  = cos
derivFunCode 3  = negate . sin
derivFunCode 4  = \x -> 1 / (cos x * cos x)
derivFunCode 5  = cosh
derivFunCode 6  = sinh
derivFunCode 7  = \x -> 1 - tanh x * tanh x
derivFunCode 8  = \x -> 1 / sqrt (1 - x * x)
derivFunCode 9  = \x -> -1 / sqrt (1 - x * x)
derivFunCode 10 = \x -> 1 / (1 + x * x)
derivFunCode 11 = \x -> 1 / sqrt (1 + x * x)
derivFunCode 12 = \x -> 1 / (sqrt (x - 1) * sqrt (x + 1))
derivFunCode 13 = \x -> 1 / (1 - x * x)
derivFunCode 14 = \x -> 1 / (2 * sqrt x)
derivFunCode 15 = \x -> x / (2 * abs x ** (3 / 2))
derivFunCode 16 = \x -> 1 / (3 * (x * x) ** (1 / 3))
derivFunCode 17 = (* 2)
derivFunCode 18 = recip
derivFunCode 19 = recip
derivFunCode 20 = exp
derivFunCode 21 = \x -> -1 / (x * x)
derivFunCode 22 = \x -> 3 * x * x
derivFunCode _  = error "derivFunCode: bad function code"
{-# INLINE derivFunCode #-}

-- Pure local-derivative rules keyed on fromEnum Op, scalar version (same
-- math as the original vectorized `diffPure`, applied per-row above).
diffScalarCode :: Int -> Double -> Double -> Double -> Double -> (Double, Double)
diffScalarCode 0 dx _  _  _  = (dx, dx)
diffScalarCode 1 dx _  _  _  = (dx, negate dx)
diffScalarCode 2 dx fx gy _  = (dx * gy, dx * fx)
diffScalarCode 3 dx _  gy fg = (dx / gy, dx * (negate fg / gy))
diffScalarCode 4 dx fx gy fg =
    ( fixNaN (dx * gy * fg / fx)
    , fixNaN (dx * fg * log fx) )
diffScalarCode 5 dx fx gy fg =
    let v2 = abs fx
    in ( fixNaN (dx * (fx * gy) * fg / (v2 * v2))
       , fixNaN (dx * fg * log (abs fx)) )
diffScalarCode 6 dx fx gy _ =
    let dxl = dx * (recip . sqrt . (+1) . (^(2::Int))) gy
        dxy = fx * gy * dxl ^ (3::Int)
    in (dxl, dxy)
diffScalarCode _ _ _ _ _ = error "diffScalarCode: bad op code"
{-# INLINE diffScalarCode #-}

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
        numChunks = max 1 (min cap (nRows `div` minChunkSize))
        cap       = if mtSingleChunk then 1 else unsafePerformIO getNumCapabilities
        ysChunks  = chunkVector numChunks ys
        -- transpose groups the chunks by slice rather than by feature
        xssChunks = Data.List.transpose (map (chunkVector numChunks) xss)
        errChunks = case mYErr of
                      Just e  -> map Just (chunkVector numChunks e)
                      Nothing -> replicate (length ysChunks) Nothing
    in [ compileTree xs y err tree | (xs, y, err) <- zip3 xssChunks ysChunks errChunks ]

-- | When True, the MultiThread backend compiles/evaluates each tree on a
-- single chunk so a higher-level population-parallel driver (eggp's fitness
-- batch) owns the cores instead of oversubscribing the per-tree chunk split.
{-# NOINLINE mtSingleChunk #-}
mtSingleChunk :: Bool
mtSingleChunk = unsafePerformIO (readIORef mtParGate)

mtParGate :: IORef Bool
mtParGate = unsafePerformIO (newIORef False)
{-# NOINLINE mtParGate #-}

-- | Enable/disable single-chunk (non-oversubscribing) mode for the MultiThread
-- backend; called around a population-parallel fitness batch.
setMTPopParallel :: Bool -> IO ()
setMTPopParallel b = writeIORef mtParGate b

-- | Evaluates the gradient across all compiled chunks in parallel.
-- Each chunk is evaluated by the fast node-outer `evalGradVec` kernel on
-- its own slice of the data. The kernel is now chunked internally (O(stride
-- * 1024) per-call buffers, L3-resident) and is compute-bound rather than
-- memory-bandwidth-bound, so splitting the data into one chunk per core and
-- running the kernels concurrently scales almost linearly. The objective
-- and gradient accumulate across chunks (same math per row; only the FP
-- summation order across chunk boundaries differs).
evalGradMulti :: [CompiledTree] -> V.Vector Double -> (Double, V.Vector Double)
evalGradMulti [ct] theta = evalGradVec ct theta
evalGradMulti cts theta = unsafePerformIO $ do
    results <- forConcurrently cts $ \ct -> evaluate (evalGradVec ct theta)
    let totalObj   = sum $ map fst results
        totalGrad  = foldl1' (V.zipWith (+)) (map snd results)
    pure (totalObj, totalGrad)
