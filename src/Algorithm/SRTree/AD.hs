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

module Algorithm.SRTree.AD
         ( compileTree
         , compileTreeMulti
         , evalGradMulti
         , CompiledTree(..)
         ) where

import Control.Monad (forM_, foldM, when, unless)
import Control.Monad.ST
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


import Control.Parallel.Strategies (parList, rdeepseq, using)
import Data.List (transpose)
import System.IO.Unsafe (unsafePerformIO)
import Control.Concurrent (getNumCapabilities)

--import UnliftIO.Async

import qualified Data.Map.Strict as Map

-- ---------------------------------------------------------------------
-- Public entry point -- same signature/behaviour as before.
-- ---------------------------------------------------------------------
data CompiledTree = CompiledTree
  { ctNodes  :: !(VB.Vector (SRTree Int))            -- id -> node, children already resolved to ids
  , ctRoot   :: !Int
  , ctDyn    :: !(VU.Vector Bool)                    -- id -> depends on theta?
  , ctStatic :: !(IntMap.IntMap (VU.Vector Double))   -- precomputed values, only for non-dynamic ids
  , ctM      :: !Int
  }

compileTree :: [VU.Vector Double] -> VU.Vector Double -> Maybe (VU.Vector Double) -> Fix SRTree -> CompiledTree
compileTree xss ys mYErr tree =
    CompiledTree { ctNodes = nodes, ctRoot = root, ctDyn = dynArr, ctStatic = static, ctM = m }
  where
    yErr = fromJust mYErr
    m    = VU.length ys

    -- state: (structural CSE map, id -> node, id -> isDynamic, id -> static value, counter)
    (_, int2key, dynMap, static, (subtract 1) -> root) =
        cataM leftToRight alg tree
          `execState` (Map.empty, IntMap.empty, IntMap.empty, IntMap.empty, 0)

    nodes  = VB.fromList (IntMap.elems int2key)
    dynArr = VU.fromList (IntMap.elems dynMap)

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

evalGrad :: CompiledTree -> V.Vector Double -> (Double, V.Vector Double)
evalGrad ct theta = (VU.sum $ vals IntMap.! root, grad)
  where
    root  = ctRoot ct
    m     = ctM ct
    p     = V.length theta
    nodes = ctNodes ct
    dyn   = ctDyn ct
    one   = VU.replicate m 1

    vals = foldl' step (ctStatic ct) [0 .. root]
      where
        step acc key
          | not (dyn VU.! key) = acc          -- static value already present, nothing to do
          | otherwise          = IntMap.insert key (evalDyn key acc) acc
        evalDyn key acc = case nodes VB.! key of
          Param ix   -> VU.replicate m (theta V.! ix)
          Uni f t    -> VU.map (evalFun f) (acc IntMap.! t)
          Bin op l r -> VU.zipWith (evalOp op) (acc IntMap.! l) (acc IntMap.! r)
          _          -> error "evalGrad: unreachable"

    gradMap = calcGrad root one `execState` IntMap.empty

    calcGrad :: Int -> VU.Vector Double -> State (IntMap.IntMap Double) ()
    calcGrad key v
      | not (dyn VU.! key) = pure ()   -- no Param below here: prune, nothing to accumulate
      | otherwise =
          case nodes VB.! key of
            Bin op l r -> do
              let xl       = vals IntMap.! l
                  xr       = vals IntMap.! r
                  fg       = vals IntMap.! key   -- this node's own cached forward value
                  (dl, dr) = diffPure op v xl xr fg
              calcGrad l dl
              calcGrad r dr
            Uni f t -> do
              let x = vals IntMap.! t
              calcGrad t (VU.zipWith (*) v (VU.map (derivative f) x))
            Param ix -> modify' (IntMap.insertWith (+) ix (VU.sum v))
            _        -> pure ()

    grad = V.generate p (\ix -> IntMap.findWithDefault 0 ix gradMap)

-- Pure local-derivative rules (same math as your `diff`, no State/Map
-- plumbing needed since `fg` -- the node's own value -- is already just
-- a plain lookup in `vals`, not something that needs re-deriving).
diffPure :: Op -> VU.Vector Double -> VU.Vector Double -> VU.Vector Double -> VU.Vector Double
         -> (VU.Vector Double, VU.Vector Double)
diffPure Add dx _  _  _  = (dx, dx)
diffPure Sub dx _  _  _  = (dx, VU.map negate dx)
diffPure Mul dx fx gy _  = (VU.zipWith (*) dx gy, VU.zipWith (*) dx fx)
diffPure Div dx _  gy fg =
    ( VU.zipWith (/) dx gy
    , VU.zipWith (*) dx (VU.zipWith (\l r -> negate l / r) fg gy) )
diffPure Power dx fx gy fg =
    ( VU.zipWith4 (\d f g v -> fixNaN $ d * g * v / f) dx fx gy fg
    , VU.zipWith3 (\d f v   -> fixNaN $ d * v * log f) dx fx fg )
diffPure PowerAbs dx fx gy fg =
    -- v2/v3 inlined directly (see earlier note) instead of materialized as separate arrays
    ( VU.zipWith4 (\d f g v -> let v2 = abs f in fixNaN $ d * (f * g) * v / (v2 * v2)) dx fx gy fg
    , VU.zipWith4 (\d f _ v -> fixNaN $ d * v * log (abs f))                          dx fx gy fg )
diffPure AQ dx fx gy _ =
    let dxl = VU.zipWith (\g d -> d * (recip . sqrt . (+1) . (^(2::Int))) g) gy dx
        dxy = VU.zipWith3 (\f g dl -> f * g * dl ^ (3::Int)) fx gy dxl
    in (dxl, dxy)
{-# INLINE diffPure #-}

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
        numChunks = max 1 $ nRows `div` 10000 -- 8 * unsafePerformIO getNumCapabilities
        ysChunks  = chunkVector numChunks ys
        -- transpose groups the chunks by slice rather than by feature
        xssChunks = Data.List.transpose (map (chunkVector numChunks) xss)
        errChunks = case mYErr of
                      Just e  -> map Just (chunkVector numChunks e)
                      Nothing -> replicate (length ysChunks) Nothing
    in [ compileTree xs y err tree | (xs, y, err) <- zip3 xssChunks ysChunks errChunks ]

-- | Evaluates the gradient across all compiled chunks in parallel.
evalGradMulti :: [CompiledTree] -> V.Vector Double -> (Double, V.Vector Double)
evalGradMulti cts theta =
    let -- parList rdeepseq fully evaluates the (Double, V.Vector Double) tuples in parallel
        results = map (`evalGrad` theta) cts `using` parList rdeepseq

        -- Accumulate the total objective
        totalObj = sum $ map fst results

        -- Accumulate the gradients (element-wise vector addition)
        totalGrad = foldl1' (V.zipWith (+)) (map snd results)
    in (totalObj, totalGrad)
