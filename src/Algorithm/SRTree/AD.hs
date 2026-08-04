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
         ( compileFunAndGrad
         , ADBackEnd(..)
         ) where

import qualified Data.Vector.Unboxed  as VU
import qualified Data.Vector.Storable as V
import Data.SRTree
import Algorithm.SRTree.AD.Unboxed
import Algorithm.SRTree.AD.Accelerate

data ADBackEnd = SingleThread | MultiThread | Accelerate deriving (Read, Show)

compileFunAndGrad :: ADBackEnd -> [VU.Vector Double] -> VU.Vector Double -> Maybe (VU.Vector Double) -> Fix SRTree -> V.Vector Double -> (Double, V.Vector Double)
compileFunAndGrad SingleThread xss ys mYerr tree =
    -- evalGradVec is the node-outer, chunk-vectorized kernel (opcode
    -- dispatched once per node, then a tight per-row loop LLVM can
    -- auto-vectorize with -mavx2 -mfma). The old `evalGrad` re-dispatched
    -- the node-kind case on every row (row-outer), which is not
    -- SIMD-friendly and was the real reason SingleThread was slower than
    -- MultiThread even at a single capability/chunk -- not thread count.
    -- Both operate on the same `CompiledTree` and evalGradVec is already
    -- chunked (stride*1024 buffers), so there's no memory-cost tradeoff.
    let ct = compileTree xss ys mYerr tree
    in \theta -> evalGradVec ct theta
compileFunAndGrad MultiThread xss ys mYerr tree =
    let cts = compileTreeMulti xss ys mYerr tree
    in \theta -> evalGradMulti cts theta
compileFunAndGrad Accelerate xss ys mYerr tree   = compileAccelerateTree (compileTree xss ys mYerr tree) xss ys
