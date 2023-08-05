-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Derivative 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Symbolic derivative of SRTree expressions
--
-----------------------------------------------------------------------------
module Data.SRTree.Derivative
        ( derivative
        , doubleDerivative
        , deriveByVar
        , deriveByParam
        )
        where

import Data.SRTree.Internal
import Data.SRTree.Eval
import Data.SRTree.Recursion ( Fix (..), mutu )

-- | Creates the symbolic partial derivative of a tree by variable `dx` (if `p` is `False`)
-- or parameter `dx` (if `p` is `True`).
-- This uses mutual recursion where the first recursion (alg1) holds the derivative w.r.t. 
-- the current node and the second (alg2) holds the original tree.
deriveBy :: Bool -> Int -> Fix SRTree -> Fix SRTree
deriveBy p dx = fst (mutu alg1 alg2)
  where
      alg1 (Var ix)        = if not p && ix == dx then 1 else 0
      alg1 (Param ix)      = if p && ix == dx then 1 else 0
      alg1 (Const _)       = 0
      alg1 (Uni f t)       = derivative f (snd t) * fst t
      alg1 (Bin Add l r)   = fst l + fst r
      alg1 (Bin Sub l r)   = fst l - fst r
      alg1 (Bin Mul l r)   = fst l * snd r + snd l * fst r
      alg1 (Bin Div l r)   = (fst l * snd r - snd l * fst r) / snd r ** 2
      alg1 (Bin Power l r) = snd l ** (snd r - 1) * (snd r * fst l + snd l * log (snd l) * fst r)

      alg2 (Var ix)    = var ix
      alg2 (Param ix)  = param ix
      alg2 (Const c)   = Fix (Const c)
      alg2 (Uni f t)   = Fix (Uni f $ snd t)
      alg2 (Bin f l r) = Fix (Bin f (snd l) (snd r))

-- | Derivative of each supported function
-- For a function h(f) it returns the derivative dh/df
derivative :: Floating a => Function -> a -> a
derivative Id      = const 1
derivative Abs     = \x -> x / abs x
derivative Sin     = cos
derivative Cos     = negate.sin
derivative Tan     = recip . (**2.0) . cos
derivative Sinh    = cosh
derivative Cosh    = sinh
derivative Tanh    = (1-) . (**2.0) . tanh
derivative ASin    = recip . sqrt . (1-) . (^2)
derivative ACos    = negate . recip . sqrt . (1-) . (^2)
derivative ATan    = recip . (1+) . (^2)
derivative ASinh   = recip . sqrt . (1+) . (^2)
derivative ACosh   = \x -> 1 / (sqrt (x-1) * sqrt (x+1))
derivative ATanh   = recip . (1-) . (^2)
derivative Sqrt    = recip . (2*) . sqrt
derivative Cbrt    = recip . (3*) . cbrt . (^2)
derivative Square  = (2*)
derivative Exp     = exp
derivative Log     = recip
{-# INLINE derivative #-}

-- | Second-order derivative of supported functions
doubleDerivative :: Floating a => Function -> a -> a
doubleDerivative Id      = const 0
doubleDerivative Abs     = const 0
doubleDerivative Sin     = negate.sin
doubleDerivative Cos     = negate.cos
doubleDerivative Tan     = \x -> 2 * sin x / (cos x) ^ 3
doubleDerivative Sinh    = sinh
doubleDerivative Cosh    = cosh
doubleDerivative Tanh    = \x -> -2 * tanh x * (1 / cosh x)^2
doubleDerivative ASin    = \x -> x / (1 - x^2)**(3/2)
doubleDerivative ACos    = \x -> x / (1 - x^2)**(3/2)
doubleDerivative ATan    = \x -> (-2*x) / (x^2 + 1)^2
doubleDerivative ASinh   = \x -> x / (x^2 + 1)**(3/2) -- check
doubleDerivative ACosh   = \x -> 1 / (sqrt (x-1) * sqrt (x+1)) -- check
doubleDerivative ATanh   = recip . (1-) . (^2) -- check
doubleDerivative Sqrt    = \x -> -1 / (4 * sqrt x^3)
doubleDerivative Cbrt    = \x -> -2 / (9 * x * (x^2)**(1/3))
doubleDerivative Square  = const 2
doubleDerivative Exp     = exp
doubleDerivative Log     = negate . recip . (^2)
{-# INLINE doubleDerivative #-}

-- | Symbolic derivative by a variable
deriveByVar :: Int -> Fix SRTree -> Fix SRTree
deriveByVar = deriveBy False
{-# INLINE deriveByVar #-}

-- | Symbolic derivative by a parameter
deriveByParam :: Int -> Fix SRTree -> Fix SRTree
deriveByParam = deriveBy True
{-# INLINE deriveByParam #-}