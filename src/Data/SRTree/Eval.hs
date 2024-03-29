-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Eval 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Evaluation of SRTree expressions
--
-----------------------------------------------------------------------------
module Data.SRTree.Eval
        ( evalTree
        , evalOp
        , evalFun
        , cbrt
        , inverseFunc
        , invertibles
        , evalInverse
        , invright
        , invleft
        )
        where

import qualified Data.Vector as V
import qualified Data.Vector.Storable as VS
import Data.Vector.Storable ((!))

import Data.SRTree.Internal
import Data.SRTree.Recursion ( Fix (..), cata )

-- | Evaluates the tree given a vector of variable values, a vector of parameter values and a function that takes a Double and change to whatever type the variables have. This is useful when working with datasets of many values per variables.
evalTree :: (Num a, Floating a) => V.Vector a -> VS.Vector Double -> (Double -> a) -> Fix SRTree -> a
evalTree xss params f = cata alg
  where
      alg (Var ix)     = xss V.! ix
      alg (Param ix)   = f $ params ! ix
      alg (Const c)    = f c
      alg (Uni g t)    = evalFun g t
      alg (Bin op l r) = evalOp op l r
{-# INLINE evalTree #-}

evalOp :: Floating a => Op -> a -> a -> a
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mul = (*)
evalOp Div = (/)
evalOp Power = (**)
{-# INLINE evalOp #-}

evalFun :: Floating a => Function -> a -> a
evalFun Id = id
evalFun Abs = abs
evalFun Sin = sin
evalFun Cos = cos
evalFun Tan = tan
evalFun Sinh = sinh
evalFun Cosh = cosh
evalFun Tanh = tanh
evalFun ASin = asin
evalFun ACos = acos
evalFun ATan = atan
evalFun ASinh = asinh
evalFun ACosh = acosh
evalFun ATanh = atanh
evalFun Sqrt = sqrt
evalFun Cbrt = cbrt
evalFun Square = (^2)
evalFun Log = log
evalFun Exp = exp
{-# INLINE evalFun #-}

-- | Cubic root
cbrt :: Floating val => val -> val
cbrt x = signum x * abs x ** (1/3)
{-# INLINE cbrt #-}

-- | Returns the inverse of a function. This is a partial function.
inverseFunc :: Function -> Function
inverseFunc Id     = Id
inverseFunc Sin    = ASin
inverseFunc Cos    = ACos
inverseFunc Tan    = ATan
inverseFunc Sinh   = ASinh
inverseFunc Cosh   = ACosh
inverseFunc Tanh   = ATanh
inverseFunc ASin   = Sin
inverseFunc ACos   = Cos
inverseFunc ATan   = Tan
inverseFunc ASinh  = Sinh
inverseFunc ACosh  = Cosh
inverseFunc ATanh  = Tanh
inverseFunc Sqrt   = Square
inverseFunc Square = Sqrt
-- inverseFunc Cbrt   = (^3)
inverseFunc Log    = Exp
inverseFunc Exp    = Log
-- inverseFunc Abs    = Abs -- we assume abs(x) = sqrt(x^2) so y = sqrt(x^2) => x^2 = y^2 => x = sqrt(y^2) = x = abs(y)
inverseFunc x      = error $ show x ++ " has no support for inverse function"
{-# INLINE inverseFunc #-}

evalInverse :: Floating a => Function -> a -> a
evalInverse Id     = id
evalInverse Sin    = asin
evalInverse Cos    = acos
evalInverse Tan    = atan
evalInverse Sinh   = asinh
evalInverse Cosh   = acosh
evalInverse Tanh   = atanh
evalInverse ASin   = sin
evalInverse ACos   = cos
evalInverse ATan   = tan
evalInverse ASinh  = sinh
evalInverse ACosh  = cosh
evalInverse ATanh  = tanh
evalInverse Sqrt   = (^2)
evalInverse Square = sqrt
evalInverse Cbrt   = (^3)
evalInverse Log    = exp
evalInverse Exp    = log
evalInverse Abs    = abs -- we assume abs(x) = sqrt(x^2) so y = sqrt(x^2) => x^2 = y^2 => x = sqrt(y^2) = x = abs(y)

invright :: Floating a => Op -> a -> (a -> a)
invright Add v   = (subtract v)
invright Sub v   = (+v)
invright Mul v   = (/v)
invright Div v   = (*v)
invright Power v = (**(1/v))

invleft :: Floating a => Op -> a -> (a -> a)
invleft Add v   = (subtract v)
invleft Sub v   = (+v) . negate -- y = v - r => r = v - y
invleft Mul v   = (/v)
invleft Div v   = (v/) -- y = v / r => r = v/y
invleft Power v = (/(log v)) . log -- y = v ^ r  log y = r log v r = log y / log v

-- | List of invertible functions
invertibles :: [Function]
invertibles = [Id, Sin, Cos, Tan, Tanh, ASin, ACos, ATan, ATanh, Sqrt, Square, Log, Exp]