{-# LANGUAGE LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Eval 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Evaluation of SRTree expressions
--
-----------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
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
        , replicateAs
        , SRVector, PVector, SRMatrix
        , compMode
        )
        where

import Data.Massiv.Array
import qualified Data.Massiv.Array as M
import Data.SRTree.Internal
import Data.SRTree.Recursion (Fix (..), cata)

-- | Vector of target values 
type SRVector = M.Array D Ix1 Double
-- | Vector of parameter values. Needs to be strict to be readily accesible.
type PVector  = M.Array S Ix1 Double
-- | Matrix of features values 
type SRMatrix = M.Array S Ix2 Double

compMode :: M.Comp
compMode = M.Seq

-- Improve quality of life with Num and Floating instances for our matrices 
instance Index ix => Num (M.Array D ix Double) where
    (+) = (!+!)
    (-) = (!-!)
    (*) = (!*!)
    abs = absA
    signum = signumA 
    fromInteger = fromInteger
    negate = negateA

instance Index ix => Floating (M.Array D ix Double) where
    pi = pi 
    exp = expA 
    log = logA 
    sqrt = sqrtA 
    sin = sinA 
    cos = cosA
    tan = tanA 
    asin = asinA 
    acos = acosA 
    atan = atanA 
    sinh = sinhA 
    cosh = coshA
    tanh = tanhA 
    asinh = asinhA 
    acosh = acoshA 
    atanh = atanhA 
    (**) = (.**)
instance Index ix => Fractional (M.Array D ix Double) where
    fromRational = fromRational
    (/) = (!/!)
    recip = recipA

-- returns a vector with the same number of rows as xss and containing a single repeated value.
replicateAs :: SRMatrix -> Double -> SRVector
replicateAs xss c = let (Sz (m :. _)) = M.size xss in M.replicate (getComp xss) (Sz m) c
{-# INLINE replicateAs #-}

-- | Evaluates the tree given a vector of variable values, a vector of parameter values and a function that takes a Double and change to whatever type the variables have. This is useful when working with datasets of many values per variables.
evalTree :: SRMatrix -> PVector -> Fix IndexedTree -> SRVector
evalTree xss params = cata $ 
    \case 
      Var ix     -> xss <! ix
      Param ix   -> replicateAs xss $ params ! ix
      Const c    -> replicateAs xss c
      Uni g t    -> evalFun g t
      Bin op l r -> evalOp op l r
{-# INLINE evalTree #-}

-- evaluates an operator 
evalOp :: Floating a => Op -> a -> a -> a
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mul = (*)
evalOp Div = (/)
evalOp Power = (**)
evalOp PowerAbs = \l r -> abs l ** r
evalOp AQ = \l r -> l / sqrt(1 + r*r)
{-# INLINE evalOp #-}

-- evaluates a function 
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
evalFun SqrtAbs = sqrt . abs
evalFun Cbrt = cbrt
evalFun Square = (^2)
evalFun Log = log
evalFun LogAbs = log . abs
evalFun Exp = exp
evalFun Recip = recip
evalFun Cube = (^3)
{-# INLINE evalFun #-}

-- Cubic root
cbrt :: Floating a => a -> a
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
inverseFunc Recip  = Recip
-- inverseFunc Abs    = Abs -- we assume abs(x) = sqrt(x^2) so y = sqrt(x^2) => x^2 = y^2 => x = sqrt(y^2) = x = abs(y)
inverseFunc x      = error $ show x ++ " has no support for inverse function"
{-# INLINE inverseFunc #-}

-- | evals the inverse of a function
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
evalInverse SqrtAbs = (^2)
evalInverse Square = sqrt
evalInverse Cbrt   = (^3)
evalInverse Log    = exp
evalInverse LogAbs = exp
evalInverse Exp    = log
evalInverse Abs    = abs -- we assume abs(x) = sqrt(x^2) so y = sqrt(x^2) => x^2 = y^2 => x = sqrt(y^2) = x = abs(y)
evalInverse Recip  = recip
evalInverse Cube   = cbrt
{-# INLINE evalInverse #-}

-- | evals the right inverse of an operator 
invright :: Floating a => Op -> a -> (a -> a)
invright Add v   = subtract v
invright Sub v   = (+v)
invright Mul v   = (/v)
invright Div v   = (*v)
invright Power v = (**(1/v))
invright PowerAbs v = (**(1/v))
invright AQ v = (* sqrt (1 + v*v))
{-# INLINE invright #-}

-- | evals the left inverse of an operator 
invleft :: Floating a => Op -> a -> (a -> a)
invleft Add v   = subtract v
invleft Sub v   = (+v) . negate -- y = v - r => r = v - y
invleft Mul v   = (/v)
invleft Div v   = (v/) -- y = v / r => r = v/y
invleft Power v = logBase v -- (/(log v)) . log -- y = v ^ r  log y = r log v r = log y / log v
invleft PowerAbs v = logBase v . abs
invleft AQ v = (v/)
{-# INLINE invleft #-}

-- | List of invertible functions
invertibles :: [Function]
invertibles = [Id, Sin, Cos, Tan, Tanh, ASin, ACos, ATan, ATanh, Sqrt, Square, Log, Exp, Recip]
{-# INLINE invertibles #-}
