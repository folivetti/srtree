{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Internal 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Expression tree for Symbolic Regression
--
-----------------------------------------------------------------------------

module Data.SRTree.Internal
         ( SRTree(..)
         , Function(..)
         , Op(..)
         , param
         , var
         , arity
         , getChildren
         , countNodes
         , countVarNodes
         , countConsts
         , countParams
         , countOccurrences
         , deriveBy
         , deriveByVar
         , deriveByParam
         , derivative
         , forwardMode
         , gradParamsFwd
         , gradParamsRev
         , evalFun
         , evalOp
         , inverseFunc
         , evalTree
         , relabelParams
         , constsToParam
         , floatConstsToParam
         , paramsToConst
         , Fix (..)
         )
         where

import Data.SRTree.Recursion ( Fix (..), cata, mutu, accu, cataM )

import qualified Data.Vector as V
import Data.Vector ((!))
import Control.Monad.State
import qualified Data.DList as DL
import Data.Bifunctor (second)

import Debug.Trace (trace)

-- | Tree structure to be used with Symbolic Regression algorithms.
-- This structure is a fixed point of a n-ary tree. 
data SRTree val =
   Var Int     -- ^ index of the variables
 | Param Int   -- ^ index of the parameter
 | Const Double -- ^ constant value, can be converted to a parameter
 | Uni Function val -- ^ univariate function
 | Bin Op val val -- ^ binary operator
 deriving (Show, Eq, Ord, Functor)

-- | Supported operators
data Op = Add | Sub | Mul | Div | Power
    deriving (Show, Read, Eq, Ord, Enum)

-- | Supported functions
data Function =
    Id
  | Abs
  | Sin
  | Cos
  | Tan
  | Sinh
  | Cosh
  | Tanh
  | ASin
  | ACos
  | ATan
  | ASinh
  | ACosh
  | ATanh
  | Sqrt
  | Cbrt
  | Square
  | Log
  | Exp
     deriving (Show, Read, Eq, Ord, Enum)

-- | create a tree with a single node representing a variable
var :: Int -> Fix SRTree
var ix = Fix (Var ix)

-- | create a tree with a single node representing a parameter
param :: Int -> Fix SRTree
param ix = Fix (Param ix)

instance Num (Fix SRTree) where
  Fix (Const 0) + r = r
  l + Fix (Const 0) = l
  Fix (Const c1) + Fix (Const c2) = Fix . Const $ c1 + c2
  l + r                   = Fix $ Bin Add l r
  {-# INLINE (+) #-}

  l - Fix (Const 0) = l
  Fix (Const 0) - r = negate r
  Fix (Const c1) - Fix (Const c2) = Fix . Const $ c1 - c2
  l - r                   = Fix $ Bin Sub l r
  {-# INLINE (-) #-}

  Fix (Const 0) * _ = Fix (Const 0)
  _ * Fix (Const 0) = Fix (Const 0)
  Fix (Const 1) * r = r
  l * Fix (Const 1) = l
  Fix (Const c1) * Fix (Const c2) = Fix . Const $ c1 * c2
  l * r                   = Fix $ Bin Mul l r
  {-# INLINE (*) #-}

  abs = Fix . Uni Abs
  {-# INLINE abs #-}

  negate (Fix (Const x)) = Fix $ Const (negate x)
  negate t         = Fix (Const (-1)) * t
  {-# INLINE negate #-}

  signum t    = case t of
                  Fix (Const x) -> Fix . Const $ signum x
                  _       -> Fix (Const 0)
  fromInteger x = Fix $ Const (fromInteger x)
  {-# INLINE fromInteger #-}

instance Fractional (Fix SRTree) where
  l / Fix (Const 1) = l
  Fix (Const c1) / Fix (Const c2) = Fix . Const $ c1/c2
  l / r                   = Fix $ Bin Div l r
  {-# INLINE (/) #-}

  fromRational = Fix . Const . fromRational
  {-# INLINE fromRational #-}

instance Floating (Fix SRTree) where
  pi      = Fix $ Const  pi
  {-# INLINE pi #-}
  exp     = Fix . Uni Exp
  {-# INLINE exp #-}
  log     = Fix . Uni Log
  {-# INLINE log #-}
  sqrt    = Fix . Uni Sqrt
  {-# INLINE sqrt #-}
  sin     = Fix . Uni Sin
  {-# INLINE sin #-}
  cos     = Fix . Uni Cos
  {-# INLINE cos #-}
  tan     = Fix . Uni Tan
  {-# INLINE tan #-}
  asin    = Fix . Uni ASin
  {-# INLINE asin #-}
  acos    = Fix . Uni ACos
  {-# INLINE acos #-}
  atan    = Fix . Uni ATan
  {-# INLINE atan #-}
  sinh    = Fix . Uni Sinh
  {-# INLINE sinh #-}
  cosh    = Fix . Uni Cosh
  {-# INLINE cosh #-}
  tanh    = Fix . Uni Tanh
  {-# INLINE tanh #-}
  asinh   = Fix . Uni ASinh
  {-# INLINE asinh #-}
  acosh   = Fix . Uni ACosh
  {-# INLINE acosh #-}
  atanh   = Fix . Uni ATanh
  {-# INLINE atanh #-}

  l ** Fix (Const 1) = l
  l ** Fix (Const 0) = Fix (Const 1)
  l ** r  = Fix $ Bin Power l r
  {-# INLINE (**) #-}

  logBase l (Fix (Const 1)) = Fix (Const 0)
  logBase l r = log l / log r
  {-# INLINE logBase #-}

-- | Arity of the current node
arity :: Fix SRTree -> Int
arity = cata alg
  where
    alg Var {}      = 0
    alg Param {}    = 0
    alg Const {}    = 0
    alg Uni {}      = 1
    alg Bin {}      = 2
{-# INLINE arity #-}

-- | Get the children of a node. Returns an empty list in case of a leaf node.
getChildren :: Fix SRTree -> [Fix SRTree]
getChildren (Fix (Var {})) = []
getChildren (Fix (Param {})) = []
getChildren (Fix (Const {})) = []
getChildren (Fix (Uni _ t)) = [t]
getChildren (Fix (Bin _ l r)) = [l, r]
{-# INLINE getChildren #-}

-- | Count the number of nodes in a tree.
countNodes :: Fix SRTree -> Int
countNodes = cata alg
  where
      alg Var {} = 1
      alg Param {} = 1
      alg Const {} = 1
      alg (Uni _ t) = 1 + t
      alg (Bin _ l r) = 1 + l + r
{-# INLINE countNodes #-}

-- | Count the number of `Var` nodes
countVarNodes :: Fix SRTree -> Int
countVarNodes = cata alg
  where
      alg Var {} = 1
      alg Param {} = 0
      alg Const {} = 0
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countVarNodes #-}

-- | Count the number of `Param` nodes
countParams :: Fix SRTree -> Int
countParams = cata alg
  where
      alg Var {} = 0
      alg Param {} = 1
      alg Const {} = 0
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countParams #-}

-- | Count the number of const nodes
countConsts :: Fix SRTree -> Int
countConsts = cata alg
  where
      alg Var {} = 0
      alg Param {} = 0
      alg Const {} = 1
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countConsts #-}

-- | Count the occurrences of variable indexed as `ix`
countOccurrences :: Int -> Fix SRTree -> Int
countOccurrences ix = cata alg
  where
      alg (Var iy) = if ix == iy then 1 else 0
      alg Param {} = 0
      alg Const {} = 0
      alg (Uni _ t) = t
      alg (Bin _ l r) = l + r
{-# INLINE countOccurrences #-}

-- | Evaluates the tree given a vector of variable values, a vector of parameter values and a function that takes a Double and change to whatever type the variables have. This is useful when working with datasets of many values per variables.
evalTree :: (Num a, Floating a) => V.Vector a -> V.Vector Double -> (Double -> a) -> Fix SRTree -> a
evalTree xss params f = cata alg
  where
      alg (Var ix) = xss ! ix
      alg (Param ix) = f $ params ! ix
      alg (Const c) = f c
      alg (Uni g t) = evalFun g t
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
inverseFunc Tanh   = ATanh
inverseFunc ASin   = Sin
inverseFunc ACos   = Cos
inverseFunc ATan   = Tan
inverseFunc ATanh  = Tanh
inverseFunc Sqrt   = Square
inverseFunc Square = Sqrt
inverseFunc Log    = Exp
inverseFunc Exp    = Log
inverseFunc x      = error $ show x ++ " has no support for inverse function"
{-# INLINE inverseFunc #-}

-- | Creates the symbolic partial derivative of a tree by variable `dx` (if `p` is `False`)
-- or parameter `dx` (if `p` is `True`).
deriveBy :: Bool -> Int -> Fix SRTree -> Fix SRTree
deriveBy p dx = fst (mutu alg1 alg2)
  where
      alg1 (Var ix) = if not p && ix == dx then 1 else 0
      alg1 (Param ix) = if p && ix == dx then 1 else 0
      alg1 (Const _) = 0
      alg1 (Uni f t) = derivative f (snd t) * fst t
      alg1 (Bin Add l r) = fst l + fst r
      alg1 (Bin Sub l r) = fst l - fst r
      alg1 (Bin Mul l r) = fst l * snd r + snd l * fst r
      alg1 (Bin Div l r) = (fst l * snd r - snd l * fst r) / snd r ** 2
      alg1 (Bin Power l r) = snd l ** (snd r - 1) * (snd r * fst l + snd l * log (snd l) * fst r)

      alg2 (Var ix) = var ix
      alg2 (Param ix) = param ix
      alg2 (Const c) = Fix (Const c)
      alg2 (Uni f t) = Fix (Uni f $ snd t)
      alg2 (Bin f l r) = Fix (Bin f (snd l) (snd r))

newtype Tape a = Tape { untape :: [a] } deriving (Show, Functor)

instance Num a => Num (Tape a) where
  (Tape x) + (Tape y) = Tape $ zipWith (+) x y
  (Tape x) - (Tape y) = Tape $ zipWith (-) x y
  (Tape x) * (Tape y) = Tape $ zipWith (*) x y
  abs (Tape x) = Tape (map abs x)
  signum (Tape x) = Tape (map signum x)
  fromInteger x = Tape [fromInteger x]
  negate (Tape x) = Tape $ map (*(-1)) x
instance Floating a => Floating (Tape a) where
  pi = Tape [pi]
  exp (Tape x) = Tape (map exp x)
  log (Tape x) = Tape (map log x)
  sqrt (Tape x) = Tape (map sqrt x)
  sin (Tape x) = Tape (map sin x)
  cos (Tape x) = Tape (map cos x)
  tan (Tape x) = Tape (map tan x)
  asin (Tape x) = Tape (map asin x)
  acos (Tape x) = Tape (map acos x)
  atan (Tape x) = Tape (map atan x)
  sinh (Tape x) = Tape (map sinh x)
  cosh (Tape x) = Tape (map cosh x)
  tanh (Tape x) = Tape (map tanh x)
  asinh (Tape x) = Tape (map asinh x)
  acosh (Tape x) = Tape (map acosh x)
  atanh (Tape x) = Tape (map atanh x)
  (Tape x) ** (Tape y) = Tape $ zipWith (**) x y
instance Fractional a => Fractional (Tape a) where
  fromRational x = Tape [fromRational x]
  (Tape x) / (Tape y) = Tape $ zipWith (/) x y
  recip (Tape x) = Tape $ map recip x

-- | Calculates the numerical derivative of a tree using forward mode
-- provided a vector of variable values `xss`, a vector of parameter values `theta` and
-- a function that changes a Double value to the type of the variable values.
forwardMode :: (Show a, Num a, Floating a) => V.Vector a -> V.Vector Double -> (Double -> a) -> Fix SRTree -> [a]
forwardMode xss theta f = untape . fst (mutu alg1 alg2)
  where
      n = V.length theta
      repMat v = Tape $ replicate n v
      zeroes = repMat $ f 0
      twos  = repMat $ f 2
      tapeXs = [repMat $ xss ! ix | ix <- [0 .. V.length xss - 1]]
      tapeTheta = [repMat $ f (theta ! ix) | ix <- [0 .. n - 1]]
      paramVec = [ Tape [if ix==iy then f 1 else f 0 | iy <- [0 .. n-1]] | ix <- [0 .. n-1] ]

      alg1 (Var ix)        = zeroes
      alg1 (Param ix)      = paramVec !! ix
      alg1 (Const _)       = zeroes
      alg1 (Uni f t)       = derivative f (snd t) * fst t
      alg1 (Bin Add l r)   = fst l + fst r
      alg1 (Bin Sub l r)   = fst l - fst r
      alg1 (Bin Mul l r)   = (fst l * snd r) + (snd l * fst r)
      alg1 (Bin Div l r)   = ((fst l * snd r) - (snd l * fst r)) / snd r ** twos
      alg1 (Bin Power l r) = snd l ** (snd r - 1) * ((snd r * fst l) + (snd l * log (snd l) * fst r))

      alg2 (Var ix)     = tapeXs !! ix
      alg2 (Param ix)   = tapeTheta !! ix
      alg2 (Const c)    = repMat $ f c
      alg2 (Uni g t)    = fmap (evalFun g) (snd t)
      alg2 (Bin op l r) = evalOp op (snd l) (snd r)

-- | The function `gradParams` calculates the numerical gradient of the tree and evaluates the tree at the same time. It assumes that each parameter has a unique occurrence in the expression. This should be significantly faster than `forwardMode`.
gradParamsFwd  :: (Show a, Num a, Floating a) => V.Vector a -> V.Vector Double -> (Double -> a) -> Fix SRTree -> (a, [a])
gradParamsFwd xss theta f = second DL.toList . cata alg
  where
      n = V.length theta

      alg (Var ix)        = (xss ! ix, DL.empty)
      alg (Param ix)      = (f $ theta ! ix, DL.singleton 1)
      alg (Const c)       = (f c, DL.empty)
      alg (Uni f (v, gs)) = let v' = evalFun f v
                                dv = derivative f v
                             in (v', DL.map (*dv) gs)
      alg (Bin Add (v1, l) (v2, r)) = (v1+v2, DL.append l r)
      alg (Bin Sub (v1, l) (v2, r)) = (v1-v2, DL.append l (DL.map negate r))
      alg (Bin Mul (v1, l) (v2, r)) = (v1*v2, DL.append (DL.map (*v2) l) (DL.map (*v1) r))
      alg (Bin Div (v1, l) (v2, r)) = let dv = (-v1/v2^2) 
                                       in (v1/v2, DL.append (DL.map (/v2) l) (DL.map (*dv) r))
      alg (Bin Power (v1, l) (v2, r)) = let dv1 = v1 ** (v2 - 1)
                                            dv2 = v1 * log v1
                                         in (v1 ** v2, DL.map (*dv1) (DL.append (DL.map (*v2) l) (DL.map (*dv2) r)))

data TupleF a b = S a | T a b | B a b b deriving Functor -- hi, I'm a tree
type Tuple a = Fix (TupleF a)

gradParamsRev  :: forall a . (Show a, Num a, Floating a) => V.Vector a -> V.Vector Double -> (Double -> a) -> Fix SRTree -> (a, [a])
gradParamsRev xss theta f t = (getTop fwdMode, DL.toList g)
  where
      fwdMode = cata forward t
      g = accu reverse combine t (1, fwdMode)

      oneTpl x  = Fix $ S x
      tuple x y = Fix $ T x y
      branch x y z = Fix $ B x y z
      getTop (Fix (S x)) = x
      getTop (Fix (T x y)) = x
      getTop (Fix (B x y z)) = x
      unCons (Fix (T x y)) = y
      getBranches (Fix (B x y z)) = (y,z)

      forward (Var ix)     = oneTpl (xss ! ix)
      forward (Param ix)   = oneTpl (f $ theta ! ix)
      forward (Const c)    = oneTpl (f c)
      forward (Uni f t)    = let v = getTop t
                              in tuple (evalFun f v) t
      forward (Bin op l r) = let vl = getTop l
                                 vr = getTop r
                              in branch (evalOp op vl vr) l r

      reverse (Var ix)     (dx,    _)        = Var ix
      reverse (Param ix)   (dx,    _)        = Param ix
      reverse (Const v)    (dx,    _)        = Const v
      reverse (Uni f t)    (dx, unCons -> v) = Uni f (t, (dx * (derivative f $ getTop v), v))
      reverse (Bin op l r) (dx, getBranches -> (vl, vr)) = let (dxl, dxr) = diff op dx (getTop vl) (getTop vr)
                                                            in Bin op (l, (dxl, vl)) (r, (dxr, vr))

      diff Add dx vl vr = (dx, dx)
      diff Sub dx vl vr = (dx, negate dx)
      diff Mul dx vl vr = (dx * vr, dx * vl)
      diff Div dx vl vr = (dx / vr, dx * (-vl/vr^2))
      diff Power dx vl vr = let dxl = dx * vl ** (vr - 1)
                                dv2 = vl * log vl
                             in (dxl * vr, dxl * dv2)

      combine (Var ix)     s = DL.empty
      combine (Param ix)   s = DL.singleton $ fst s
      combine (Const c)    s = DL.empty
      combine (Uni _ gs)   s = gs
      combine (Bin op l r) s = DL.append l r

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

-- | Symbolic derivative by a variable
deriveByVar :: Int -> Fix SRTree -> Fix SRTree
deriveByVar = deriveBy False

-- | Symbolic derivative by a parameter
deriveByParam :: Int -> Fix SRTree -> Fix SRTree
deriveByParam = deriveBy True

-- | Relabel the parameters incrementaly starting from 0
relabelParams :: Fix SRTree -> Fix SRTree
relabelParams t = cataM lTor alg t `evalState` 0
  where
      lTor (Uni f mt) = Uni f <$> mt;
      lTor (Bin f ml mr) = Bin f <$> ml <*> mr
      lTor (Var ix) = pure (Var ix)
      lTor (Param ix) = pure (Param ix)
      lTor (Const c) = pure (Const c)

      alg :: SRTree (Fix SRTree) -> State Int (Fix SRTree)
      alg (Var ix) = pure $ var ix
      alg (Param ix) = do iy <- get; modify (+1); pure (param iy)
      alg (Const c) = pure $ Fix $ Const c
      alg (Uni f t) = pure $ Fix (Uni f t)
      alg (Bin f l r) = pure $ Fix (Bin f l r)

-- | Change constant values to a parameter, returning the changed tree and a list
-- of parameter values
constsToParam :: Fix SRTree -> (Fix SRTree, [Double])
constsToParam = first relabelParams . cata alg
  where
      first f (x, y) = (f x, y)

      alg (Var ix) = (Fix $ Var ix, [])
      alg (Param ix) = (Fix $ Param ix, [1.0])
      alg (Const c) = (Fix $ Param 0, [c])
      alg (Uni f t) = (Fix $ Uni f (fst t), snd t)
      alg (Bin f l r) = (Fix (Bin f (fst l) (fst r)), snd l <> snd r)

-- | Same as `constsToParam` but does not change constant values that
-- can be converted to integer without loss of precision
floatConstsToParam :: Fix SRTree -> (Fix SRTree, [Double])
floatConstsToParam = first relabelParams . cata alg
  where
      first f (x, y) = (f x, y)

      alg (Var ix) = (Fix $ Var ix, [])
      alg (Param ix) = (Fix $ Param ix, [1.0])
      alg (Const c) = if floor c == ceiling c then (Fix $ Const c, []) else (Fix $ Param 0, [c])
      alg (Uni f t) = (Fix $ Uni f (fst t), snd t)
      alg (Bin f l r) = (Fix (Bin f (fst l) (fst r)), snd l <> snd r)

-- | Convert the parameters into constants in the tree
paramsToConst :: [Double] -> Fix SRTree -> Fix SRTree
paramsToConst theta = cata alg
  where
      alg (Var ix) = Fix $ Var ix
      alg (Param ix) = Fix $ Const (theta !! ix)
      alg (Const c) = Fix $ Const c
      alg (Uni f t) = Fix $ Uni f t
      alg (Bin f l r) = Fix $ Bin f l r
