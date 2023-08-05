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
         , constv
         , arity
         , getChildren
         , countNodes
         , countVarNodes
         , countConsts
         , countParams
         , countOccurrences
         , countUniqueTokens
         , numberOfVars
         , getIntConsts
         , relabelParams
         , constsToParam
         , floatConstsToParam
         , paramsToConst
         , Fix (..)
         )
         where

import Data.SRTree.Recursion ( Fix (..), cata, cataM )
import Control.Monad.State
import qualified Data.Set as S

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

-- | create a tree with a single node representing a constant value
constv :: Double -> Fix SRTree
constv x = Fix (Const x)

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
countNodes :: Num a => Fix SRTree -> a
countNodes = cata alg
  where
      alg Var   {}    = 1
      alg Param {}    = 1
      alg Const {}    = 1
      alg (Uni _ t)   = 1 + t
      alg (Bin _ l r) = 1 + l + r
{-# INLINE countNodes #-}

-- | Count the number of `Var` nodes
countVarNodes :: Num a => Fix SRTree -> a
countVarNodes = cata alg
  where
      alg Var {} = 1
      alg Param {} = 0
      alg Const {} = 0
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countVarNodes #-}

-- | Count the number of `Param` nodes
countParams :: Num a => Fix SRTree -> a
countParams = cata alg
  where
      alg Var {} = 0
      alg Param {} = 1
      alg Const {} = 0
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countParams #-}

-- | Count the number of const nodes
countConsts :: Num a => Fix SRTree -> a
countConsts = cata alg
  where
      alg Var {} = 0
      alg Param {} = 0
      alg Const {} = 1
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countConsts #-}

-- | Count the occurrences of variable indexed as `ix`
countOccurrences :: Num a => Int -> Fix SRTree -> a
countOccurrences ix = cata alg
  where
      alg (Var iy) = if ix == iy then 1 else 0
      alg Param {} = 0
      alg Const {} = 0
      alg (Uni _ t) = t
      alg (Bin _ l r) = l + r
{-# INLINE countOccurrences #-}

countUniqueTokens :: Num a => Fix SRTree -> a
countUniqueTokens = len . cata alg
  where
    len (a, b, c, d, e) = fromIntegral $ length a + length b + length c + length d + length e
    alg (Var ix)        = (mempty, mempty, S.singleton ix, mempty, mempty)
    alg (Param _)       = (mempty, mempty, mempty, S.singleton 1, mempty)
    alg (Const _)       = (mempty, mempty, mempty, mempty, S.singleton 1)
    alg (Uni f t)       = (mempty, S.singleton f, mempty, mempty, mempty) <> t
    alg (Bin op l r)    = (S.singleton op, mempty, mempty, mempty, mempty) <> l <> r
{-# INLINE countUniqueTokens #-}

numberOfVars :: Num a => Fix SRTree -> a
numberOfVars = foldr (\_ acc -> acc + 1) 0 . cata alg
  where
    alg (Uni f t)    = t
    alg (Bin op l r) = l <> r
    alg (Var ix)     = S.singleton ix
    alg _            = mempty
{-# INLINE numberOfVars #-}

getIntConsts :: Fix SRTree -> [Double]
getIntConsts = cata alg
  where
    alg (Uni f t)    = t
    alg (Bin op l r) = l <> r
    alg (Var ix)     = []
    alg (Param _)    = []
    alg (Const x)    = [x | floor x == ceiling x]
{-# INLINE getIntConsts #-}

-- | Relabel the parameters indices incrementaly starting from 0
relabelParams :: Fix SRTree -> Fix SRTree
relabelParams t = cataM leftToRight alg t `evalState` 0
  where
      -- | leftToRight (left to right) defines the sequence of processing
      leftToRight (Uni f mt)    = Uni f <$> mt;
      leftToRight (Bin f ml mr) = Bin f <$> ml <*> mr
      leftToRight (Var ix)      = pure (Var ix)
      leftToRight (Param ix)    = pure (Param ix)
      leftToRight (Const c)     = pure (Const c)

      -- | any time we reach a Param ix, it replaces ix with current state
      -- and increments one to the state.
      alg :: SRTree (Fix SRTree) -> State Int (Fix SRTree)
      alg (Var ix)    = pure $ var ix
      alg (Param ix)  = do iy <- get; modify (+1); pure (param iy)
      alg (Const c)   = pure $ Fix $ Const c
      alg (Uni f t)   = pure $ Fix (Uni f t)
      alg (Bin f l r) = pure $ Fix (Bin f l r)

-- | Change constant values to a parameter, returning the changed tree and a list
-- of parameter values
constsToParam :: Fix SRTree -> (Fix SRTree, [Double])
constsToParam = first relabelParams . cata alg
  where
      first f (x, y) = (f x, y)

      -- | If the tree already contains a parameter
      -- it will return a default value of 1.0
      -- whenever it finds a constant, it changes that
      -- to a parameter and adds its content to the singleton list
      alg (Var ix)    = (Fix $ Var ix, [])
      alg (Param ix)  = (Fix $ Param ix, [1.0])
      alg (Const c)   = (Fix $ Param 0, [c])
      alg (Uni f t)   = (Fix $ Uni f (fst t), snd t)
      alg (Bin f l r) = (Fix (Bin f (fst l) (fst r)), snd l <> snd r)

-- | Same as `constsToParam` but does not change constant values that
-- can be converted to integer without loss of precision
floatConstsToParam :: Fix SRTree -> (Fix SRTree, [Double])
floatConstsToParam = first relabelParams . cata alg
  where
      first f (x, y)          = (f x, y)
      combine f (x, y) (z, w) = (f x z, y <> w)
      isInt x                 = floor x == ceiling x

      alg (Var ix)    = (var ix, [])
      alg (Param ix)  = (param ix, [1.0])
      alg (Const c)   = if isInt c then (constv c, []) else (param 0, [c])
      alg (Uni f t)   = first (Fix . Uni f) t -- (Fix $ Uni f (fst t), snd t)
      alg (Bin f l r) = combine ((Fix .) . Bin f) l r -- (Fix (Bin f (fst l) (fst r)), snd l <> snd r)

-- | Convert the parameters into constants in the tree
paramsToConst :: [Double] -> Fix SRTree -> Fix SRTree
paramsToConst theta = cata alg
  where
      alg (Var ix)    = Fix $ Var ix
      alg (Param ix)  = Fix $ Const (theta !! ix)
      alg (Const c)   = Fix $ Const c
      alg (Uni f t)   = Fix $ Uni f t
      alg (Bin f l r) = Fix $ Bin f l r