{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language OverloadedStrings #-}
{-# language LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Internal 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
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
         , IndexedTree
         , NamedTree
         , Function(..)
         , Op(..)
         , param
         , var
         , constv
         , arity
         , getChildren
         , childrenOf
         , replaceChildren
         , getOperator
         , countNodes
         , countVarNodes
         , countConsts
         , countParams
         , countParamsUniq
         , countOccurrences
         , countUniqueTokens
         , numberOfVars
         , getIntConsts
         , relabelParams
         , relabelParamsOrder
         , relabelVars
         , constsToParam
         , floatConstsToParam
         , paramsToConst
         , removeProtectedOps
         , convertProtectedOps
         , Fix (..)
         )
         where

import Control.Monad.State (MonadState (get), State, evalState, modify, put)
import Data.SRTree.Recursion (Fix (..), cata, cataM)
import qualified Data.Set as S
import Data.String (IsString (..))
import Text.Read (readMaybe)
import qualified Data.IntMap as IntMap
import Data.List ( nub )
import Data.Text ( Text, pack ) 

-- | Tree structure to be used with Symbolic Regression algorithms.
-- This structure is a fixed point of a n-ary tree. 
data SRTree var val =
   Var var     -- ^ index of the variables
 | Param Int   -- ^ index of the parameter
 | Const Double -- ^ constant value, can be converted to a parameter
 -- | IConst Int   -- TODO: integer constant
 -- | RConst Ratio  -- TODO: rational constant
 | Uni Function val -- ^ univariate function
 | Bin Op val val -- ^ binary operator
 deriving (Show, Eq, Ord, Functor)

type NamedTree = SRTree Text 
type IndexedTree = SRTree Int 

-- | Supported operators
data Op = Add | Sub | Mul | Div | Power | PowerAbs | AQ
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
  | SqrtAbs
  | Cbrt
  | Square
  | Log
  | LogAbs
  | Exp
  | Recip
  | Cube
     deriving (Show, Read, Eq, Ord, Enum)

removeProtectedOps :: Fix (SRTree var) -> Fix (SRTree var) 
removeProtectedOps = cata alg 
  where 
    alg (Var ix)           = var ix
    alg (Param ix)         = param ix
    alg (Const x)          = constv x
    alg (Bin PowerAbs l r) = l ** r
    alg (Bin op l r)       = Fix $ Bin op l r
    alg (Uni SqrtAbs t)    = Fix $ Uni Sqrt t
    alg (Uni LogAbs t)     = Fix $ Uni Log t
    alg (Uni f t)          = Fix $ Uni f t
{-# INLINE removeProtectedOps #-}

convertProtectedOps :: Fix (SRTree var) -> Fix (SRTree var) 
convertProtectedOps = cata alg 
  where 
    alg (Var ix)           = var ix
    alg (Param ix)         = param ix
    alg (Const x)          = constv x
    alg (Bin PowerAbs l r) = abs l ** r
    alg (Bin op l r)       = Fix $ Bin op l r
    alg (Uni SqrtAbs t)    = sqrt (abs t)
    alg (Uni LogAbs t)     = log (abs t)
    alg (Uni f t)          = Fix $ Uni f t
{-# INLINE convertProtectedOps #-}

-- | create a tree with a single node representing a variable
var :: var -> Fix (SRTree var)
var ix = Fix (Var ix)

-- | create a tree with a single node representing a parameter
param :: Int -> Fix (SRTree var)
param ix = Fix (Param ix)

-- | create a tree with a single node representing a constant value
constv :: Double -> Fix (SRTree var)
constv x = Fix (Const x)

-- | the instance of `IsString` allows us to
-- create a tree using a more practical notation:
--
-- >>> :t  "x0" + "t0" * sin("x1" * "t1")
-- Fix SRTree
--
instance IsString (Fix IndexedTree) where 
    fromString [] = error "empty string for SRTree"
    fromString ('x':ix) = case readMaybe ix of 
                            Just iy -> Fix (Var iy)
                            Nothing -> error "wrong format for variable. It should be xi where i is an index. Ex.: \"x0\", \"x1\"."
    fromString ('t':ix) = case readMaybe ix of 
                            Just iy -> Fix (Param iy)
                            Nothing -> error "wrong format for parameter. It should be ti where i is an index. Ex.: \"t0\", \"t1\"."
    fromString _        = error "A string can represent a variable or a parameter following the format xi or ti, respectivelly, where i is the index. Ex.: \"x0\", \"t0\"."

instance IsString (Fix NamedTree) where 
    fromString ('_':xs) = Fix (Var $ pack xs)
    fromString ('t':ix) = case readMaybe ix of 
                            Just iy -> Fix (Param iy)
                            Nothing -> error "wrong format for parameter. It should be ti where i is an index. Ex.: \"t0\", \"t1\"."
    fromString _        = error "A string can represent a variable or a parameter following the format xi or ti, respectivelly, where i is the index. Ex.: \"x0\", \"t0\"."

instance Num (Fix (SRTree var)) where
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

instance Fractional (Fix (SRTree var)) where
  l / Fix (Const 1) = l
  Fix (Const c1) / Fix (Const c2) = Fix . Const $ c1/c2
  l / r                   = Fix $ Bin Div l r
  {-# INLINE (/) #-}

  recip = Fix . Uni Recip
  {-# INLINE recip #-}

  fromRational = Fix . Const . fromRational
  {-# INLINE fromRational #-}

instance Floating (Fix (SRTree var)) where
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

instance Foldable (SRTree var) where 
    foldMap f =
        \case
          Bin op l r -> f l <> f r
          Uni g t    -> f t 
          _          -> mempty 

instance Traversable (SRTree var) where 
    traverse f = 
        \case 
          Bin op l r -> Bin op <$> f l <*> f r 
          Uni g t    -> Uni g <$> f t 
          Var ix     -> pure (Var ix) 
          Param ix   -> pure (Param ix) 
          Const x    -> pure (Const x) 
    sequence =
        \case
          Bin op l r -> Bin op <$> l <*> r 
          Uni g t    -> Uni g <$> t 
          Var ix     -> pure (Var ix) 
          Param ix   -> pure (Param ix) 
          Const x    -> pure (Const x) 

-- | Arity of the current node
arity :: Fix (SRTree var) -> Int
arity = cata alg
  where
    alg Var {}      = 0
    alg Param {}    = 0
    alg Const {}    = 0
    alg Uni {}      = 1
    alg Bin {}      = 2
{-# INLINE arity #-}

-- | Get the children of a node. Returns an empty list in case of a leaf node.
--
-- >>> map showExpr . getChildren $ "x0" + 2 
-- ["x0", 2]
--
getChildren :: Fix (SRTree var) -> [Fix (SRTree var)]
getChildren (Fix (Var {})) = []
getChildren (Fix (Param {})) = []
getChildren (Fix (Const {})) = []
getChildren (Fix (Uni _ t)) = [t]
getChildren (Fix (Bin _ l r)) = [l, r]
{-# INLINE getChildren #-}

-- | Get the children of an unfixed node 
-- 
childrenOf :: SRTree v a -> [a] 
childrenOf = 
    \case 
      Uni _ t   -> [t] 
      Bin _ l r -> [l, r] 
      _         -> []

-- | replaces the children with elements from a list 
replaceChildren :: [a] -> SRTree v b -> SRTree v a
replaceChildren [l, r] (Bin op _ _) = Bin op l r
replaceChildren [t]    (Uni f _)    = Uni f t
replaceChildren _      (Var ix)     = Var ix
replaceChildren _      (Param ix)   = Param ix
replaceChildren _      (Const x)    = Const x
replaceChildren xs     n            = error "ERROR: trying to replace children with not enough elements."
{-# INLINE replaceChildren #-}

-- | returns a node containing the operator and () as children
getOperator :: SRTree v a -> SRTree v ()
getOperator (Bin op _ _) = Bin op () ()
getOperator (Uni f _)    = Uni f ()
getOperator (Var ix)     = Var ix
getOperator (Param ix)   = Param ix
getOperator (Const x)    = Const x
{-# INLINE getOperator #-}

-- | Count the number of nodes in a tree.
--
-- >>> countNodes $ "x0" + 2
-- 3
countNodes :: Num a => Fix (SRTree var) -> a
countNodes = cata alg
  where
      alg Var   {}    = 1
      alg Param {}    = 1
      alg Const {}    = 1
      alg (Uni _ t)   = 1 + t
      alg (Bin _ l r) = 1 + l + r
{-# INLINE countNodes #-}

-- | Count the number of `Var` nodes
--
-- >>> countVarNodes $ "x0" + 2 * ("x0" - sin "x1")
-- 3
countVarNodes :: Num a => Fix (SRTree var) -> a
countVarNodes = cata alg
  where
      alg Var {} = 1
      alg Param {} = 0
      alg Const {} = 0
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countVarNodes #-}

-- | Count the number of `Param` nodes
--
-- >>> countParams $ "x0" + "t0" * sin ("t1" + "x1") - "t0"
-- 3
countParams :: Num a => Fix (SRTree var) -> a
countParams = cata alg
  where
      alg Var {} = 0
      alg Param {} = 1
      alg Const {} = 0
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countParams #-}

-- | Count the unique occurrences of `Param` nodes
--
-- >>> countParams $ "x0" + "t0" * sin ("t1" + "x1") - "t0"
-- 2
countParamsUniq :: Fix (SRTree var) -> Int
countParamsUniq t = length . nub $ cata alg t
  where
      alg Var {} = []
      alg (Param ix) = [ix]
      alg Const {} = []
      alg (Uni _ t) = t
      alg (Bin _ l r) = l <> r
{-# INLINE countParamsUniq #-}

-- | Count the number of const nodes
--
-- >>> countConsts $ "x0"* 2 + 3 * sin "x0"
-- 2
countConsts :: Num a => Fix (SRTree var) -> a
countConsts = cata alg
  where
      alg Var {} = 0
      alg Param {} = 0
      alg Const {} = 1
      alg (Uni _ t) = 0 + t
      alg (Bin _ l r) = 0 + l + r
{-# INLINE countConsts #-}

-- | Count the occurrences of variable indexed as `ix`
--
-- >>> countOccurrences 0 $ "x0"* 2 + 3 * sin "x0" + "x1"
-- 2
countOccurrences :: (Num a, Eq var) => var -> Fix (SRTree var) -> a
countOccurrences ix = cata alg
  where
      alg (Var iy) = if ix == iy then 1 else 0
      alg Param {} = 0
      alg Const {} = 0
      alg (Uni _ t) = t
      alg (Bin _ l r) = l + r
{-# INLINE countOccurrences #-}

-- | counts the number of unique tokens 
--
-- >>> countUniqueTokens $ "x0" + ("x1" * "x0" - sin ("x0" ** 2))
-- 8
countUniqueTokens :: (Ord var, Num a) => Fix (SRTree var) -> a
countUniqueTokens = len . cata alg
  where
    len (a, b, c, d, e) = fromIntegral $ length a + length b + length c + length d + length e
    alg (Var ix)        = (mempty, mempty, S.singleton ix, mempty, mempty)
    alg (Param _)       = (mempty, mempty, mempty, S.singleton 1, mempty)
    alg (Const _)       = (mempty, mempty, mempty, mempty, S.singleton 1)
    alg (Uni f t)       = (mempty, S.singleton f, mempty, mempty, mempty) <> t
    alg (Bin op l r)    = (S.singleton op, mempty, mempty, mempty, mempty) <> l <> r
{-# INLINE countUniqueTokens #-}

-- | return the number of unique variables 
-- 
-- >>> numberOfVars $ "x0" + 2 * ("x0" - sin "x1")
-- 2
numberOfVars :: (Ord var, Num a) => Fix (SRTree var) -> a
numberOfVars = fromIntegral . S.size . cata alg
  where
    alg (Uni f t)    = t
    alg (Bin op l r) = l <> r
    alg (Var ix)     = S.singleton ix
    alg _            = mempty
{-# INLINE numberOfVars #-}

-- | returns the integer constants. We assume an integer constant 
-- as those values in which `floor x == ceiling x`.
--
-- >>> getIntConsts $ "x0" + 2 * "x1" ** 3 - 3.14
-- [2.0,3.0]
getIntConsts :: Fix (SRTree var) -> [Double]
getIntConsts = cata alg
  where
    alg (Uni f t)    = t
    alg (Bin op l r) = l <> r
    alg (Var ix)     = []
    alg (Param _)    = []
    alg (Const x)    = [x | floor x == ceiling x]
{-# INLINE getIntConsts #-}

-- | Relabel the parameters indices incrementaly starting from 0
--
-- >>> showExpr . relabelParams $ "x0" + "t0" * sin ("t1" + "x1") - "t0" 
-- "x0" + "t0" * sin ("t1" + "x1") - "t2" 
relabelParams :: Fix (SRTree var) -> Fix (SRTree var)
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
      alg :: SRTree var (Fix (SRTree var)) -> State Int (Fix (SRTree var))
      alg (Var ix)    = pure $ var ix
      alg (Param ix)  = do iy <- get; modify (+1); pure (param iy)
      alg (Const c)   = pure $ Fix $ Const c
      alg (Uni f t)   = pure $ Fix (Uni f t)
      alg (Bin f l r) = pure $ Fix (Bin f l r)

-- | Reorder the labels of the parameters indices
--
-- >>> showExpr . relabelParamsOrder $ "x0" + "t1" * sin ("t3" + "x1") - "t1"
-- "x0" + "t0" * sin ("t1" + "x1") - "t0"
relabelParamsOrder :: Fix (SRTree var) -> Fix (SRTree var)
relabelParamsOrder t = cataM leftToRight alg t `evalState` (IntMap.empty, 0)
  where
      -- | leftToRight (left to right) defines the sequence of processing
      leftToRight (Uni f mt)    = Uni f <$> mt;
      leftToRight (Bin f ml mr) = Bin f <$> ml <*> mr
      leftToRight (Var ix)      = pure (Var ix)
      leftToRight (Param ix)    = pure (Param ix)
      leftToRight (Const c)     = pure (Const c)

      -- | any time we reach a Param ix, it replaces ix with current state
      -- and increments one to the state.
      alg :: SRTree var (Fix (SRTree var)) -> State (IntMap.IntMap Int, Int) (Fix (SRTree var))
      alg (Var ix)    = pure $ var ix
      alg (Param ix)  = do (m, iy) <- get
                           if IntMap.member ix m
                              then pure (param $ m IntMap.! ix)
                              else do let m' = IntMap.insert ix iy m
                                      put (m', iy+1)
                                      pure (param iy)
      alg (Const c)   = pure $ Fix $ Const c
      alg (Uni f t)   = pure $ Fix (Uni f t)
      alg (Bin f l r) = pure $ Fix (Bin f l r)

-- | Relabel the parameters indices incrementaly starting from 0
--
-- >>> showExpr . relabelParams $ "x0" + "t0" * sin ("t1" + "x1") - "t0"
-- "x0" + "t0" * sin ("t1" + "x1") - "t2"
relabelVars :: Fix (SRTree Int) -> Fix (SRTree Int)
relabelVars t = cataM leftToRight alg t `evalState` 0
  where
      -- | leftToRight (left to right) defines the sequence of processing
      leftToRight (Uni f mt)    = Uni f <$> mt;
      leftToRight (Bin f ml mr) = Bin f <$> ml <*> mr
      leftToRight (Var ix)      = pure (Var ix)
      leftToRight (Param ix)    = pure (Param ix)
      leftToRight (Const c)     = pure (Const c)

      -- | any time we reach a Param ix, it replaces ix with current state
      -- and increments one to the state.
      alg :: SRTree var (Fix (SRTree Int)) -> State Int (Fix (SRTree Int))
      alg (Var ix)    = do iy <- get; modify (+1); pure (var iy)
      alg (Param ix)  = pure $ param ix
      alg (Const c)   = pure $ Fix $ Const c
      alg (Uni f t)   = pure $ Fix (Uni f t)
      alg (Bin f l r) = pure $ Fix (Bin f l r)

-- | Change constant values to a parameter, returning the changed tree and a list
-- of parameter values
--
-- >>> snd . constsToParam $ "x0" * 2 + 3.14 * sin (5 * "x1")
-- [2.0,3.14,5.0]
constsToParam :: Fix (SRTree var) -> (Fix (SRTree var), [Double])
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
--
-- >>> snd . floatConstsToParam $ "x0" * 2 + 3.14 * sin (5 * "x1")
-- [3.14]
floatConstsToParam :: Fix (SRTree var) -> (Fix (SRTree var), [Double])
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
--
-- >>> showExpr . paramsToConst [1.1, 2.2, 3.3] $ "x0" + "t0" * sin ("t1" * "x0" - "t2")
-- x0 + 1.1 * sin(2.2 * x0 - 3.3)
paramsToConst :: [Double] -> Fix (SRTree var) -> Fix (SRTree var)
paramsToConst theta = cata alg
  where
      alg (Var ix)    = Fix $ Var ix
      alg (Param ix)  = Fix $ Const (theta !! ix)
      alg (Const c)   = Fix $ Const c
      alg (Uni f t)   = Fix $ Uni f t
      alg (Bin f l r) = Fix $ Bin f l r
