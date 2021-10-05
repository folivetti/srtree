{-# language ConstraintKinds #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Random 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
-- Functions to generate random trees and nodes.
--
-----------------------------------------------------------------------------
module Data.SRTree.Random 
         ( HasVars
         , HasVals
         , HasFuns
         , HasEverything
         , FullParams(..)
         , RndTree
         , randomVar
         , randomConst
         , randomPow
         , randomFunction
         , randomNode
         , randomNonTerminal
         , randomTree
         , randomTreeBalanced
         )
         where

import System.Random 
import Control.Monad.State 
import Control.Monad.Reader 
import Data.Maybe (fromJust)

import Data.SRTree.Internal

{- 
data TIR ix val = TIR { _funY :: Function
                      , _p :: Sigma ix val
                      , _q :: Sigma ix val 
                      }
type Sigma ix val = [Pi ix val]
type Pi ix val    = (val, Function, [SRTree ix val])

assembleTree :: (Eq ix, Eq val, Floating val) => TIR ix val -> SRTree ix val
assembleTree (TIR f p q) = Fun f (assemble p / (1 + assemble q))
  where
    -- assemble :: Sigma ix val -> SRTree ix val
    assemble [p']    = mk p'
    assemble (p':ps) = mk p' + assemble ps

    -- mk :: Pi ix val -> SRTree ix val
    mk (v, g, ts) = Const v * Fun g (product ts)
-}

-- * Class definition of properties that a certain parameter type has.
--
-- HasVars: does `p` provides a list of the variable indices?
-- HasVals: does `p` provides a range of values for the constants?
-- HasExps: does `p` provides a range for the integral exponentes?
-- HasFuns: does `p` provides a list of allowed functions?
class HasVars p where
  _vars :: p ix val -> [ix]
class HasVals p where
  _range :: p ix val -> (val, val)
class HasExps p where
  _exponents :: p ix val -> (Int, Int)
class HasFuns p where
  _funs :: p ix val -> [Function]

-- | Constraint synonym for all properties.
type HasEverything p = (HasVars p, HasVals p, HasExps p, HasFuns p)

-- | A structure with every property
data FullParams ix val = P [ix] (val, val) (Int, Int) [Function]

instance HasVars FullParams where
  _vars (P ixs _ _ _) = ixs
instance HasVals FullParams where
  _range (P _ r _ _) = r
instance HasExps FullParams where
  _exponents (P _ _ e _) = e
instance HasFuns FullParams where
  _funs (P _ _ _ fs) = fs

-- auxiliary function to sample between False and True
toss :: StateT StdGen IO Bool
toss = state random
{-# INLINE toss #-}

-- returns a random element of a list
randomFrom :: [a] -> StateT StdGen IO a
randomFrom funs = do n <- randomRange (0, length funs - 1)
                     pure $ funs !! n
{-# INLINE randomFrom #-}

-- returns a random element within a range
randomRange :: (Ord val, Random val) => (val, val) -> StateT StdGen IO val
randomRange rng = state (randomR rng)
{-# INLINE randomRange #-}

-- Replace the child of a unary tree.
replaceChild :: SRTree ix val -> SRTree ix val -> Maybe (SRTree ix val)
replaceChild (Fun g _) t = Just $ Fun g t
replaceChild (Pow _ k) t = Just $ Pow t k
replaceChild _         _ = Nothing 
{-# INLINE replaceChild #-}

-- Replace the children of a binary tree.
replaceChildren :: SRTree ix val -> SRTree ix val -> SRTree ix val -> Maybe (SRTree ix val)
replaceChildren (Add _ _) l r     = Just $ Add l r
replaceChildren (Sub _ _) l r     = Just $ Sub l r
replaceChildren (Mul _ _) l r     = Just $ Mul l r
replaceChildren (Div _ _) l r     = Just $ Div l r
replaceChildren (Power _ _) l r   = Just $ Power l r
replaceChildren (LogBase _ _) l r = Just $ LogBase l r
replaceChildren _             _ _ = Nothing
{-# INLINE replaceChildren #-}

-- | RndTree is a Monad Transformer to generate random trees of type `SRTree ix val` 
-- given the parameters `p ix val` using the random number generator `StdGen`.
type RndTree p ix val = ReaderT (p ix val) (StateT StdGen IO) (SRTree ix val)

-- | Returns a random variable, the parameter `p` must have the `HasVars` property
randomVar :: HasVars p => RndTree p ix val
randomVar = do vars <- asks _vars
               lift $ Var <$> randomFrom vars

-- | Returns a random constant, the parameter `p` must have the `HasConst` property
randomConst :: (Ord val, Random val, HasVals p) => RndTree p ix val
randomConst = do rng <- asks _range
                 lift $ Const <$> randomRange rng

-- | Returns a random integer power node, the parameter `p` must have the `HasExps` property
randomPow :: (Ord val, Random val, HasExps p) => RndTree p ix val
randomPow = do rng <- asks _exponents
               lift $ Pow Empty <$> randomRange rng

-- | Returns a random function, the parameter `p` must have the `HasFuns` property
randomFunction :: HasFuns p => RndTree p ix val
randomFunction = do funs <- asks _funs
                    lift $ (`Fun` Empty) <$> randomFrom funs

-- | Returns a random node, the parameter `p` must have every property.
randomNode :: (Ord val, Random val, HasEverything p) => RndTree p ix val
randomNode = do
  choice <- lift $ randomRange (0, 9 :: Int)
  case choice of
    0 -> randomVar
    1 -> randomConst
    2 -> randomFunction
    3 -> randomPow
    4 -> pure $ Add Empty Empty
    5 -> pure $ Sub Empty Empty
    6 -> pure $ Mul Empty Empty
    7 -> pure $ Div Empty Empty
    8 -> pure $ Power Empty Empty
    9 -> pure $ LogBase Empty Empty

-- | Returns a random non-terminal node, the parameter `p` must have every property.
randomNonTerminal :: (Ord val, Random val, HasEverything p) => RndTree p ix val
randomNonTerminal = do
  choice <- lift $ randomRange (0, 7 :: Int)
  case choice of
    0 -> randomFunction
    1 -> randomPow
    2 -> pure $ Add Empty Empty
    3 -> pure $ Sub Empty Empty
    4 -> pure $ Mul Empty Empty
    5 -> pure $ Div Empty Empty
    6 -> pure $ Power Empty Empty
    7 -> pure $ LogBase Empty Empty
    
-- | Returns a random tree with a limited budget, the parameter `p` must have every property.
randomTree :: (Ord val, Random val, HasEverything p) => Int -> RndTree p ix val
randomTree 0      = do
  coin <- lift toss
  if coin
    then randomVar
    else randomConst
randomTree budget = do 
  node  <- randomNode
  fromJust <$> case arity node of
    0 -> pure $ Just node
    1 -> replaceChild node <$> randomTree (budget - 1)
    2 -> replaceChildren node <$> randomTree (budget `div` 2) <*> randomTree (budget `div` 2)
    
-- | Returns a random tree with a approximately a number `n` of nodes, the parameter `p` must have every property.
randomTreeBalanced :: (Ord val, Random val, HasEverything p) => Int -> RndTree p ix val
randomTreeBalanced n | n <= 1 = do
  coin <- lift toss
  if coin
    then randomVar
    else randomConst
randomTreeBalanced n = do 
  node  <- randomNonTerminal
  fromJust <$> case arity node of
    1 -> replaceChild node <$> randomTreeBalanced (n - 1)
    2 -> replaceChildren node <$> randomTreeBalanced (n `div` 2) <*> randomTreeBalanced (n `div` 2)    
