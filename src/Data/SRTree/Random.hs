{-# language ConstraintKinds #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Random 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
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

import Control.Monad.Reader (ReaderT, asks, runReaderT)
import Control.Monad.State ( MonadState(state), MonadTrans(lift), StateT )
import Data.Maybe (fromJust)
import Data.SRTree.Internal
import System.Random (Random (random, randomR), StdGen, mkStdGen)

-- * Class definition of properties that a certain parameter type has.
--
-- HasVars: does `p` provides a list of the variable indices?
-- HasVals: does `p` provides a range of values for the constants?
-- HasExps: does `p` provides a range for the integral exponentes?
-- HasFuns: does `p` provides a list of allowed functions?
class HasVars p where
  _vars :: p -> [Int]
class HasVals p where
  _range :: p -> (Double, Double)
class HasExps p where
  _exponents :: p -> (Int, Int)
class HasFuns p where
  _funs :: p -> [Function]

-- | Constraint synonym for all properties.
type HasEverything p = (HasVars p, HasVals p, HasExps p, HasFuns p)

-- | A structure with every property
data FullParams = P [Int] (Double, Double) (Int, Int) [Function]

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
replaceChild :: Fix SRTree -> Fix SRTree -> Maybe (Fix SRTree)
replaceChild (Fix (Uni f _)) t = Just $ Fix (Uni f t)
replaceChild _         _ = Nothing 
{-# INLINE replaceChild #-}

-- Replace the children of a binary tree.
replaceFixChildren :: Fix SRTree -> Fix SRTree -> Fix SRTree -> Maybe (Fix SRTree)
replaceFixChildren (Fix (Bin f _ _)) l r = Just $ Fix (Bin f l r)
replaceFixChildren _             _ _ = Nothing
{-# INLINE replaceFixChildren #-}

-- | RndTree is a Monad Transformer to generate random trees of type `SRTree ix val` 
-- given the parameters `p ix val` using the random number generator `StdGen`.
type RndTree p = ReaderT p (StateT StdGen IO) (Fix SRTree)

-- | Returns a random variable, the parameter `p` must have the `HasVars` property
randomVar :: HasVars p => RndTree p
randomVar = do vars <- asks _vars
               lift $ Fix . Var <$> randomFrom vars

-- | Returns a random constant, the parameter `p` must have the `HasConst` property
randomConst :: HasVals p => RndTree p
randomConst = do rng <- asks _range
                 lift $ Fix . Const <$> randomRange rng

-- | Returns a random integer power node, the parameter `p` must have the `HasExps` property
randomPow :: HasExps p => RndTree p
randomPow = do rng <- asks _exponents
               lift $ Fix . Bin Power 0 . Fix . Const . fromIntegral <$> randomRange rng

-- | Returns a random function, the parameter `p` must have the `HasFuns` property
randomFunction :: HasFuns p => RndTree p
randomFunction = do funs <- asks _funs
                    f <- lift $ randomFrom funs
                    lift $ pure $ Fix (Uni f 0)

-- | Returns a random node, the parameter `p` must have every property.
randomNode :: HasEverything p => RndTree p
randomNode = do
  choice <- lift $ randomRange (0, 8 :: Int)
  case choice of
    0 -> randomVar
    1 -> randomConst
    2 -> randomFunction
    3 -> randomPow
    4 -> pure . Fix $ Bin Add 0 0
    5 -> pure . Fix $ Bin Sub 0 0
    6 -> pure . Fix $ Bin Mul 0 0
    7 -> pure . Fix $ Bin Div 0 0
    8 -> pure . Fix $ Bin Power 0 0

-- | Returns a random non-terminal node, the parameter `p` must have every property.
randomNonTerminal :: HasEverything p => RndTree p
randomNonTerminal = do
  choice <- lift $ randomRange (0, 6 :: Int)
  case choice of
    0 -> randomFunction
    1 -> randomPow
    2 -> pure . Fix $ Bin Add 0 0
    3 -> pure . Fix $ Bin Sub 0 0
    4 -> pure . Fix $ Bin Mul 0 0
    5 -> pure . Fix $ Bin Div 0 0
    6 -> pure . Fix $ Bin Power 0 0
    
-- | Returns a random tree with a limited budget, the parameter `p` must have every property.
--
-- >>> let treeGen = runReaderT (randomTree 12) (P [0,1] (-10, 10) (2, 3) [Log, Exp])
-- >>> tree <- evalStateT treeGen (mkStdGen 52)
-- >>> showExpr tree
-- "(-2.7631152121655838 / Exp((x0 / ((x0 * -7.681722660704317) - Log(3.378309080134594)))))"
randomTree :: HasEverything p => Int -> RndTree p
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
    2 -> replaceFixChildren node <$> randomTree (budget `div` 2) <*> randomTree (budget `div` 2)
    
-- | Returns a random tree with a approximately a number `n` of nodes, the parameter `p` must have every property.
--
-- >>> let treeGen = runReaderT (randomTreeBalanced 10) (P [0,1] (-10, 10) (2, 3) [Log, Exp])
-- >>> tree <- evalStateT treeGen (mkStdGen 42)
-- >>> showExpr tree
-- "Exp(Log((((7.784360517385774 * x0) - (3.6412224491658223 ^ x1)) ^ ((x0 ^ -4.09764995657091) + Log(-7.710216839988497)))))"
randomTreeBalanced :: HasEverything p => Int -> RndTree p
randomTreeBalanced n | n <= 1 = do
  coin <- lift toss
  if coin
    then randomVar
    else randomConst
randomTreeBalanced n = do 
  node  <- randomNonTerminal
  fromJust <$> case arity node of
    1 -> replaceChild node <$> randomTreeBalanced (n - 1)
    2 -> replaceFixChildren node <$> randomTreeBalanced (n `div` 2) <*> randomTreeBalanced (n `div` 2)    
