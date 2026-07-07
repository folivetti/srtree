{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.SRTree.Opt 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
-- Functions to optimize the parameters of an expression.
--
-----------------------------------------------------------------------------
module Algorithm.SRTree.Opt
    where

import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.NonlinearOpt
import Data.Bifunctor (bimap, second)
import Data.SRTree (Fix (..), SRTree (..), floatConstsToParam, relabelParams, countNodes, convertProtectedOps)
import Data.SRTree.Eval
import Algorithm.SRTree.AD

import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Unboxed.Mutable as VM
import qualified Data.Vector.Generic as G

import qualified Data.IntMap.Strict as IntMap
import Data.SRTree.Recursion
import Control.Monad.State.Strict
import Control.Monad.Identity
import Algorithm.SRTree.ReverseModeAcc

import Debug.Trace

minimizeNLLWith :: (VS.Vector Double -> (Double, VS.Vector Double)) -> (ObjectiveD -> (Maybe VectorStorage) -> LocalAlgorithm) -> Int -> Target -> (Target, Double, Int)
minimizeNLLWith funAndGrad alg niter t0
  | niter == 0 = (t0, f, 0)
  | n == 0     = (t0, f, 0)
  | otherwise  = (t_opt', fst (funAndGrad t_opt), nEvs)
  where
    t0'        = G.convert t0
    n          = V.length t0

    (f, _)     = funAndGrad t0' -- if there's no parameter or no iterations

    algorithm  = alg funAndGrad (Just $ VectorStorage $ fromIntegral n)
    stop       = ObjectiveRelativeTolerance 1e-6 :| [ObjectiveAbsoluteTolerance 1e-6, MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    (t_opt, nEvs) = case minimizeLocal problem t0' of
                      Right sol -> (solutionParams sol, nEvals sol)
                      Left e    -> (t0', 0)
    t_opt'      = G.convert t_opt
{-# INLINE minimizeNLLWith #-}

-- | minimizes the negative log-likelihood of the expression
minimizeNLL' :: (ObjectiveD -> (Maybe VectorStorage) -> LocalAlgorithm) -> Distribution -> Maybe Target -> Int -> Columns -> Target -> Fix SRTree -> Target -> (Target, Double, Int)
minimizeNLL' alg dist mYerr niter xss ys tree t0 = minimizeNLLWith funAndGrad alg niter t0
  where
    m          = V.length ys
    tree'      = buildNLL dist (fromIntegral m) tree
    ct         = compileTreeMulti xss ys mYerr tree'
    funAndGrad = evalGradMulti ct

-- | minimizes the negative log-likelihood of the expression
minimizeNLLAcc' :: (ObjectiveD -> (Maybe VectorStorage) -> LocalAlgorithm) -> Distribution -> Maybe Target -> Int -> Columns -> Target -> Fix SRTree -> Target -> (Target, Double, Int)
minimizeNLLAcc' alg dist mYerr niter xss ys tree t0 = minimizeNLLWith funAndGrad alg niter t0
  where
    m          = V.length ys
    tree'      = buildNLL dist (fromIntegral m) tree
    ct         = compileTree xss ys mYerr tree'
    funAndGrad = compileAccelerateTree ct xss ys

minimizeNLL :: Distribution -> Maybe Target -> Int -> Columns -> Target -> Fix SRTree -> Target -> (Target, Double, Int)
minimizeNLL = minimizeNLL' TNEWTON

minimizeNLLAcc :: Distribution -> Maybe Target -> Int -> Columns -> Target -> Fix SRTree -> Target -> (Target, Double, Int)
minimizeNLLAcc = minimizeNLLAcc' TNEWTON

-- | minimizes the function while keeping the parameter ix fixed (used to calculate the profile)
minimizeNLLWithFixedParam' :: (ObjectiveD -> (Maybe VectorStorage) -> LocalAlgorithm) -> Distribution -> Maybe Target -> Int -> Columns -> Target -> Fix SRTree -> Int -> Target -> Target
minimizeNLLWithFixedParam' alg dist mYerr' niter xss' ys' tree ix t0 = t
  where
    m          = V.length ys'
    tree'      = buildNLL dist (fromIntegral m) tree
    ct         = compileTreeMulti xss' ys' mYerr' tree'
    funAndGrad = second (VS.// [(ix, 0.0)]) . evalGradMulti ct
    (t,_,_)    = minimizeNLLWith funAndGrad alg niter t0

minimizeNLLWithFixedParam = minimizeNLLWithFixedParam' TNEWTON

-- | minimizes using Gaussian likelihood 
minimizeGaussian :: Int -> Columns -> Target -> Fix SRTree -> Target -> (Target, Double, Int)
minimizeGaussian = minimizeNLL Gaussian Nothing

-- | minimizes using Binomial likelihood 
minimizeBinomial :: Int -> Columns -> Target -> Fix SRTree -> Target -> (Target, Double, Int)
minimizeBinomial = minimizeNLL Bernoulli Nothing

-- | minimizes using Poisson likelihood 
minimizePoisson :: Int -> Columns -> Target -> Fix SRTree -> Target -> (Target, Double, Int)
minimizePoisson = minimizeNLL Poisson Nothing
