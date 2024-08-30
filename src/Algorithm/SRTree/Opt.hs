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
import Data.Massiv.Array
import Data.SRTree (Fix (..), SRTree (..), floatConstsToParam, relabelParams)
import Data.SRTree.Eval (evalTree)
import qualified Data.Vector.Storable as VS

-- | minimizes the negative log-likelihood of the expression
minimizeNLL :: Distribution -> Maybe Double -> Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizeNLL dist msErr niter xss ys tree t0
  | niter == 0 = (t0, f)
  | n == 0     = (t0, f)
  | otherwise  = (fromStorableVector Seq t_opt, f)
  where
    tree'      = relabelParams $ fst $ floatConstsToParam tree
    t0'        = toStorableVector t0
    (Sz n)     = size t0
    (Sz m)     = size ys
    funAndGrad = second (toStorableVector . computeAs S) . gradNLL dist msErr xss ys tree' . fromStorableVector Seq
    (f, _)     = gradNLL dist msErr xss ys tree t0 -- if there's no parameter or no iterations

    algorithm  = LBFGS funAndGrad Nothing
    stop       = ObjectiveRelativeTolerance 1e-5 :| [MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    t_opt      = case minimizeLocal problem t0' of
                  Right sol -> solutionParams sol
                  Left e    -> t0'

-- | minimizes the likelihood assuming repeating parameters in the expression 
minimizeNLLNonUnique :: Distribution -> Maybe Double -> Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizeNLLNonUnique dist msErr niter xss ys tree t0
  | niter == 0 = (t0, f)
  | n == 0     = (t0, f)
  | otherwise  = (fromStorableVector Seq t_opt, f)
  where
    t0'        = toStorableVector t0
    (Sz n)     = size t0
    (Sz m)     = size ys
    funAndGrad = second (toStorableVector . computeAs S) . gradNLLNonUnique dist msErr xss ys tree . fromStorableVector Seq
    (f, _)     = gradNLLNonUnique dist msErr xss ys tree t0 -- if there's no parameter or no iterations

    algorithm  = LBFGS funAndGrad Nothing
    stop       = ObjectiveRelativeTolerance 1e-5 :| [MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    t_opt      = case minimizeLocal problem t0' of
                  Right sol -> solutionParams sol
                  Left e    -> t0'

-- | minimizes the function while keeping the parameter ix fixed (used to calculate the profile)
minimizeNLLWithFixedParam :: Distribution -> Maybe Double -> Int -> SRMatrix -> PVector -> Fix SRTree -> Int -> PVector -> PVector
minimizeNLLWithFixedParam dist msErr niter xss ys tree ix t0
  | niter == 0 = t0
  | n == 0     = t0
  | n > m      = t0
  | otherwise  = fromStorableVector Seq t_opt
  where
    t0'        = toStorableVector t0
    (Sz n)     = size t0
    (Sz m)     = size ys
    setTo0     = (VS.// [(ix, 0.0)])
    funAndGrad = second (setTo0 . toStorableVector . computeAs S). gradNLLNonUnique dist msErr xss ys tree . fromStorableVector Seq
    (f, _)     = gradNLLNonUnique dist msErr xss ys tree t0 -- if there's no parameter or no iterations

    algorithm  = LBFGS funAndGrad Nothing
    stop       = ObjectiveRelativeTolerance 1e-5 :| [MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    t_opt      = case minimizeLocal problem t0' of
                  Right sol -> solutionParams sol
                  Left e    -> t0'

-- | minimizes using Gaussian likelihood 
minimizeGaussian :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizeGaussian = minimizeNLL Gaussian Nothing

-- | minimizes using Binomial likelihood 
minimizeBinomial :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizeBinomial = minimizeNLL Bernoulli Nothing

-- | minimizes using Poisson likelihood 
minimizePoisson :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizePoisson = minimizeNLL Poisson Nothing

-- estimates the standard error if not provided 
estimateSErr :: Distribution -> Maybe Double -> SRMatrix -> PVector -> PVector -> Fix SRTree -> Int -> Maybe Double
estimateSErr Gaussian Nothing  xss ys theta0 t nIter = Just err
  where
    theta  = fst $ minimizeNLL Gaussian (Just 1) nIter xss ys t theta0
    (Sz m) = size ys
    (Sz p) = size theta
    ssr    = sse xss ys t theta
    err    = sqrt $ ssr / fromIntegral (m - p)
estimateSErr _        (Just s) _   _  _ _ _   = Just s
estimateSErr _        _        _   _  _ _ _   = Nothing
