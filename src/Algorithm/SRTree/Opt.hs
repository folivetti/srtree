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
import Data.Massiv.Array
import Data.SRTree (Fix (..), SRTree (..), floatConstsToParam, relabelParams, countNodes, convertProtectedOps)
import Data.SRTree.Eval (evalTree, compMode)
import qualified Data.Vector.Storable as VS
import qualified Data.IntMap.Strict as IntMap
import Data.SRTree.Recursion

import Debug.Trace



-- | minimizes the negative log-likelihood of the expression
minimizeNLL' :: (ObjectiveD -> (Maybe VectorStorage) -> LocalAlgorithm) -> Distribution -> Maybe PVector -> Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizeNLL' alg dist mYerr niter xss ys tree t0
  | niter == 0 = (t0, f, 0)
  | n == 0     = (t0, f, 0)
  | otherwise  = (t_opt', nll dist mYerr xss ys tree t_opt', nEvs)
  where
    tree'      = buildNLL dist (fromIntegral m) tree -- convertProtectedOps
    t0'        = toStorableVector t0
    treeArr    = IntMap.toAscList $ tree2arr tree'
    j2ix       = IntMap.fromList $ Prelude.zip (Prelude.map fst treeArr) [0..]
    (Sz n)     = size t0
    (Sz m)     = size ys
    funAndGrad = gradNLLGraph dist xss ys mYerr tree' -- second (toStorableVector . computeAs S) . gradNLLArr dist xss ys mYerr treeArr j2ix

    (f, _)     = gradNLLGraph dist xss ys mYerr tree' t0' -- if there's no parameter or no iterations
    -- gradNLL dist mYerr xss ys tree t0
    --debug1     = gradNLLArr dist msErr xss ys treeArr j2ix t0
    --debug2     = gradNLL dist msErr xss ys tree t0

    algorithm  = alg funAndGrad (Just $ VectorStorage $ fromIntegral n) -- alg funAndGrad Nothing -- PRAXIS (fst . funAndGrad) [] Nothing -- TNEWTON funAndGrad Nothing
    stop       = ObjectiveRelativeTolerance 1e-6 :| [ObjectiveAbsoluteTolerance 1e-6, MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    (t_opt, nEvs) = case minimizeLocal problem t0' of
                      Right sol -> (solutionParams sol, nEvals sol) -- traceShow (">>>>>>>", nEvals sol) $
                      Left e    -> (t0', 0)
    t_opt'      = fromStorableVector compMode t_opt
    debugGrad t = let g1 = gradNLL dist mYerr xss ys tree . fromStorableVector compMode $ t
                      g2 = gradNLLArr dist xss ys mYerr treeArr j2ix t
                      g3 = gradNLLGraph dist xss ys mYerr tree' t
                  in traceShow (t, g1, g2, g3) $ g3 -- second (toStorableVector . computeAs S) g2

minimizeNLL :: Distribution -> Maybe PVector -> Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizeNLL = minimizeNLL' TNEWTON

-- | minimizes the function while keeping the parameter ix fixed (used to calculate the profile)
minimizeNLLWithFixedParam' :: (ObjectiveD -> (Maybe VectorStorage) -> LocalAlgorithm) -> Distribution -> Maybe PVector -> Int -> SRMatrix -> PVector -> Fix SRTree -> Int -> PVector -> PVector
minimizeNLLWithFixedParam' alg dist mYerr niter xss ys tree ix t0
  | niter == 0 = t0
  | n == 0     = t0
  | otherwise  = t_opt'
  where
    tree'      = buildNLL dist (fromIntegral m) tree -- relabelParams
    t0'        = toStorableVector t0
    treeArr    = IntMap.toAscList $ tree2arr tree'
    j2ix       = IntMap.fromList $ Prelude.zip (Prelude.map fst treeArr) [0..]
    (Sz n)     = size t0
    (Sz m)     = size ys
    setTo0     = (VS.// [(ix, 0.0)])
    funAndGrad = second (setTo0 . toStorableVector . computeAs S) . gradNLLArr dist xss ys mYerr treeArr j2ix

    (f, _)     = gradNLL dist mYerr xss ys tree t0 -- if there's no parameter or no iterations

    algorithm  = alg funAndGrad Nothing -- PRAXIS (fst . funAndGrad) [] Nothing -- TNEWTON funAndGrad Nothing
    stop       = ObjectiveRelativeTolerance 1e-8 :| [ObjectiveAbsoluteTolerance 1e-8, MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    (t_opt, nEvs) = case minimizeLocal problem t0' of
                      Right sol -> (solutionParams sol, nEvals sol) -- traceShow (">>>>>>>", nEvals sol) $
                      Left e    -> (t0', 0)
    t_opt'      = fromStorableVector compMode t_opt

minimizeNLLWithFixedParam = minimizeNLLWithFixedParam' TNEWTON

-- | minimizes using Gaussian likelihood 
minimizeGaussian :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizeGaussian = minimizeNLL Gaussian Nothing

-- | minimizes using Binomial likelihood 
minimizeBinomial :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizeBinomial = minimizeNLL Bernoulli Nothing

-- | minimizes using Poisson likelihood 
minimizePoisson :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizePoisson = minimizeNLL Poisson Nothing
