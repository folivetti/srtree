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
import Data.SRTree (Fix (..), SRTree (..), floatConstsToParam, relabelParams, countNodes)
import Data.SRTree.Eval (evalTree, compMode)
import qualified Data.Vector.Storable as VS
import qualified Data.IntMap.Strict as IntMap
import Data.SRTree.Recursion

import Debug.Trace

tree2arr :: Fix SRTree -> IntMap.IntMap (Int, Int, Int, Double)
tree2arr tree = IntMap.fromList listTree
  where
    height = cata alg
      where
        alg (Var ix) = 1
        alg (Const x) = 1
        alg (Param ix) = 1
        alg (Uni _ t) = 1 + t
        alg (Bin _ l r) = 1 + max l r
    listTree = accu indexer convert tree 0

    indexer (Var ix) iy   = Var ix
    indexer (Const x) iy  = Const x
    indexer (Param ix) iy = Param ix
    indexer (Bin op l r) iy = Bin op (l, 2*iy+1) (r, 2*iy+2)
    indexer (Uni f t) iy = Uni f (t, 2*iy+1)

    convert (Var ix) iy = [(iy, (0, 0, ix, -1))]
    convert (Const x) iy = [(iy, (0, 2, -1, x))]
    convert (Param ix) iy = [(iy, (0, 1, ix, -1))]
    convert (Uni f t) iy = (iy, (1, fromEnum f, -1, -1)) : t
    convert (Bin op l r) iy = (iy, (2, fromEnum op, -1, -1)) : (l <> r)

-- | minimizes the negative log-likelihood of the expression
minimizeNLL :: Distribution -> Maybe SRMatrix -> Maybe PVector -> Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizeNLL dist mXerr mYerr niter xss ys tree t0
  | niter == 0 = (t0, f, 0)
  | n == 0     = (t0, f, 0)
  | otherwise  = (fromStorableVector compMode t_opt, f, nEvs)
  where
    tree'      = relabelParams tree -- $ fst $ floatConstsToParam tree
    t0'        = toStorableVector t0
    treeArr    = IntMap.toAscList $ tree2arr tree'
    j2ix       = IntMap.fromList $ Prelude.zip (Prelude.map fst treeArr) [0..]
    (Sz n)     = size t0
    (Sz m)     = size ys
    funAndGrad = second (toStorableVector . computeAs S) . gradNLLArr dist mXerr mYerr xss ys treeArr j2ix
    (f, _)     = gradNLL dist mXerr mYerr xss ys tree t0 -- if there's no parameter or no iterations
    --debug1     = gradNLLArr dist msErr xss ys treeArr j2ix t0
    --debug2     = gradNLL dist msErr xss ys tree t0

    algorithm  = LBFGS funAndGrad Nothing
    stop       = ObjectiveRelativeTolerance 1e-8 :| [ObjectiveAbsoluteTolerance 1e-8, MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    (t_opt, nEvs) = case minimizeLocal problem t0' of
                      Right sol -> (solutionParams sol, nEvals sol) -- traceShow (">>>>>>>", nEvals sol) $
                      Left e    -> (t0', 0)

-- | minimizes the likelihood assuming repeating parameters in the expression 
minimizeNLLNonUnique :: Distribution -> Maybe SRMatrix -> Maybe PVector -> Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizeNLLNonUnique dist mXerr mYerr niter xss ys tree t0
  | niter == 0 = (t0, f)
  | n == 0     = (t0, f)
  | otherwise  = (fromStorableVector compMode t_opt, f)
  where
    t0'        = toStorableVector t0
    (Sz n)     = size t0
    (Sz m)     = size ys
    funAndGrad = second (toStorableVector . computeAs S) . gradNLLNonUnique dist mXerr mYerr xss ys tree . fromStorableVector compMode
    (f, _)     = gradNLLNonUnique dist mXerr mYerr xss ys tree t0 -- if there's no parameter or no iterations

    algorithm  = LBFGS funAndGrad Nothing
    stop       = ObjectiveRelativeTolerance 1e-5 :| [MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    t_opt      = case minimizeLocal problem t0' of
                  Right sol -> solutionParams sol
                  Left e    -> t0'

-- | minimizes the function while keeping the parameter ix fixed (used to calculate the profile)
minimizeNLLWithFixedParam :: Distribution -> Maybe SRMatrix -> Maybe PVector -> Int -> SRMatrix -> PVector -> Fix SRTree -> Int -> PVector -> PVector
minimizeNLLWithFixedParam dist mXerr mYerr niter xss ys tree ix t0
  | niter == 0 = t0
  | n == 0     = t0
  | n > m      = t0
  | otherwise  = fromStorableVector compMode t_opt
  where
    t0'        = toStorableVector t0
    (Sz n)     = size t0
    (Sz m)     = size ys
    setTo0     = (VS.// [(ix, 0.0)])
    funAndGrad = second (setTo0 . toStorableVector . computeAs S). gradNLLNonUnique dist mXerr mYerr xss ys tree . fromStorableVector compMode
    (f, _)     = gradNLLNonUnique dist mXerr mYerr xss ys tree t0 -- if there's no parameter or no iterations

    algorithm  = LBFGS funAndGrad Nothing
    stop       = ObjectiveRelativeTolerance 1e-5 :| [MaximumEvaluations (fromIntegral niter)]
    problem    = LocalProblem (fromIntegral n) stop algorithm
    t_opt      = case minimizeLocal problem t0' of
                  Right sol -> solutionParams sol
                  Left e    -> t0'

-- | minimizes using Gaussian likelihood 
minimizeGaussian :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizeGaussian = minimizeNLL Gaussian Nothing Nothing

-- | minimizes using Binomial likelihood 
minimizeBinomial :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizeBinomial = minimizeNLL Bernoulli Nothing Nothing

-- | minimizes using Poisson likelihood 
minimizePoisson :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double, Int)
minimizePoisson = minimizeNLL Poisson Nothing Nothing

{-
-- estimates the standard error if not provided 
estimateSErr :: Distribution -> Maybe Double -> SRMatrix -> PVector -> PVector -> Fix SRTree -> Int -> Maybe Double
estimateSErr Gaussian Nothing  xss ys theta0 t nIter = Just err
  where
    (theta , _, _) = minimizeNLL Gaussian (Just 1) nIter xss ys t theta0
    (Sz m) = size ys
    (Sz p) = size theta
    ssr    = sse xss ys t theta
    err    = sqrt $ ssr / fromIntegral (m - p)
estimateSErr _        (Just s) _   _  _ _ _   = Just s
estimateSErr _        _        _   _  _ _ _   = Nothing
-}
