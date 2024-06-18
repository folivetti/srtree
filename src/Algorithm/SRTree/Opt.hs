{-# language BangPatterns #-}
{-# language FlexibleInstances #-}
{-# language OverloadedStrings #-}
{-# language ImportQualifiedPost #-}
{-# language ViewPatterns #-}
module Algorithm.SRTree.Opt
--    ( optimize, sse, mse, rmse, PVector, SRMatrix, minimizeNLL, minimizeNLLWithFixedParam, minimizeGaussian, minimizeBinomial, minimizePoisson, nll, Distribution (..), gradNLL, fisherNLL, hessianNLL )
    where

import Data.SRTree ( SRTree (..), Fix(..), floatConstsToParam, relabelParams )
import Data.SRTree.Eval ( evalTree )
import Algorithm.SRTree.AD ( reverseModeUnique )
import Algorithm.SRTree.Likelihoods
import Debug.Trace ( trace )
import Data.SRTree.Print ( showExpr )
import Data.Massiv.Array 
import Algorithm.SRTree.NonlinearOpt
import Data.Bifunctor ( second, bimap )
import Control.Monad.ST
import qualified Data.Vector.Storable as VS
import Debug.Trace ( trace )

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

minimizeGaussian :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizeGaussian = minimizeNLL Gaussian Nothing

minimizeBinomial :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizeBinomial = minimizeNLL Bernoulli Nothing

minimizePoisson :: Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Double)
minimizePoisson = minimizeNLL Poisson Nothing

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
