
{-# language FlexibleInstances #-}
{-# language OverloadedStrings #-}
{-# language ImportQualifiedPost #-}
{-# language ViewPatterns #-}
module Algorithm.SRTree.Opt
--    ( optimize, sse, mse, rmse, PVector, SRMatrix, minimizeNLL, minimizeNLLWithFixedParam, minimizeGaussian, minimizeBinomial, minimizePoisson, nll, Distribution (..), gradNLL, fisherNLL, hessianNLL )
    where

import Data.SRTree ( SRTree (..), Fix(..), floatConstsToParam )
import Data.SRTree.Eval ( evalTree )
import Algorithm.SRTree.AD ( reverseModeUnique )
import Algorithm.SRTree.Likelihoods
import Debug.Trace ( trace )
import Data.SRTree.Print ( showExpr )
import Data.Massiv.Array 
import Algorithm.SRTree.NonlinearOpt
import Data.Bifunctor ( second )
import GHC.IO (unsafePerformIO)

minimizeNLL :: Distribution -> Maybe Double -> Int -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (PVector, Int)
minimizeNLL dist msErr niter xss ys tree t0
  | niter == 0 = (t0, 0)
  | n == 0     = (t0, 0)
  | n > m      = (t0, 0)
  | otherwise  = unsafePerformIO $ minimizeBFGS funAndGrad hessian niter 1e-5 t0
  -- | otherwise  = unsafePerformIO $ minimizeCG funAndGrad niter 1e-6 t0 
  where
    (Sz n)     = size t0
    (Sz m)     = size ys
    funAndGrad = second (computeAs S). gradNLL dist msErr xss ys tree
    hessian    = hessianNLL dist msErr xss ys tree

    {-
minimizeNLLWithFixedParam :: Distribution -> Maybe Double -> Int -> SRMatrix -> PVector -> Fix SRTree -> Int -> VS.Vector Double -> (VS.Vector Double, Int)
minimizeNLLWithFixedParam dist msErr niter xss ys tree ix t0
  | niter == 0 = (t0, 0)
  | n == 0     = (t0, 0)
  | n > m      = (t0, 0)
  | otherwise  = (t_opt, iters path)
  where
    (t_opt, path) = minimizeVD ConjugateFR 1e-20 niter 1e-1 1e-2 model jacob t0
    --(t_opt, path) = minimizeVD ConjugateFR 1e-20 niter 1e-16 1e-3 model jacob t0

    iters   = fst . size   
    n       = VS.length t0
    m       = VS.length ys
    model   = nll dist msErr xss ys tree
    jacob t = gradNLL dist msErr xss ys tree t VS.// [(ix, 0.0)] 

minimizeGaussian :: Int -> SRMatrix -> PVector -> Fix SRTree -> VS.Vector Double -> (VS.Vector Double, Int)
minimizeGaussian = minimizeNLL Gaussian Nothing

minimizeBinomial :: Int -> SRMatrix -> PVector -> Fix SRTree -> VS.Vector Double -> (VS.Vector Double, Int)
minimizeBinomial = minimizeNLL Bernoulli Nothing

minimizePoisson :: Int -> SRMatrix -> PVector -> Fix SRTree -> VS.Vector Double -> (VS.Vector Double, Int)
minimizePoisson = minimizeNLL Poisson Nothing
-}
