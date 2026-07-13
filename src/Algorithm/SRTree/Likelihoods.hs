{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  AlgorithV.SRTree.Likelihoods 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
-- Functions to calculate different likelihood functions, their gradient, and Hessian matrices.
--
-----------------------------------------------------------------------------
module Algorithm.SRTree.Likelihoods
  ( Distribution (..)
  , Loss (..)
  , Target
  , Columns
  , mae
  , mape
  , pinballLoss
  , buildDistLoss
  , buildLoss
  , buildPredictor
  , fisherNLL
  , getSErr
  , hessianNLL
  )
    where

import Data.SRTree
import Data.SRTree.Recursion ( cata, accu )
import Data.SRTree.Derivative (deriveByParam, deriveByVar, derivative, derivOp)
import Data.SRTree.Eval
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as VSM

import GHC.IO (unsafePerformIO)
import Data.Maybe

import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as VM
import Control.Concurrent (getNumCapabilities)
import Control.Concurrent.Async (forConcurrently)

import Debug.Trace
import Data.SRTree.Print
import Control.Monad.State.Strict
import Control.Monad.Identity

import Data.SRTree.Print
import qualified Data.Vector.Generic as G

-- | Supported distributions for negative log-likelihood.
-- | HGaussian is Gaussian with heteroscedasticity, where the error should be provided.
data Distribution = Gaussian | HGaussian | Bernoulli | Poisson | ROXY
    deriving (Show, Read, Enum, Bounded, Eq)

-- | Loss functions used to build the per-row optimization objective (see
-- 'buildLoss'), to be used by e.g. "Algorithm.SRTree.Opt". 'NLL' wraps a
-- 'Distribution' to use its negative log-likelihood as the loss --
-- including the plain \'MSE\' and \'LOG10\' losses, reached via @NLL MSE@
-- and @NLL LOG10@ respectively (kept on 'Distribution', rather than
-- duplicated here, since Haskell does not allow two data constructors
-- with the same name -- 'MSE' and 'LOG10' -- to coexist in the same
-- module).
data Loss = MSE | LOG10 | MAE | MAPE | Pinball Double | NLL Distribution
    deriving (Show, Read, Eq)

-- | Mean absolute error
mae :: Columns -> Target -> Fix SRTree -> Target -> Double
mae xss ys tree theta = let m = V.length ys in err / fromIntegral m
  where
    yhat = compile xss tree theta
    err  = V.sum . V.map abs $ ys - yhat

-- | Mean absolute percentage error
mape :: Columns -> Target -> Fix SRTree -> Target -> Double
mape xss ys tree theta = let m = V.length ys in err / fromIntegral m
  where
    yhat = compile xss tree theta
    err  = V.sum . V.map abs $ (ys - yhat) / ys

-- | Pinball (quantile) loss for a given quantile @tau@ in @(0, 1)@.
pinballLoss :: Double -> Columns -> Target -> Fix SRTree -> Target -> Double
pinballLoss tau xss ys tree theta = let m = V.length ys in err / fromIntegral m
  where
    yhat  = compile xss tree theta
    pin r = if r >= 0 then tau * r else (tau - 1) * r
    err   = V.sum . V.map pin $ ys - yhat

-- | logistic function
logistic :: Floating a => a -> a
logistic x = 1 / (1 + exp (-x))
{-# inline logistic #-}

-- | get the standard error from a Maybe Double
-- if it is Nothing, estimate from the ssr, otherwise use the current value
-- For distributions other than Gaussian, it defaults to a constant 1
getSErr :: Num a => Distribution -> a -> Maybe a -> a
getSErr Gaussian est = fromMaybe est
getSErr _        _   = const 1
{-# inline getSErr #-}

-- negation of the sum of values in a vector
negSum :: Target -> Double
negSum = negate . V.sum
{-# inline negSum #-}

checkAssumptions :: Distribution -> Maybe Target ->  Target -> Bool
checkAssumptions Gaussian  _           _  = True
checkAssumptions HGaussian (Just yErr) _  = True
checkAssumptions HGaussian Nothing     _  = False
checkAssumptions Bernoulli _           ys = V.all (\x -> x /= 0 && x /= 1) ys
checkAssumptions Poisson   _           ys = V.all (>0) ys
checkAssumptions ROXY      mYerr       ys = isJust mYerr

-- WARNING: pass tree with parameters
-- TODO: handle error similar to ROXY

-- | Builds the per-row negative log-likelihood expression for a given
-- 'Distribution', to be summed across rows (e.g. by
-- 'Algorithm.SRTree.AD.evalGradMulti') and differentiated by automatic
-- differentiation. The special variable index @-1@ refers to the target
-- ('ys') and @-2@ to the target's measurement error ('yErr'), following
-- the convention used by "Algorithm.SRTree.AD".
--
-- 'buildLoss' delegates to this function for the @'NLL' dist@ loss.
buildDistLoss :: Distribution -> Double -> Fix SRTree -> Fix SRTree
buildDistLoss Gaussian m tree =  (square(tree - var (-1)) * (e (negate (param p)))) + (((param p)))
  where
    square = Fix . Uni Square
    e      = Fix. Uni Exp
    p      = countParamsUniq tree
buildDistLoss HGaussian m tree = (tree - var (-1)) ** 2 / var (-2) + constv m * log (2*pi* var (-2))
buildDistLoss Poisson m tree   = var (-1) * log (var (-1)) + exp tree - var (-1) * tree
buildDistLoss Bernoulli m tree = log (1 + exp (negate tree)) + (1 - var (-1)) * tree
buildDistLoss ROXY m tree      = neglogP
  where
    p        = countParamsUniq tree
    f        = log (abs tree) / log 10
    fprime   = deriveByVar 0 tree / (log 10 * tree) * var 0 * log 10
    logX     = var 1
    logY     = var 2
    logXErr  = var 3
    logYErr  = var 4
    sig      = param p
    mu_gauss = param (p+1)
    w_gauss  = param (p+2)
    w_gauss2 = w_gauss ** 2
    s2       = logYErr + sig ** 2
    den      = fprime ** 2 * w_gauss2 * logXErr + s2 * (w_gauss2 + logXErr)
    neglogP  = log (2*pi)
              + log den
              + ( w_gauss2 * (f - logY) * (f - logY)
                + logXErr * (fprime *(mu_gauss - logX) + f - logY)**2
                + s2 * (logX - mu_gauss) ** 2
                ) / den

-- | Builds the per-row loss expression for a given 'Loss', to be summed
-- across rows (e.g. by 'Algorithm.SRTree.AD.evalGradMulti') and
-- differentiated by automatic differentiation. Same special variable
-- convention as 'buildDistLoss'.
buildLoss :: Loss -> Double -> Fix SRTree -> Fix SRTree
buildLoss MSE m tree           = ((tree - var (-1)) ** 2) / constv m
buildLoss LOG10 m tree         = (((log (y / tree')) / log 10) ** 2) / constv m
  where
    tree' = (tree + sqrt(tree^2 + 1e-10))
    y     = (var (-1) + sqrt(var (-1) ^ 2 + 1e-10))

buildLoss MAE m tree           = abs (tree - var (-1)) / constv m

-- | Mean absolute percentage error. A small epsilon is added to the
-- denominator's magnitude to avoid division by zero when the target is
-- (close to) zero.
buildLoss MAPE m tree          = (abs (tree - var (-1)) / (abs (var (-1)) + constv 1e-8)) / constv m

-- | Pinball (quantile) loss for a residual @r = y - yhat@:
-- @tau * r@ if @r >= 0@, @(tau - 1) * r@ otherwise. Both cases are
-- captured in closed form by @0.5 * ((2*tau - 1) * r + abs r)@, which
-- avoids branching in the symbolic tree.
buildLoss (Pinball tau) m tree = ((constv (2*tau - 1) * r + abs r) / 2) / constv m
  where r                      = var (-1) - tree

buildLoss (NLL dist) m tree    = buildDistLoss dist m tree

-- | Builds the predictor expression from a fitted model tree by applying
-- the inverse link function implied by the 'Distribution': @exp@ for
-- 'Poisson', the logistic function for 'Bernoulli', and the identity
-- otherwise.
buildPredictor :: Distribution -> Fix SRTree -> Fix SRTree
buildPredictor Poisson   tree = exp tree
buildPredictor Bernoulli tree = 1 / (1 + exp (negate tree))
buildPredictor _         tree = tree

-- | Fisher information of negative log-likelihood
fisherNLL :: Distribution -> Maybe Target -> Columns -> Target -> Fix SRTree -> Target -> Target
fisherNLL ROXY mYerr xss ys tree theta = V.generate p finiteDiff
  where
    m             = V.length ys
    p             = V.length theta
    loss          = compileLoss xss (buildDistLoss ROXY (fromIntegral m) tree) ys
    f             = loss theta
    eps           = 1e-6
    finiteDiff ix = unsafePerformIO $ do
                      theta' <- V.thaw theta
                      v <- VM.read theta' ix
                      VM.write theta' ix (v + eps)
                      thetaPlus <- V.freeze theta'
                      VM.write theta' ix (v - eps)
                      thetaMinus <- V.freeze theta'
                      let fPlus     = loss thetaPlus
                          fMinus    = loss thetaMinus
                      pure $ (fPlus + fMinus - 2*f)/(eps*eps)
fisherNLL Gaussian mYerr xss ys tree theta = V.generate p finiteDiff
  where
    m             = V.length ys
    p             = V.length theta
    loss          = compileLoss xss (buildDistLoss Gaussian (fromIntegral m) tree) ys
    f             = loss theta
    eps           = 1e-6
    finiteDiff ix = unsafePerformIO $ do
                      theta' <- V.thaw theta
                      v <- VM.read theta' ix
                      VM.write theta' ix (v + eps)
                      thetaPlus <- V.freeze theta'
                      VM.write theta' ix (v - eps)
                      thetaMinus <- V.freeze theta'
                      let fPlus     = loss thetaPlus
                          fMinus    = loss thetaMinus
                      pure $ (fPlus + fMinus - 2*f)/(eps*eps)
fisherNLL dist mYerr xss ys tree theta = V.generate p build
  where
    build ix = let dtdix   = deriveByParam ix t'
                   d2tdix2 = deriveByParam ix dtdix 
                   f'      = eval dtdix 
                   f''     = eval d2tdix2 
               in V.sum $ phi' * f'^2 - res * f''
               --case dist of
               --     Gaussian -> V.sum . (/(theta V.! (p-1))) $ phi' * f'^2 - res * f''
               --     _        -> V.sum $ phi' * f'^2 - res * f''
    m      = V.length ys
    p      = V.length theta
    t'     = fst $ floatConstsToParam tree
    eval   = \t -> compile xss t theta
    yhat   = eval t'
    res    = ys - phi
    yErr   = case mYerr of
               Nothing -> V.replicate m est
               Just e  -> e
    est    = fromIntegral (m - p)

    (phi, phi') = case dist of
                    Gaussian  -> (yhat, V.replicate m 1)
                    Bernoulli -> (logistic yhat, phi*(V.replicate m 1 - phi))
                    Poisson   -> (exp yhat, phi)

-- | Hessian of negative log-likelihood
--
-- Note, though the Fisher is just the diagonal of the return of this function
-- it is better to keep them as different functions for efficiency
hessianNLL :: Distribution -> Maybe Target -> Columns -> Target -> Fix SRTree -> Target -> Columns
hessianNLL ROXY mYerr xss ys tree theta = undefined
hessianNLL Gaussian mYerr xss ys tree theta = [V.generate p (build iy) | iy <- [0..p-1]]
  where
    build iy ix = let dtdix   = deriveByParam ix tree
                      dtdiy   = deriveByParam iy tree
                      d2tdixy = deriveByParam iy dtdix
                      fx      = eval dtdix
                      fy      = eval dtdiy
                      fxy     = eval d2tdixy
                   in if ix < p-1 && iy < p-1
                        then V.sum . (/yErr) $ fx * fy - res * fxy
                        else if ix == p-1 && iy == p-1
                               then (*0.5) . V.sum . (/ yErr ) $ res*res
                               else if ix == p-1
                                   then V.sum . (/yErr) $ res * fy
                                   else V.sum . (/yErr) $ res * fx
    m    = V.length ys
    p    = V.length theta
    yErr :: Target
    yErr = V.replicate m $ exp (theta V.! (p-1)) / est
    yhat = eval tree
    res  = ys - yhat
    eval = \t -> compile xss t theta
    est  = fromIntegral (m - p + 1)

hessianNLL dist mYerr xss ys tree theta = [V.generate p (build iy) | iy <- [0..p-1]]
  where
    build iy ix = let dtdix   = deriveByParam ix t' 
                      dtdiy   = deriveByParam iy t' 
                      d2tdixy = deriveByParam iy dtdix
                      fx      = eval dtdix 
                      fy      = eval dtdiy 
                      fxy     = eval d2tdixy 
                    in case dist of
                         Gaussian -> V.sum . (/yErr) $ phi' * fx * fy - res * fxy
                         _        -> V.sum $ phi' * fx * fy - res * fxy

    m           = V.length ys
    p           = V.length theta
    t'          = tree -- relabelParams tree -- $ floatConstsToParam tree
    eval        = \t -> compile xss t theta
    yErr        = case mYerr of
                   Nothing -> V.replicate m est
                   Just e  -> e
    est         = fromIntegral (m - p)
    yhat        = eval t'
    res         = ys - phi

    (phi, phi') = case dist of
                    Gaussian  -> (yhat, V.replicate m 1)
                    Bernoulli -> (logistic yhat, phi*(V.replicate m 1 - phi))
                    Poisson   -> (exp yhat, phi)

