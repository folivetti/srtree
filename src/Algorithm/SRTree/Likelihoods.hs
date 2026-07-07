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
  , Target
  , Columns
  , sse
  , mse
  , rmse
  , r2
  , nll
  , predict
  , buildNLL
  , gradNLL
  , fisherNLL
  , getSErr
  , hessianNLL
  , tree2arr
  )
    where

import Data.Maybe (fromMaybe)
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

-- | Supported distributions for negative log-likelihood
-- MSE refers to mean squared error
-- HGaussian is Gaussian with heteroscedasticity, where the error should be provided
data Distribution = MSE | Gaussian | HGaussian | Bernoulli | Poisson | ROXY | LOG10
    deriving (Show, Read, Enum, Bounded, Eq)

-- | Sum-of-square errors or Sum-of-square residues
sse :: Columns -> Target -> Fix SRTree -> Target -> Double
sse xss ys tree theta = err
  where
    m      = V.length ys
    yhat   = compile xss tree theta
    err    = V.sum $ (ys - yhat) ^ (2 :: Int)

sseError :: Columns -> Target -> Target -> Fix SRTree -> Target -> Double
sseError xss ys yErr tree theta = err
  where
    m      = V.length ys
    yhat   = compile xss tree theta
    err    = V.sum $ ((ys - yhat) ^ (2 :: Int) / yErr)

-- | Total Sum-of-squares
sseTot :: Columns -> Target -> Fix SRTree -> Target -> Double
sseTot xss ys tree theta = err
  where
    m      = V.length ys
    ym     = V.sum ys / fromIntegral m
    err    = V.sum $ (V.map (subtract ym) ys) ^ (2 :: Int)
        
-- | Mean squared errors
mse :: Columns -> Target -> Fix SRTree -> Target -> Double
mse xss ys tree theta = let m = V.length ys in sse xss ys tree theta / fromIntegral m

-- | Root of the mean squared errors
rmse :: Columns -> Target -> Fix SRTree -> Target -> Double
rmse xss ys tree = sqrt . mse xss ys tree

-- | Coefficient of determination
r2 :: Columns -> Target -> Fix SRTree -> Target -> Double
r2 xss ys tree theta = 1 - sse xss ys tree theta / sseTot  xss ys tree theta

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

-- | Negative log-likelihood
nll :: Distribution -> Maybe Target -> Columns -> Target -> Fix SRTree -> Target -> Double

-- | Mean Squared error (not a distribution)
nll MSE _ xss ys t theta = mse xss ys t theta

nll LOG10 _ xss ys t theta = V.sum $ (V.map (logBase 10) $ (f ys / f yhat)) ^ (2 :: Int)
  where
    yhat   = compile xss t theta
    m      = V.length ys
    f :: Target -> Target
    f z    =  (z + V.map (\zi -> sqrt (zi^2 + 1e-10)) z)
    -- log ys - log y = log (ys/y)

-- | Gaussian distribution, theta must contain an additional parameter corresponding
-- to variance.
nll Gaussian mYerr xss ys t theta
  -- | nParams == p' = error "For Gaussian distribution theta must contain the variance as its last value."
  | otherwise     = if nParams < p'
                       then 0.5*(sse xss ys t theta / s + m*log (2*pi*s))
                       else 0.5*(sse xss ys t theta * (exp $ negate s') + m*log(2*pi) + m*s')
  where
    s       = mse xss ys t theta
    s'      = (theta V.! (p' - 1))
    -- s       = (theta V.! (p' - 1))
    m'      = V.length ys
    p'      = V.length theta
    nParams = countParamsUniq t
    m       = fromIntegral m'
    p       = fromIntegral p'

-- | Gaussian with heteroscedasticity, it needs a valid mYerr
nll HGaussian mYerr xss ys t theta =
  case mYerr of
    Nothing   -> error "For HGaussian, you must provide the measured error for the target variable."
    Just yErr -> 0.5*(sseError xss ys yErr t theta + V.sum (V.map (log . (2*) . (pi*)) yErr))
  where
    m'      = V.length ys
    p'      = V.length theta
    m       = fromIntegral m'
    p       = fromIntegral p'

-- | Bernoulli distribution of f(x; theta) is, given phi = 1 / (1 + exp (-f(x; theta))),
-- y log phi + (1-y) log (1 - phi), assuming y \in {0,1}
nll Bernoulli _ xss ys tree theta
  | notValid ys = error "For Bernoulli distribution the output must be either 0 or 1."
  | otherwise   = V.sum $ (V.map (1-) ys) * yhat + log (V.map (1+) $ exp (V.map negate yhat))
  where
    m        = V.length ys
    yhat     = compile xss tree theta
    notValid = V.any (\x -> x /= 0 && x /= 1)

nll Poisson _ xss ys tree theta
  | notValid ys = error "For Poisson distribution the output must be non-negative."
  -- | V.any isNaN yhat = error $ "NaN predictions " <> show theta
  | otherwise   = negate . V.sum $ ys * yhat - ys * log ys - exp yhat
  where
    yhat     = compile xss tree theta
    notValid = V.any (<0)

nll ROXY mYerr xss ys tree theta
  | isNothing mYerr = error "Can't calculate ROXY nll without x,y-errors."
  | p < num_params + 3 = error "We need 3 additional parameters for ROXY."
  | n /= 1 && n/=5     = error "For ROXY dataset must contain a single variable, or 1 variable + 4 cached data."
  | otherwise          = if isNaN negLL then (1.0/0.0) else negLL
  where
    m            = V.length ys
    p'           = V.length theta
    n            = length xss
    p            = fromIntegral p'
    num_params   = countParamsUniq tree

    x0           = xss !! 0
    logX         = xss !! 1
    logY         = xss !! 2
    logXErr      = xss !! 3
    logYErr      = xss !! 4


    yErr         = fromJust mYerr
    one          = V.replicate m 1
    zero         = V.replicate m 0

    (sig, mu_gauss, w_gauss) = (theta V.! num_params, theta V.! (num_params + 1), theta V.! (num_params + 2))

    applyDer :: Op -> Target -> Target -> Target -> Target -> Target
    applyDer Add l dl r dr      = dl+dr
    applyDer Sub l dl r dr      = dl-dr
    applyDer Mul l dl r dr      = l*dr + r*dl
    applyDer Div l dl r dr      = (dl*r - dr*l) / (r^2)
    applyDer Power l dl r dr    = l ** (r - 1) * (r*dl + l * log l * dr)
    applyDer PowerAbs l dl r dr = (abs l ** r) * (dr * log (abs l) + r * dl / l)
    applyDer AQ l dl r dr       = ((1 + r*r) * dl - l * r * dr) / V.map (**1.5) (1 + r*r)

    (yhat, grad) = cata alg tree
      where
        alg (Var ix)   = (x0, one)
        alg (Param ix) = (V.replicate m (theta V.! ix), zero)
        alg (Const x)  = (V.replicate m x, zero)
        alg (Uni f (val, der))  = (V.map (evalFun f) val, V.map (derivative f) val * der)
        alg (Bin op (valL, derL) (valR, derR)) = (V.zipWith (evalOp op) valL valR, applyDer op valL derL valR derR)

    f            = V.map (logBase 10) (abs yhat)
    fprime       = grad / (log 10 * yhat) * x0 * log 10

    -- nll
    w_gauss2     = w_gauss ^ 2
    s2           = V.map(+(sig^2)) logYErr
    den          = V.map(*w_gauss2) (fprime ^ 2 * logXErr) + s2 * (V.map (+ w_gauss2) logXErr)

    neglogP = log (2 * pi)
        + log den
        + (V.map (*w_gauss2) (f - logY) * (f - logY)
           + logXErr * (fprime * (V.map (mu_gauss-) logX) + f - logY)^2
           + s2 * (V.map (subtract mu_gauss) logX)^2) / den
    negLL = 0.5 * V.sum neglogP

-- WARNING: pass tree with parameters
-- TODO: handle error similar to ROXY
buildNLL MSE m tree = ((tree - var (-1)) ** 2) / constv m
buildNLL LOG10 m tree = (((log (y / tree')) / log 10) ** 2) / constv m
  where
    tree' = (tree + sqrt(tree^2 + 1e-10))
    y     = (var (-1) + sqrt(var (-1) ^ 2 + 1e-10))

buildNLL Gaussian m tree =  (square(tree - var (-1)) * (e (negate (param p)))) + (((param p)))
  where
    -- (f(x) - y)^2 / s^2 + log(s^2)
    square = Fix . Uni Square
    e = Fix. Uni Exp

    p = countParamsUniq tree
buildNLL HGaussian m tree = (tree - var (-1)) ** 2 / var (-2) + constv m * log (2*pi* var (-2))
buildNLL Poisson m tree = var (-1) * log (var (-1)) + exp tree - var (-1) * tree
buildNLL Bernoulli m tree = log (1 + exp (negate tree)) + (1 - var (-1)) * tree
buildNLL ROXY m tree = neglogP
  where
    p = countParamsUniq tree
    f = log (abs tree) / log 10
    fprime = deriveByVar 0 tree / (log 10 * tree) * var 0 * log 10
    logX         = var 1
    logY         = var 2
    logXErr      = var 3
    logYErr      = var 4
    sig = param p
    mu_gauss = param (p+1)
    w_gauss = param (p+2)
    w_gauss2 = w_gauss ** 2
    s2 = logYErr + sig ** 2
    den = fprime ** 2 * w_gauss2 * logXErr + s2 * (w_gauss2 + logXErr)
    neglogP = log (2*pi)
              + log den
              + ( w_gauss2 * (f - logY) * (f - logY)
                + logXErr * (fprime *(mu_gauss - logX) + f - logY)**2
                + s2 * (logX - mu_gauss) ** 2
                ) / den

-- | Prediction for different distributions
predict :: Distribution -> Fix SRTree -> Target -> Columns -> Target
predict MSE       tree theta xss = compile xss tree theta
predict LOG10     tree theta xss = compile xss tree theta
predict Gaussian  tree theta xss = compile xss tree theta
predict Bernoulli tree theta xss = logistic $ compile xss tree theta
predict Poisson   tree theta xss = exp $ compile xss tree theta
predict ROXY      tree theta xss = compile xss tree theta

-- | Gradient of the negative log-likelihood
gradNLL :: Distribution -> Maybe Target -> Columns -> Target -> Fix SRTree -> Target -> (Double, Target)
gradNLL dist mYerr xss ys tree theta = (f, grad) -- gradNLLArr dist xss ys mYerr treeArr j2ix (toStorableVector theta)
  where
    grad :: Target
    grad = V.fromList [finitediff ix | ix <- [0..p-1]]
    p    = V.length theta

    disturb :: Int -> Target
    disturb ix    = V.fromList $ Prelude.zipWith (\iy v -> if iy==ix  then (v+eps) else v) [0..] (V.toList theta)

    eps :: Double
    eps           = 1e-8
    f             = (/ fromIntegral m) . V.sum . V.map (^2) $ (predict MSE tree theta xss) - ys
    finitediff ix = let t1 = disturb ix
                        f' = (/ fromIntegral m) . V.sum . V.map (^2) $ (predict MSE tree t1 xss) - ys'
                     in (f' - f)/eps
    m         = V.length ys
    tree'     = buildNLL dist (fromIntegral m) tree
    treeArr   = IntMap.toAscList $ tree2arr tree'
    j2ix      = IntMap.fromList $ Prelude.zip (Prelude.map fst treeArr) [0..]
    flog :: Target -> Target
    flog z    = V.map (logBase 10) (z + V.map sqrt (z^2 + 1e-10))
    ys'       = (if dist==LOG10 then id else id) (ys)


nanTo0 x = if isNaN x || isInfinite x then 0 else x
{-# INLINE nanTo0 #-}

-- | Fisher information of negative log-likelihood
fisherNLL :: Distribution -> Maybe Target -> Columns -> Target -> Fix SRTree -> Target -> Target
fisherNLL ROXY mYerr xss ys tree theta = V.generate p finiteDiff
  where
    m             = V.length ys
    p             = V.length theta
    f             = nll ROXY mYerr xss ys tree theta
    eps           = 1e-6
    finiteDiff ix = unsafePerformIO $ do
                      theta' <- V.thaw theta
                      v <- VM.read theta' ix
                      VM.write theta' ix (v + eps)
                      thetaPlus <- V.freeze theta'
                      VM.write theta' ix (v - eps)
                      thetaMinus <- V.freeze theta'
                      let fPlus     = nll ROXY mYerr xss ys tree thetaPlus
                          fMinus    = nll ROXY mYerr xss ys tree thetaMinus
                      pure $ (fPlus + fMinus - 2*f)/(eps*eps)
fisherNLL Gaussian mYerr xss ys tree theta = V.generate p finiteDiff
  where
    m             = V.length ys
    p             = V.length theta
    f             = nll Gaussian mYerr xss ys tree theta
    eps           = 1e-6
    finiteDiff ix = unsafePerformIO $ do
                      theta' <- V.thaw theta
                      v <- VM.read theta' ix
                      VM.write theta' ix (v + eps)
                      thetaPlus <- V.freeze theta'
                      VM.write theta' ix (v - eps)
                      thetaMinus <- V.freeze theta'
                      let fPlus     = nll Gaussian mYerr xss ys tree thetaPlus
                          fMinus    = nll Gaussian mYerr xss ys tree thetaMinus
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
                    MSE       -> (yhat, V.replicate m 1)
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
                    MSE       -> (yhat, V.replicate m 1)
                    LOG10     -> (yhat, V.replicate m 1)
                    Gaussian  -> (yhat, V.replicate m 1)
                    Bernoulli -> (logistic yhat, phi*(V.replicate m 1 - phi))
                    Poisson   -> (exp yhat, phi)

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
{-# INLINE tree2arr #-}
