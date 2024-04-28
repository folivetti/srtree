{-# LANGUAGE ViewPatterns #-}
module Algorithm.SRTree.Likelihoods
  ( Distribution (..)
  , PVector
  , SRMatrix
  , sse
  , mse
  , rmse
  , nll
  , predict
  , gradNLL
  , fisherNLL
  , getSErr
  , hessianNLL
  )
    where

import Data.SRTree (SRTree (..), Fix(..), floatConstsToParam, relabelParams)
import Algorithm.SRTree.AD -- ( reverseModeUnique )
import Data.SRTree.Eval ( evalTree, PVector, SRVector, SRMatrix, SRMatrix, PVector )
import Data.SRTree.Derivative ( deriveByParam )
import Data.Maybe ( fromMaybe )

import qualified Data.Massiv.Array as M 
import Data.Massiv.Array hiding (map, read, all, take, replicate, zip, tail)

import Debug.Trace ( trace, traceShow )

-- | Supported distributions for negative log-likelihood
data Distribution = Gaussian | Bernoulli | Poisson
    deriving (Show, Read, Enum, Bounded)

-- | Sum-of-square errors or Sum-of-square residues
sse :: SRMatrix -> PVector -> Fix SRTree -> PVector -> Double
sse xss ys tree theta = err
  where
    (Sz m) = M.size ys
    cmp    = getComp xss
    yhat   = evalTree xss theta tree
    err    = M.sum $ (delay ys - yhat) ^ (2 :: Int)
        
-- | Mean squared errors
mse :: SRMatrix -> PVector -> Fix SRTree -> PVector -> Double
mse xss ys tree theta = let (Sz m) = M.size ys in sse xss ys tree theta / fromIntegral m

-- | Root of the mean squared errors
rmse :: SRMatrix -> PVector -> Fix SRTree -> PVector -> Double
rmse xss ys tree = sqrt . mse xss ys tree

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
negSum :: PVector -> Double
negSum = negate . M.sum
{-# inline negSum #-}

-- | Negative log-likelihood
nll :: Distribution -> Maybe Double -> SRMatrix -> PVector -> Fix SRTree -> PVector -> Double

-- | Gaussian distribution
nll Gaussian msErr xss ys t theta = 0.5*(ssr/s2 + m*log (2*pi*s2))
  where
    (Sz m') = M.size ys 
    (Sz p') = M.size theta
    m    = fromIntegral m' 
    p    = fromIntegral p'
    ssr  = sse xss ys t theta
    est  = sqrt $ ssr / (m - p)
    sErr = getSErr Gaussian est msErr
    s2   = sErr ^ 2

-- | Bernoulli distribution of f(x; theta) is, given phi = 1 / (1 + exp (-f(x; theta))),
-- y log phi + (1-y) log (1 - phi), assuming y \in {0,1}
nll Bernoulli _ xss ys tree theta
  | notValid ys = error "For Bernoulli distribution the output must be either 0 or 1."
  | otherwise   = negate . M.sum $ delay ys * yhat - log (1 + exp yhat)
  where
    (Sz m)   = M.size ys
    yhat     = evalTree xss theta tree
    notValid = M.any (\x -> x /= 0 && x /= 1)

nll Poisson _ xss ys tree theta 
  | notValid ys = error "For Poisson distribution the output must be non-negative."
  | M.any isNaN yhat = error $ "NaN predictions " <> show theta
  | otherwise   = negate . M.sum $ ys' * yhat - ys' * log ys' - exp yhat
  where
    ys'      = delay ys
    yhat     = evalTree xss theta tree
    notValid = M.any (<0)

nll' :: Distribution -> Double -> SRVector -> SRVector -> Double
nll' Gaussian sErr yhat ys = 0.5*(ssr/s2 + m*log (2*pi*s2))
  where 
    (Sz m') = M.size ys 
    m    = fromIntegral m' 
    ssr  = M.sum $ (ys - yhat)^2
    s2   = sErr ^ 2
nll' Bernoulli _ yhat ys = negate . M.sum $ ys * yhat - log (1 + exp yhat)
nll' Poisson _ yhat ys   = negate . M.sum $ ys * yhat - ys * log ys - exp yhat
{-# INLINE nll' #-}

-- | Prediction for different distributions
predict :: Distribution -> Fix SRTree -> PVector -> SRMatrix -> SRVector
predict Gaussian  tree theta xss = evalTree xss theta tree
predict Bernoulli tree theta xss = logistic $ evalTree xss theta tree
predict Poisson   tree theta xss = exp $ evalTree xss theta tree

-- | Gradient of the negative log-likelihood
gradNLL :: Distribution -> Maybe Double -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (Double, SRVector)
gradNLL Gaussian msErr xss ys tree theta = (nll' Gaussian sErr yhat (delay ys), transpose grad !>< err ./ (sErr * sErr))
  where
    (Sz m)                = M.size ys
    (Sz p)                = M.size theta
    (delay -> yhat, grad) = forwardMode xss theta tree
    err                   = delay yhat - delay ys
    ssr                   = sse xss ys tree theta
    est                   = sqrt $ ssr / fromIntegral (m - p)
    sErr                  = getSErr Gaussian est msErr

gradNLL Bernoulli _ xss (delay -> ys) tree theta
  | notValid ys = error "For Bernoulli distribution the output must be either 0 or 1."
  | otherwise   = (nll' Bernoulli 1.0 yhat ys, transpose grad !>< err)
  where
    (delay -> yhat, grad) = forwardMode xss theta tree
    notValid              = M.any (\x -> x /= 0 && x /= 1)
    grad'                 = M.map nanTo0 grad
    err                   = logistic yhat - ys
    nanTo0 x              = if isNaN x then 0 else x

gradNLL Poisson _ xss (delay -> ys) tree theta
  | notValid ys      = error "For Poisson distribution the output must be non-negative."
  | M.any isNaN grad = error $ "NaN gradient " <> show grad
  | otherwise        = (nll' Poisson 1.0 yhat ys, transpose grad !>< err)
  where
    (delay -> yhat, grad) = forwardMode xss theta tree
    err                   = exp yhat - ys
    notValid              = M.any (<0)

-- | Fisher information of negative log-likelihood
fisherNLL :: Distribution -> Maybe Double -> SRMatrix -> PVector -> Fix SRTree -> PVector -> SRVector
fisherNLL dist msErr xss ys tree theta = makeArray cmp (Sz p) build 
  where
    build ix = let dtdix = deriveByParam ix t'
                   d2tdix2 = deriveByParam ix dtdix 
                   f'      = eval dtdix 
                   f''     = eval d2tdix2 
                in (/sErr^2) . M.sum $ phi' * f'^2 - res * f'' 
    cmp    = getComp xss 
    (Sz m) = M.size ys
    (Sz p) = M.size theta
    t'     = fst $ floatConstsToParam tree
    eval   = evalTree xss theta
    ssr    = sse xss ys tree theta
    sErr   = getSErr dist est msErr
    est    = sqrt $ ssr / fromIntegral (m - p)
    yhat   = eval t'
    res    = delay ys - phi

    (phi, phi') = case dist of
                    Gaussian  -> (yhat, 1)
                    Bernoulli -> (logistic yhat, phi*(1 - phi))
                    Poisson   -> (exp yhat, phi)

-- | Hessian of negative log-likelihood
--
-- Note, though the Fisher is just the diagonal of the return of this function
-- it is better to keep them as different functions for efficiency
hessianNLL :: Distribution -> Maybe Double -> SRMatrix -> PVector -> Fix SRTree -> PVector -> SRMatrix
hessianNLL dist msErr xss ys tree theta = makeArray cmp (Sz (p :. p)) build  
  where
    build (ix :. iy) = let dtdix   = deriveByParam ix t' 
                           dtdiy   = deriveByParam iy t' 
                           d2tdixy = deriveByParam iy dtdix
                           fx      = eval dtdix 
                           fy      = eval dtdiy 
                           fxy     = eval d2tdixy 
                           e       = (/sErr^2) . M.sum $ phi' * fx * fy - res * fxy
                        in traceShow fxy e
    cmp    = getComp xss
    (Sz m) = M.size ys
    (Sz p) = M.size theta
    t'     = relabelParams tree -- $ floatConstsToParam tree
    eval   = evalTree xss theta
    ssr    = sse xss ys tree theta
    sErr   = getSErr dist est msErr
    est    = sqrt $ ssr / fromIntegral (m - p)
    yhat   = eval t'
    res    = delay ys - phi

    (phi, phi') = case dist of
                    Gaussian  -> (yhat, M.replicate cmp (Sz m) 1)
                    Bernoulli -> (logistic yhat, phi*(M.replicate cmp (Sz m) 1 - phi))
                    Poisson   -> (exp yhat, phi)

