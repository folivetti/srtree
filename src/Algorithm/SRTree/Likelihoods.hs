{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.SRTree.Likelihoods 
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
  , PVector
  , SRMatrix
  , sse
  , mse
  , rmse
  , r2
  , nll
  , predict
  , buildNLL
  , gradNLL
  , gradNLLArr
  , fisherNLL
  , getSErr
  , hessianNLL
  , tree2arr
  )
    where

import Algorithm.SRTree.AD ( reverseModeArr )
import Data.Massiv.Array hiding (all, map, read, replicate, tail, take, zip)
import qualified Data.Massiv.Array as M
import qualified Data.Massiv.Array.Mutable as Mut
import Data.Maybe (fromMaybe)
import Data.SRTree
import Data.SRTree.Recursion ( cata, accu )
import Data.SRTree.Derivative (deriveByParam, deriveByVar, derivative)
import Data.SRTree.Eval
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Vector.Storable as VS
import GHC.IO (unsafePerformIO)
import Data.Maybe

import Debug.Trace
import Data.SRTree.Print

-- | Supported distributions for negative log-likelihood
-- MSE refers to mean squared error
-- HGaussian is Gaussian with heteroscedasticity, where the error should be provided
data Distribution = MSE | Gaussian | HGaussian | Bernoulli | Poisson | ROXY
    deriving (Show, Read, Enum, Bounded, Eq)

-- | Sum-of-square errors or Sum-of-square residues
sse :: SRMatrix -> PVector -> Fix SRTree -> PVector -> Double
sse xss ys tree theta = err
  where
    (Sz m) = M.size ys
    cmp    = getComp xss
    yhat   = evalTree xss theta tree
    err    = M.sum $ (delay ys - yhat) ^ (2 :: Int)

sseError :: SRMatrix -> PVector -> PVector -> Fix SRTree -> PVector -> Double
sseError xss ys yErr tree theta = err
  where
    (Sz m) = M.size ys
    cmp    = getComp xss
    yhat   = evalTree xss theta tree
    err    = M.sum $ ((delay ys - yhat) ^ (2 :: Int) / (delay yErr))

-- | Total Sum-of-squares
sseTot :: SRMatrix -> PVector -> Fix SRTree -> PVector -> Double
sseTot xss ys tree theta = err
  where
    (Sz m) = M.size ys
    cmp    = getComp xss
    ym     = M.sum ys / fromIntegral m
    err    = M.sum $ (M.map (subtract ym) ys) ^ (2 :: Int)
        
-- | Mean squared errors
mse :: SRMatrix -> PVector -> Fix SRTree -> PVector -> Double
mse xss ys tree theta = let (Sz m) = M.size ys in sse xss ys tree theta / fromIntegral m

-- | Root of the mean squared errors
rmse :: SRMatrix -> PVector -> Fix SRTree -> PVector -> Double
rmse xss ys tree = sqrt . mse xss ys tree

-- | Coefficient of determination
r2 :: SRMatrix -> PVector -> Fix SRTree -> PVector -> Double
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
negSum :: PVector -> Double
negSum = negate . M.sum
{-# inline negSum #-}

-- | Negative log-likelihood
nll :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> Double

-- | Mean Squared error (not a distribution)
nll MSE _ xss ys t theta = mse xss ys t theta

-- | Gaussian distribution, theta must contain an additional parameter corresponding
-- to variance.
nll Gaussian mYerr xss ys t theta
  | nParams == p' = error "For Gaussian distribution theta must contain the variance as its last value."
  | otherwise     = 0.5*(sse xss ys t theta / s + m*log (2*pi*s))
  where
    s       = theta M.! (p' - 1)
    (Sz m') = M.size ys 
    (Sz p') = M.size theta
    nParams = countParams t
    m       = fromIntegral m'
    p       = fromIntegral p'

-- | Gaussian with heteroscedasticity, it needs a valid mYerr
nll HGaussian mYerr xss ys t theta =
  case mYerr of
    Nothing   -> error "For HGaussian, you must provide the measured error for the target variable."
    Just yErr -> 0.5*(sseError xss ys yErr t theta + M.sum (M.map (log . (2*) . (pi*)) yErr))
  where
    (Sz m') = M.size ys
    (Sz p') = M.size theta
    m       = fromIntegral m'
    p       = fromIntegral p'

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
  -- | M.any isNaN yhat = error $ "NaN predictions " <> show theta
  | otherwise   = negate . M.sum $ ys' * yhat - ys' * log ys' - exp yhat
  where
    ys'      = delay ys
    yhat     = evalTree xss theta tree
    notValid = M.any (<0)

nll ROXY mYerr xss ys tree theta
  | isNothing mYerr = error "Can't calculate ROXY nll without x,y-errors."
  | p < num_params + 3 = error "We need 3 additional parameters for ROXY."
  | n /= 1 && n/=5     = error "For ROXY dataset must contain a single variable, or 1 variable + 4 cached data."
  | otherwise          = if isNaN negLL then (1.0/0.0) else negLL
  where
    (Sz p')      = M.size theta
    (Sz2 m n)    = M.size xss
    p            = fromIntegral p'
    num_params   = countParams tree

    x0           = xss <! 0
    logX         = xss <! 1
    logY         = xss <! 2
    logXErr      = xss <! 3
    logYErr      = xss <! 4


    yErr         = fromJust mYerr
    one          = M.replicate compMode (Sz m) 1
    zero         = M.replicate compMode (Sz m) 0

    (sig, mu_gauss, w_gauss) = (theta ! num_params, theta ! (num_params + 1), theta ! (num_params + 2))

    applyDer :: Op -> Array D Ix1 Double -> Array D Ix1 Double -> Array D Ix1 Double -> Array D Ix1 Double -> Array D Ix1 Double
    applyDer Add l dl r dr      = dl+dr
    applyDer Sub l dl r dr      = dl-dr
    applyDer Mul l dl r dr      = l*dr + r*dl
    applyDer Div l dl r dr      = (dl*r - dr*l) / (r^2)
    applyDer Power l dl r dr    = l ** (r.-1) * (r*dl + l * log l * dr)
    applyDer PowerAbs l dl r dr = (abs l ** r) * (dr * log (abs l) + r * dl / l)
    applyDer AQ l dl r dr       = ((1 +. r*r) * dl - l * r * dr) / M.map (**1.5) (1 +. r*r)

    (yhat, grad) = cata alg tree
      where
        alg (Var ix)   = (x0, one)
        alg (Param ix) = (M.replicate compMode (Sz m) (theta M.! ix), zero)
        alg (Const x)  = (M.replicate compMode (Sz m) x, zero)
        alg (Uni f (val, der))  = (M.map (evalFun f) val, M.map (derivative f) val * der)
        alg (Bin op (valL, derL) (valR, derR)) = (M.zipWith (evalOp op) valL valR, applyDer op valL derL valR derR)

    f            = M.map (logBase 10) (abs yhat)
    fprime       = grad / (log 10 *. yhat) * x0 .* log 10

    -- nll
    w_gauss2     = w_gauss ^ 2
    s2           = delay $ logYErr .+ sig^2
    den          = fprime ^ 2 .* w_gauss2 * logXErr + s2 * (w_gauss2 +. logXErr)

    neglogP = log (2 * pi)
        +. log den
        + (w_gauss2 *. (f - logY) * (f - logY)
           + logXErr * (fprime * (mu_gauss -. logX) + f - logY)^2
           + s2 * (logX .- mu_gauss)^2) / den
    negLL = 0.5 * M.sum neglogP

-- WARNING: pass tree with parameters
-- TODO: handle error similar to ROXY
buildNLL MSE m tree = ((tree - var (-1)) ** 2) / constv m
buildNLL Gaussian m tree = (tree - var (-1)) ** 2 / param p + constv m * log (2*pi* param p)
  where
    p = countParams tree
buildNLL HGaussian m tree = (tree - var (-1)) ** 2 / var (-2) + constv m * log (2*pi* var (-2))
buildNLL Poisson m tree = var (-1) * log (var (-1)) + exp tree - var (-1) * tree
buildNLL Bernoulli m tree = log (1 + exp tree) - var (-1) * tree
buildNLL ROXY m tree = neglogP
  where
    p = countParams tree
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
predict :: Distribution -> Fix SRTree -> PVector -> SRMatrix -> SRVector
predict MSE       tree theta xss = evalTree xss theta tree
predict Gaussian  tree theta xss = evalTree xss theta tree
predict Bernoulli tree theta xss = logistic $ evalTree xss theta tree
predict Poisson   tree theta xss = exp $ evalTree xss theta tree
predict ROXY      tree theta xss = evalTree xss theta tree

-- | Gradient of the negative log-likelihood
gradNLL :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (Double, SRVector)
gradNLL dist mYerr xss ys tree theta = (f, delay grad) -- gradNLLArr dist xss ys mYerr treeArr j2ix (toStorableVector theta)
  where
    grad :: PVector
    grad = M.fromList M.Seq [finitediff ix | ix <- [0..p-1]]
    (Sz p) = M.size theta

    disturb :: Int -> PVector
    disturb ix = M.fromList M.Seq $ Prelude.zipWith (\iy v -> if iy==ix  then (v+eps) else v) [0..] (M.toList theta)
    eps :: Double
    eps = 1e-8
    f = (/ fromIntegral m) . M.sum . M.map (^2) $ (predict MSE tree theta xss) - delay ys
    finitediff ix = let t1 = disturb ix
                        f' = (/ fromIntegral m) . M.sum . M.map (^2) $ (predict MSE tree t1 xss) - delay ys
                     in (f' - f)/eps
    (Sz2 m _) = M.size xss
    tree'     = buildNLL dist (fromIntegral m) tree
    treeArr   = IntMap.toAscList $ tree2arr tree'
    j2ix      = IntMap.fromList $ Prelude.zip (Prelude.map fst treeArr) [0..]

    {-
    -- EXAMPLE OF FINITE DIFFERENCE
    -- Implement for debugging
gradNLL ROXY mXerr mYerr xss ys tree theta =
   (f, delay grad)
  where
    (Sz p) = M.size theta
    (Sz2 m n) = M.size xss
    yhat   = predict Gaussian tree theta xss
    f      = nll ROXY mXerr mYerr xss ys tree theta
    grad   = makeArray @S (getComp xss) (Sz p) finiteDiff
    eps    = 1e-8

    finiteDiff ix = unsafePerformIO $ do
                      theta' <- Mut.thaw theta
                      v <- Mut.readM theta' ix
                      Mut.writeM theta' ix (v + eps)
                      theta'' <- Mut.freezeS theta'
                      let f'= nll ROXY mXerr mYerr xss ys tree theta''
                          g = (f' - f)/eps
                      pure $ if isNaN g then (1/0) else g
                      -}

nanTo0 x = x -- if isNaN x || isInfinite x then 0 else x
{-# INLINE nanTo0 #-}

-- | Gradient of the negative log-likelihood
gradNLLArr MSE xss ys mYerr tree j2ix theta =
  (M.sum yhat, delay grad')
  where
    (yhat, grad) = reverseModeArr xss ys mYerr theta tree j2ix
    grad'        = M.map nanTo0 grad
gradNLLArr Gaussian xss ys mYerr tree j2ix theta =
  (M.sum yhat, delay grad')
  where
    (yhat, grad) = reverseModeArr xss ys mYerr theta tree j2ix
    grad'        = M.map nanTo0 grad
gradNLLArr Bernoulli xss ys mYerr tree j2ix theta
  | M.any (\x -> x /= 0 && x /= 1) ys = error "For Bernoulli distribution the output must be either 0 or 1."
  | otherwise                         = (M.sum yhat, delay grad')
  where
    (yhat, grad) = reverseModeArr xss ys mYerr theta tree j2ix
    grad'        = M.map nanTo0 grad
gradNLLArr Poisson xss ys mYerr tree j2ix theta
  | M.any (<0) ys    = error "For Poisson distribution the output must be non-negative."
  | otherwise        = (M.sum yhat, delay grad')
  where
    (yhat, grad) = reverseModeArr xss ys mYerr theta tree j2ix
    grad'        = M.map nanTo0 grad
gradNLLArr ROXY xss ys mYerr tree j2ix theta =
  ((*0.5) $ M.sum yhat, M.map (*(0.5)) $ delay grad')
  where
    (yhat, grad) = reverseModeArr xss ys mYerr theta tree j2ix
    grad'        = M.map nanTo0 grad

-- | Fisher information of negative log-likelihood
fisherNLL :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> SRVector
fisherNLL ROXY mYerr xss ys tree theta = makeArray cmp (Sz p) finiteDiff
  where
    cmp    = getComp xss
    (Sz m) = M.size ys
    (Sz p) = M.size theta
    f      = nll ROXY mYerr xss ys tree theta
    eps = 1e-6
    finiteDiff ix = unsafePerformIO $ do
                      theta' <- Mut.thaw theta
                      v <- Mut.readM theta' ix
                      Mut.writeM theta' ix (v + eps)
                      thetaPlus <- Mut.freezeS theta'
                      Mut.writeM theta' ix (v - eps)
                      thetaMinus <- Mut.freezeS theta'
                      let fPlus     = nll ROXY mYerr xss ys tree thetaPlus
                          fMinus    = nll ROXY mYerr xss ys tree thetaMinus
                      pure $ (fPlus + fMinus - 2*f)/(eps*eps)

fisherNLL dist mYerr xss ys tree theta = makeArray cmp (Sz p) build
  where
    build ix = let dtdix   = deriveByParam ix t'
                   d2tdix2 = deriveByParam ix dtdix 
                   f'      = eval dtdix 
                   f''     = eval d2tdix2 
               in case dist of
                    Gaussian -> M.sum . (/delay yErr) $ phi' * f'^2 - res * f''
                    _        -> M.sum $ phi' * f'^2 - res * f''
    cmp    = getComp xss 
    (Sz m) = M.size ys
    (Sz p) = M.size theta
    t'     = fst $ floatConstsToParam tree
    eval   = evalTree xss theta
    yhat   = eval t'
    res    = delay ys - phi
    yErr   = case mYerr of
               Nothing -> M.replicate (getComp xss) (Sz m) est
               Just e  -> e
    est    = fromIntegral (m - p)

    (phi, phi') = case dist of
                    MSE       -> (yhat, M.replicate compMode (Sz m) 1)
                    Gaussian  -> (yhat, M.replicate compMode (Sz m) 1)
                    Bernoulli -> (logistic yhat, phi*(M.replicate compMode (Sz m) 1 - phi))
                    Poisson   -> (exp yhat, phi)

-- | Hessian of negative log-likelihood
--
-- Note, though the Fisher is just the diagonal of the return of this function
-- it is better to keep them as different functions for efficiency
hessianNLL :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> SRMatrix
hessianNLL ROXY mYerr xss ys tree theta = undefined
hessianNLL dist mYerr xss ys tree theta = makeArray cmp (Sz (p :. p)) build
  where
    build (ix :. iy) = let dtdix   = deriveByParam ix t' 
                           dtdiy   = deriveByParam iy t' 
                           d2tdixy = deriveByParam iy dtdix
                           fx      = eval dtdix 
                           fy      = eval dtdiy 
                           fxy     = eval d2tdixy 
                        in case dist of
                            Gaussian -> M.sum . (/delay yErr) $ phi' * fx * fy - res * fxy
                            _        -> M.sum $ phi' * fx * fy - res * fxy

    cmp    = getComp xss
    (Sz m) = M.size ys
    (Sz p) = M.size theta
    t'     = tree -- relabelParams tree -- $ floatConstsToParam tree
    eval   = evalTree xss theta
    yErr   = case mYerr of
               Nothing -> M.replicate compMode (Sz m) est
               Just e  -> e
    est    = fromIntegral (m - p)
    yhat   = eval t'
    res    = delay ys - phi

    (phi, phi') = case dist of
                    Gaussian  -> (yhat, M.replicate cmp (Sz m) 1)
                    Bernoulli -> (logistic yhat, phi*(M.replicate cmp (Sz m) 1 - phi))
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
