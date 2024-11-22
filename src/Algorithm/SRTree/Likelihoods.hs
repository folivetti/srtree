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
  , gradNLL
  , gradNLLArr
  , gradNLLNonUnique
  , fisherNLL
  , getSErr
  , hessianNLL
  )
    where

import Algorithm.SRTree.AD ( forwardMode, reverseModeUnique, reverseModeUniqueArr ) -- ( reverseModeUnique )
import Data.Massiv.Array hiding (all, map, read, replicate, tail, take, zip)
import qualified Data.Massiv.Array as M
import qualified Data.Massiv.Array.Mutable as Mut
import Data.Maybe (fromMaybe)
import Data.SRTree
import Data.SRTree.Recursion ( cata )
import Data.SRTree.Derivative (deriveByParam, derivative)
import Data.SRTree.Eval
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Vector.Storable as VS
import GHC.IO (unsafePerformIO)
import Data.Maybe

import Debug.Trace
import Data.SRTree.Print

-- | Supported distributions for negative log-likelihood
data Distribution = Gaussian | Bernoulli | Poisson | ROXY
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
    err    = M.sum $ ((delay ys - yhat) / (delay yErr)) ^ (2 :: Int)

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
nll :: Distribution -> Maybe SRMatrix -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> Double

-- | Gaussian distribution
nll Gaussian mXerr mYerr xss ys t theta =
  case mYerr of
    Nothing   -> 0.5*(sse xss ys t theta / (m-p) + m*log (2*pi*(m-p)))
    Just yErr -> 0.5*(sseError xss ys yErr t theta + log (2*pi* M.sum yErr))
  where
    (Sz m') = M.size ys 
    (Sz p') = M.size theta
    m       = fromIntegral m'
    p       = fromIntegral p'

-- | Bernoulli distribution of f(x; theta) is, given phi = 1 / (1 + exp (-f(x; theta))),
-- y log phi + (1-y) log (1 - phi), assuming y \in {0,1}
nll Bernoulli _ _ xss ys tree theta
  | notValid ys = error "For Bernoulli distribution the output must be either 0 or 1."
  | otherwise   = negate . M.sum $ delay ys * yhat - log (1 + exp yhat)
  where
    (Sz m)   = M.size ys
    yhat     = evalTree xss theta tree
    notValid = M.any (\x -> x /= 0 && x /= 1)

nll Poisson _ _ xss ys tree theta
  | notValid ys = error "For Poisson distribution the output must be non-negative."
  -- | M.any isNaN yhat = error $ "NaN predictions " <> show theta
  | otherwise   = negate . M.sum $ ys' * yhat - ys' * log ys' - exp yhat
  where
    ys'      = delay ys
    yhat     = evalTree xss theta tree
    notValid = M.any (<0)

nll ROXY mXerr mYerr xss ys tree theta
  | isNothing mXerr || isNothing mYerr = error "Can't calculate ROXY nll without x,y-errors."
  | p < num_params + 3 = error "We need 3 additional parameters for ROXY."
  | n > 1              = error "For ROXY dataset must contain a single variable."
  | otherwise          = 0.5 * M.sum neglogP
  where
    (Sz p')      = M.size theta
    (Sz2 m n) = M.size xss
    p            = fromIntegral p'
    num_params   = countParams tree
    x0           = xss <! 0
    xErr0        = (fromJust mXerr) <! 0
    yErr         = fromJust mYerr
    (sig, mu_gauss, w_gauss) = (theta ! num_params, theta ! (num_params + 1), theta ! (num_params + 2))

    -- TODO: if this hangs, you must do map, etc.
    applyDer :: Op -> Array D Ix1 Double -> Array D Ix1 Double -> Array D Ix1 Double -> Array D Ix1 Double -> Array D Ix1 Double
    applyDer Add l dl r dr = dl+dr
    applyDer Sub l dl r dr = dl-dr
    applyDer Mul l dl r dr = l*dr + r*dl
    applyDer Div l dl r dr = (dl*r - dr*l) / (l^2)
    applyDer Power l dl r dr = l ** (r.-1) * (r*dl + l * log l * dr)
    applyDer PowerAbs l dl r dr = (abs l ** r) * (dr * log (abs l) + r * dl / l)
    applyDer AQ l dl r dr = ((1 +. r*r) * dl - l * r * dr) / M.map (**1.5) (1 +. r*r)

    (yhat, grad) = cata alg tree
      where
        alg (Var ix)   = (x0, M.replicate compMode (Sz m) 1)
        alg (Param ix) = (M.replicate compMode (Sz m) (theta M.! ix), M.replicate compMode (Sz m) 0)
        alg (Const x)  = (M.replicate compMode (Sz m) x, M.replicate compMode (Sz m) 0)
        alg (Uni f (val, der))  = (M.map (evalFun f) val, M.map (derivative f) val * der)
        alg (Bin op (valL, derL) (valR, derR)) = (M.zipWith (evalOp op) valL valR, applyDer op valL derL valR derR)

    f            = M.map (logBase 10) (abs yhat)
    fprime       = grad / (log 10 *. yhat) * x0 .* log 10
    logX         = M.map (logBase 10) x0
    logY         = M.map (logBase 10) (delay ys)
    logXErr      = (xErr0 / (x0 .* log 10)) ^ (2  :: Int)
    logYErr      = (delay yErr / (delay ys .* log 10)) ^ (2  :: Int)
    -- nll
    w_gauss2     = w_gauss ^ 2
    s2           = delay $ logYErr .+ sig^2
    den          = fprime ^ 2 .* w_gauss2 * logXErr + s2 * (w_gauss2 +. logXErr)

    neglogP = log (2 * pi)
        +. log den
        + (w_gauss2 *. (f - logY)*(f - logY)
           + logXErr * (fprime * (mu_gauss -. logX) + f - logY)^2
           + s2 * (logX .- mu_gauss)^2) / den



nll' :: Distribution -> PVector -> SRVector -> SRVector -> Double
nll' Gaussian yErr yhat ys = 0.5*(err + log (2*pi*M.sum yErr))
  where
    (Sz m') = M.size ys
    m    = fromIntegral m'
    err  = M.sum $ ((delay ys - yhat) / (delay yErr)) ^ (2 :: Int)

nll' Bernoulli _ yhat ys = negate . M.sum $ ys * yhat - log (1 + exp yhat)
nll' Poisson _ yhat ys   = negate . M.sum $ ys * yhat - ys * log ys - exp yhat
{-# INLINE nll' #-}

-- | Prediction for different distributions
predict :: Distribution -> Fix SRTree -> PVector -> SRMatrix -> SRVector
predict Gaussian  tree theta xss = evalTree xss theta tree
predict Bernoulli tree theta xss = logistic $ evalTree xss theta tree
predict Poisson   tree theta xss = exp $ evalTree xss theta tree

-- | Gradient of the negative log-likelihood
gradNLL :: Distribution -> Maybe SRMatrix -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (Double, SRVector)
gradNLL Gaussian mXerr mYerr xss ys tree theta =
  (nll Gaussian mXerr mYerr xss ys tree theta, delay grad)
  where
    (Sz m)       = M.size ys
    (Sz p)       = M.size theta
    ys'          = delay ys
    (yhat, grad) = reverseModeUnique xss theta ys' yErr id tree
    yErr         = case mYerr of
                     Nothing -> delay $ M.replicate @S (M.getComp xss) (Sz m) est
                     Just e  -> delay e
    est          = fromIntegral (m - p)

gradNLL Bernoulli mXerr mYerr xss ys tree theta
  | M.any (\x -> x /= 0 && x /= 1) ys = error "For Bernoulli distribution the output must be either 0 or 1."
  | otherwise                         = (nll Bernoulli mXerr mYerr xss ys tree theta, delay grad)
  where
    (yhat, grad) = reverseModeUnique xss theta (delay ys) (M.replicate (getComp xss) (M.size ys) 1) logistic tree
    grad'        = M.map nanTo0 grad
    nanTo0 x     = if isNaN x then 0 else x

gradNLL Poisson mXerr mYerr xss ys tree theta
  | M.any (<0) ys    = error "For Poisson distribution the output must be non-negative."
 -- | M.any isNaN grad = error $ "NaN gradient " <> show grad
  | otherwise        = (nll Poisson mXerr mYerr xss ys tree theta, delay grad)
  where
    (yhat, grad) = reverseModeUnique xss theta (delay ys) (M.replicate (getComp xss) (M.size ys) 1) exp tree

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
                      pure g

-- | Gradient of the negative log-likelihood
--Array B Ix1 (Int, Int, Int, Double)
gradNLLArr :: Distribution -> Maybe SRMatrix -> Maybe PVector -> SRMatrix -> PVector -> [(Int,(Int, Int, Int, Double))] -> IntMap.IntMap Int -> VS.Vector Double -> (Double, SRVector)
gradNLLArr Gaussian mXerr mYerr xss ys tree j2ix theta =
  (nll' Gaussian yErr yhat (delay ys), delay grad)
  where
    (Sz m)       = M.size ys
    p            = VS.length theta
    ys'          = delay ys
    (yhat, grad) = reverseModeUniqueArr xss theta ys' (delay yErr) id tree j2ix
    yErr         = case mYerr of
                     Nothing -> M.replicate (getComp xss) (Sz m) est
                     Just e  -> e
    est          = fromIntegral (m - p)

gradNLLArr Bernoulli mXerr mYerr xss (delay -> ys) tree j2ix theta
  | M.any (\x -> x /= 0 && x /= 1) ys = error "For Bernoulli distribution the output must be either 0 or 1."
  | otherwise                         = (nll' Bernoulli yErr yhat ys, delay grad)
  where
    (yhat, grad) = reverseModeUniqueArr xss theta ys (M.replicate (getComp xss) (M.size ys) 1) logistic tree j2ix
    grad'        = M.map nanTo0 grad
    (Sz m)       = M.size ys
    --err          = logistic yhat - ys
    nanTo0 x     = if isNaN x then 0 else x
    yErr         = case mYerr of
                     Nothing -> M.replicate (getComp xss) (Sz m) 1
                     Just e  -> e

gradNLLArr Poisson mXerr mYerr xss (delay -> ys) tree j2ix theta
  | M.any (<0) ys    = error "For Poisson distribution the output must be non-negative."
 -- | M.any isNaN grad = error $ "NaN gradient " <> show grad
  | otherwise        = (nll' Poisson yErr yhat ys, delay grad)
  where
    (yhat, grad) = reverseModeUniqueArr xss theta ys (M.replicate (getComp xss) (M.size ys) 1) exp tree j2ix
    --err          = exp yhat - ys
    (Sz m)       = M.size ys
    yErr         = case mYerr of
                     Nothing -> M.replicate (getComp xss) (Sz m) 1
                     Just e  -> e

-- | TODO: this is "hacky" and should be improved
gradNLLArr ROXY mXerr mYerr xss ys tree j2ix theta =
   (f, delay grad)
  where
    p      = VS.length theta
    f      = nll ROXY mXerr mYerr xss ys tree' (M.fromStorableVector compMode theta)
    grad   = makeArray @S (getComp xss) (Sz p) finiteDiff
    eps    = 1e-6
    tree'  = (arr2tree $ IntMap.fromList tree)

    arr2tree :: IntMap.IntMap (Int, Int, Int, Double) -> Fix SRTree
    arr2tree arr = go 0
      where
        go ix = let (opType, opCode, ix, v) = arr IntMap.! ix
                in case opType of
                    0 -> case opCode of
                            0 -> Fix $ Var ix
                            1 -> Fix $ Param ix
                            2 -> Fix $ Const v
                    1 -> Fix $ Uni (toEnum opCode) $ go (2*ix + 1)
                    2 -> Fix $ Bin (toEnum opCode) (go $ 2*ix + 1) (go $ 2*ix + 2)

    finiteDiff ix = unsafePerformIO $ do
                      print (showExpr tree')
                      theta' <- Mut.thaw (M.fromStorableVector compMode theta)
                      v <- Mut.readM theta' ix
                      Mut.writeM theta' ix (v + eps)
                      theta'' <- Mut.freezeS theta'
                      let f' = nll ROXY mXerr mYerr xss ys tree' theta''
                      pure $ (f - f') / eps

-- | Gradient of the negative log-likelihood
gradNLLNonUnique :: Distribution -> Maybe SRMatrix -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> (Double, SRVector)
gradNLLNonUnique Gaussian mXerr mYerr xss ys tree theta =
  (nll Gaussian mXerr mYerr xss ys tree theta, delay grad)
  where
    (Sz m)       = M.size ys
    (Sz p)       = M.size theta
    ys'          = delay ys
    (yhat, grad) = forwardMode xss theta err tree
    err          = (predict Gaussian tree theta xss - ys') / (delay yErr)
    yErr         = case mYerr of
                     Nothing -> M.replicate (getComp xss) (Sz m) est
                     Just e  -> e
    est          = fromIntegral (m - p)

gradNLLNonUnique Bernoulli mXerr mYerr xss ys tree theta
  | M.any (\x -> x /= 0 && x /= 1) ys = error "For Bernoulli distribution the output must be either 0 or 1."
  | otherwise                         = (nll Bernoulli mXerr mYerr xss ys tree theta, delay grad)
  where
    (yhat, grad) = forwardMode xss theta err tree
    grad'        = M.map nanTo0 grad
    err          = predict Bernoulli tree theta xss - delay ys
    nanTo0 x     = if isNaN x then 0 else x

gradNLLNonUnique Poisson mXerr mYerr xss ys tree theta
  | M.any (<0) ys    = error "For Poisson distribution the output must be non-negative."
  -- | M.any isNaN grad = error $ "NaN gradient " <> show grad
  | otherwise        = (nll Poisson mXerr mYerr xss ys tree theta, delay grad)
  where
    (yhat, grad) = forwardMode xss theta err tree
    err          = predict Poisson tree theta xss - delay ys

gradNLLNonUnique ROXY mXerr mYerr xss ys tree theta =
   (f, delay grad)
  where
    (Sz p) = M.size theta
    yhat   = predict Gaussian tree theta xss
    f      = nll ROXY mXerr mYerr xss ys tree theta
    grad   = makeArray @S (getComp xss) (Sz p) finiteDiff
    eps    = 1e-6

    finiteDiff ix = unsafePerformIO $ do
                      theta' <- Mut.thaw theta
                      v <- Mut.readM theta' ix
                      Mut.writeM theta' ix (v + eps)
                      theta'' <- Mut.freezeS theta'
                      let f' = nll ROXY mXerr mYerr xss ys tree theta''
                      pure $ (f - f')/eps

-- | Fisher information of negative log-likelihood
fisherNLL :: Distribution -> Maybe SRMatrix -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> SRVector
fisherNLL ROXY mXerr mYerr xss ys tree theta = makeArray cmp (Sz p) finiteDiff
  where
    cmp    = getComp xss
    (Sz m) = M.size ys
    (Sz p) = M.size theta
    f      = nll ROXY mXerr mYerr xss ys tree theta
    eps = 1e-6
    finiteDiff ix = unsafePerformIO $ do
                      theta' <- Mut.thaw theta
                      v <- Mut.readM theta' ix
                      Mut.writeM theta' ix (v + eps)
                      thetaPlus <- Mut.freezeS theta'
                      Mut.writeM theta' ix (v - eps)
                      thetaMinus <- Mut.freezeS theta'
                      let fPlus     = nll ROXY mXerr mYerr xss ys tree thetaPlus
                          fMinus    = nll ROXY mXerr mYerr xss ys tree thetaMinus
                      pure $ (fPlus + fMinus - 2*f)/(eps*eps)

fisherNLL dist mXerr mYerr xss ys tree theta = makeArray cmp (Sz p) build
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
                    Gaussian  -> (yhat, M.replicate compMode (Sz m) 1)
                    Bernoulli -> (logistic yhat, phi*(M.replicate compMode (Sz m) 1 - phi))
                    Poisson   -> (exp yhat, phi)

-- | Hessian of negative log-likelihood
--
-- Note, though the Fisher is just the diagonal of the return of this function
-- it is better to keep them as different functions for efficiency
hessianNLL :: Distribution -> Maybe SRMatrix -> Maybe PVector -> SRMatrix -> PVector -> Fix SRTree -> PVector -> SRMatrix
hessianNLL ROXY mXerr mYerr xss ys tree theta = undefined
hessianNLL dist mXerr mYerr xss ys tree theta = makeArray cmp (Sz (p :. p)) build
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

