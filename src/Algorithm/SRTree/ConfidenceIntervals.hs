{-# language ViewPatterns, ScopedTypeVariables, MultiWayIf, FlexibleContexts #-}
-------------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.SRTree.ConfidenceIntervals
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
-- Functions to optimize the parameters of an expression.
-------------------------------------------------------------------------------
module Algorithm.SRTree.ConfidenceIntervals where

import Statistics.Distribution ( ContDistr(quantile) )
import Statistics.Distribution.StudentT ( studentT )
import Statistics.Distribution.FDistribution ( fDistribution )
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Storable as VS
import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Recursion ( cata )
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.Opt ( minimizeNLL, minimizeNLLWithFixedParam )
import Data.List ( sortOn, nubBy, transpose )
import Data.Maybe ( fromMaybe )
import Algorithm.SRTree.NonlinearOpt
import Algorithm.SRTree.Utils
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad.Catch ( catch, SomeException )

import Debug.Trace ( trace, traceShow )

-- | profile likelihood algorithms: Bates (classical), ODE (faster), Constrained (fastest)
-- The Constrained approach returns only the endpoints.
data PType = Bates | ODE | Constrained deriving (Show, Read, Eq)

-- | Confidence Interval using Laplace approximation or profile likelihood.
data CIType = Laplace BasicStats | Profile BasicStats [ProfileT]

-- | Basic stats of the data: covariance of parameters, correlation, standard errors
data BasicStats = MkStats
  { _cov :: Columns
  , _corr :: Columns
  , _stdErr :: Target
  } deriving (Eq, Show)

-- | a confience interval is composed of the point estimate (`est_`), lower bound (`_lower_`)
-- and upper bound (`upper_`)
data CI = CI
  { est_ :: Double
  , lower_ :: Double
  , upper_ :: Double
  } deriving (Eq, Show, Read)

-- | A profile likelihood is composed of a vector of tau values that traces the likelihood,
-- the matrix of thetas for each profile, the local optima, and two splines that converts
-- taus to theta and vice-versa.
data ProfileT = ProfileT
  { _taus :: Target
  , _thetas :: Columns
  , _opt :: Double
  , _tau2theta :: Double -> Double
  , _theta2tau :: Double -> Double
  }

-- shows the CI with n places
showCI :: Int -> CI -> String
showCI n (CI x l h) = show (rnd l) <> " <= " <> show (rnd x) <> " <= " <> show (rnd h)
  where rnd = (/10^n) . (fromIntegral . round) . (*10^n)

printCI :: Int -> CI -> IO ()
printCI n = putStrLn . showCI n

-- | Calculates the confidence interval of the parameters using
-- Laplace approximation or Profile likelihood
paramCI :: CIType -> Int -> Target -> Double -> [CI]
paramCI (Laplace stats) nSamples theta alpha = zipWith3 CI (U.toList theta) lows highs
  where
    -- the Laplace approximation is theta +/- t(1-alpha/2) * standard error
    k = U.length theta
    t = quantile (studentT . fromIntegral $ nSamples - k) (1 - alpha / 2.0)
    stdErr = _stdErr stats
    lows = U.toList $ U.zipWith (-) theta $ U.map (*t) stdErr
    highs = U.toList $ U.zipWith (+) theta $ U.map (*t) stdErr

paramCI (Profile stats profiles) nSamples _ alpha = zipWith3 CI theta lows highs
  where
    -- for the profile likelihood we use the square root of the F-distribution with (1-alpha)
    k = length theta
    t = sqrt $ quantile (fDistribution k (fromIntegral $ nSamples - k)) (1 - alpha)
    stdErr = _stdErr stats
    lows = map (`_tau2theta` (-t)) profiles
    highs = map (`_tau2theta` t) profiles
    theta = map _opt profiles

-- | calculates the prediction confidence interval using Laplace approximation or profile likelihood.
-- predictionCI
predictionCI :: CIType -> Distribution -> (Columns -> Target) -> (Columns -> [Target]) -> (CI -> Target -> Fix SRTree -> (Double -> Double, Double)) -> Columns -> Fix SRTree -> Target -> Double -> [CI] -> [CI]
predictionCI (Laplace stats) _ predFun jacFun _ xss tree theta alpha _ = zipWith3 CI yhat lows highs
  where
    yhat = U.toList $ predFun xss
    jac' = jacFun xss
    jac = transpose (map U.toList jac')

    n = length yhat
    k = U.length theta
    t = quantile (studentT . fromIntegral $ n - k) (1 - alpha / 2.0)

    covMat = toRowMajor (_cov stats)
    covs = [ [ covMat U.! (i * k + j) | j <- [0 .. k-2] ] | i <- [0 .. k-2] ]

    lows = zipWith (-) yhat $ map (*t) resStdErr
    highs = zipWith (+) yhat $ map (*t) resStdErr

    -- Manual dot products for std error mapping slices
    getResStdError row = sqrt $ sum [ row !! i * (sum [ (covs !! i !! j) * (row !! j) | j <- [0 .. length row - 1] ]) | i <- [0 .. length row - 1] ]
    resStdErr = map (getResStdError . init) jac

predictionCI (Profile _ _) dist predFun _ profFun xss tree theta alpha estPIs = zipWith3 f estPIs yhat xss'
  where
    yhat = U.toList $ predFun xss
    theta' = VS.generate (U.length theta) (\i -> theta U.! i)
    k = U.length theta
    n = length yhat
    t = sqrt $ quantile (fDistribution k (fromIntegral $ n - k)) (1 - alpha)

    theta0 = calcTheta0 dist tree
    xss' = map U.toList (getRows xss)

    f estPI yh xs = let
        t' = replaceParam0 tree $ evalVar xs theta0
        (spline, yh') = profFun estPI (U.generate (VS.length theta') (\i -> if i == 0 then yh else theta' VS.! i)) t'
      in CI yh' (spline (-t)) (spline t)

-- inverse function of the distributions
inverseDist :: Floating p => Distribution -> p -> p
inverseDist Gaussian y = y
inverseDist Bernoulli y = log (y/(1-y))
inverseDist Poisson y = log y

-- rewrite the tree by fixing theta 0 to optimal value
replaceParam0 :: Fix SRTree -> Fix SRTree -> Fix SRTree
replaceParam0 tree t0 = cata alg tree
  where
    alg (Var ix) = Fix $ Var ix
    alg (Param 0) = t0
    alg (Param ix) = Fix $ Param ix
    alg (Const c) = Fix $ Const c
    alg (Uni g t) = Fix $ Uni g t
    alg (Bin op l r) = Fix $ Bin op l r

evalVar :: [Double] -> Fix SRTree -> Fix SRTree
evalVar xs = cata alg
  where
    alg (Var ix) = Fix $ Const (xs !! ix)
    alg (Param ix) = Fix $ Param ix
    alg (Const c) = Fix $ Const c
    alg (Uni g t) = Fix $ Uni g t
    alg (Bin op l r) = Fix $ Bin op l r

calcTheta0 :: Distribution -> Fix SRTree -> Fix SRTree
calcTheta0 dist tree = case cata alg tree of
  Left g -> g $ inverseDist dist (Fix $ Param 0)
  Right _ -> error "No theta0?"
  where
    alg (Var ix) = Right $ Fix $ Var ix
    alg (Param 0) = Left id
    alg (Param ix) = Right $ Fix $ Param ix
    alg (Const c) = Right $ Fix $ Const c
    alg (Uni g t) = case t of
      Left f -> Left $ f . evalInverse g
      Right v -> Right $ evalFun g v
    alg (Bin op l r) = case l of
      Left f -> case r of
        Left _ -> error "This shouldn't happen!"
        Right v -> Left $ f . invright op v
      Right vl -> case r of
        Left g -> Left $ g . invleft op vl
        Right vr -> Right $ evalOp op vl vr

-- tau0, tau1 theta0, thetaX = tau1 theta0 / tau0
getStatsFromModel :: Distribution -> Maybe Target -> Columns -> Target -> Fix SRTree -> Target -> BasicStats
getStatsFromModel dist mYerr xss ys tree theta = MkStats cov corr stdErr
  where
    k = U.length theta
    n = U.length ys
    nParams = fromIntegral k
    ssr = compileLoss xss (buildLoss MSE (fromIntegral n) tree) ys theta
    ident = fromRowMajor k k (U.generate (k * k) (\ix -> let (i, j) = ix `divMod` k in if i == j then 1.0 else 0.0))

    hess = hessianNLL dist mYerr xss ys tree theta

    fexcept :: SomeException -> IO Columns
    fexcept e = trace ("cov NegDef" <> show (toRowMajor hess)) $ pure ident

    cov = unsafePerformIO $ catch (invChol hess) fexcept

    covMat = toRowMajor cov
    stdErr = U.generate k (\ix -> sqrt $ covMat U.! (ix * k + ix))

    stdErrSq = case outer stdErr stdErr of
      Right v -> v
      Left _ -> []

    stdErrSqMat = toRowMajor stdErrSq
    corr = fromRowMajor k k $ U.generate (k * k) (\ix -> covMat U.! ix / stdErrSqMat U.! ix)

-- Create splines for profile-t
createSplines :: Target -> Columns -> Double -> Double -> Int -> (Double -> Double, Double -> Double)
createSplines taus thetas se tau_max ix
  | n < 2 = (genSplineFun [(-tau_max, -se), (tau_max, se)], genSplineFun [(-se, 0), (se, 1)])
  | otherwise = (tau2theta, theta2tau)
  where
    n = U.length taus
    cols = getCol ix thetas
    nubOnFirst = nubBy (\x y -> fst x == fst y)
    tau2theta = genSplineFun $ nubOnFirst $ sortOnFirst taus cols
    theta2tau = genSplineFun $ nubOnFirst $ sortOnFirst cols taus

getCol :: Int -> Columns -> Target
getCol ix mtx = U.fromList [ (mtx !! j) U.! ix | j <- [0 .. length mtx - 1] ]
{-# inline getCol #-}

sortOnFirst :: Target -> Target -> [(Double, Double)]
sortOnFirst xs ys = sortOn fst $ zip (U.toList xs) (U.toList ys)
{-# inline sortOnFirst #-}

splinesSketches :: Double -> Target -> Target -> (Double -> Double) -> (Double -> Double)
splinesSketches tauScale (U.toList -> tau) (U.toList -> theta) theta2tau
  | length tau < 2 = id
  | otherwise = genSplineFun gpq
  where
    gpq = sortOn fst [ (x, acos y') | (x, y) <- zip tau theta, let y' = theta2tau y / tauScale, abs y' < 1 ]

approximateContour :: Int -> Int -> [ProfileT] -> Int -> Int -> Double -> [(Double, Double)]
approximateContour nParams nPoints profs ix1 ix2 alpha = go 0
  where
    (prof1, prof2) = (profs !! ix1, profs !! ix2)
    (tau2theta1, theta2tau1) = (_tau2theta prof1, _theta2tau prof1)
    (tau2theta2, theta2tau2) = (_tau2theta prof2, _theta2tau prof2)

    tauScale = sqrt (fromIntegral nParams * quantile (fDistribution nParams (fromIntegral nPoints - fromIntegral nParams)) (1 - alpha))
    splineG1 = splinesSketches tauScale (_taus prof2) (getCol ix1 (_thetas prof2)) theta2tau1
    splineG2 = splinesSketches tauScale (_taus prof1) (getCol ix2 (_thetas prof1)) theta2tau2

    angles = [ (0, splineG2 1), (splineG1 1, 0), (pi, splineG2 (-1)), (splineG1 (-1), pi) ]
    applyIfNeg (x, y) = if y < 0 then (-x, -y) else (x ,y)
    points' = [applyIfNeg ((x+y)/2, x - y) | (x, y) <- angles]
    points = sortOn fst $ (points' <> (\(x,y) -> [(x + 2*pi, y)]) (head points'))
    splineAD = genSplineFun points

    fmod a b = a - b * fromIntegral (truncate (a / b))

    tot = 100
    go 100 = []
    go ix = (p, q) : go (ix+1)
      where
        ai = fromIntegral ix * 2 * pi / 99 - pi
        di = splineAD ai
        t1i = tauScale * cos (ai + di)
        t2i = tauScale * cos (ai - di)
        p = tau2theta1 t1i
        q = tau2theta2 t2i
