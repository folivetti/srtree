{-# language ViewPatterns, ScopedTypeVariables, MultiWayIf, FlexibleContexts, BangPatterns #-}
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
import qualified Data.Vector.Generic as G
import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Recursion ( cata )
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.Compile
import Data.List ( sortOn, nubBy )
import Data.Maybe ( listToMaybe )
import Algorithm.SRTree.Utils
import Numeric.Optimization.NLOPT
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad.Catch ( catch, SomeException )
import Debug.Trace ( trace )

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
    -- for the profile likelihood we use the square root of the F-distribution
    -- with 1 numerator df (each parameter is profiled individually)
    k = length theta
    t = sqrt $ quantile (fDistribution 1 (fromIntegral $ nSamples - k)) (1 - alpha)
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
    k = U.length theta
    n = length yhat
    t = quantile (studentT . fromIntegral $ n - k) (1 - alpha / 2.0)

    covMat = toRowMajor (_cov stats)
    nCov = k - 1

    lows = zipWith (-) yhat $ map (*t) resStdErr
    highs = zipWith (+) yhat $ map (*t) resStdErr

    getResStdError row =
      sqrt $ U.sum $ U.generate nCov $ \i ->
        (row U.! i) * U.sum (U.zipWith (*) row (U.slice (i * k) nCov covMat))
    resStdErr = map (getResStdError . U.slice 0 nCov) (getRows jac')

predictionCI (Profile _ _) dist predFun _ profFun xss tree theta alpha estPIs = zipWith3 f estPIs yhat xss'
  where
    yhat = U.toList $ predFun xss
    k = U.length theta
    n = length yhat
    t = sqrt $ quantile (fDistribution k (fromIntegral $ n - k)) (1 - alpha)

    theta0 = calcTheta0 dist tree
    xss' = getRows xss

    f estPI yh xs = let
        t' = replaceParam0 tree $ evalVar xs theta0
        (spline, yh') = profFun estPI (theta U.// [(0, yh)]) t'
      in CI yh' (spline (-t)) (spline t)

-- inverse function of the distributions
inverseDist :: Floating p => Distribution -> p -> p
inverseDist Gaussian  y = y
inverseDist Bernoulli y = log (y/(1-y))
inverseDist Poisson   y = log y
inverseDist _         y = y

-- rewrite the tree by fixing theta 0 to optimal value
replaceParam0 :: Fix SRTree -> Fix SRTree -> Fix SRTree
replaceParam0 tree t0 = cata alg tree
  where
    alg (Var ix) = Fix $ Var ix
    alg (Param 0) = t0
    alg (Param ix) = Fix $ Param ix
    alg (Const c) = Fix $ Const c
    alg (Y ix)    = Fix $ Y ix
    alg (Uni g t) = Fix $ Uni g t
    alg (Bin op l r) = Fix $ Bin op l r

evalVar :: Target -> Fix SRTree -> Fix SRTree
evalVar xs = cata alg
  where
    alg (Var ix) = Fix $ Const (xs U.! ix)
    alg (Param ix) = Fix $ Param ix
    alg (Const c) = Fix $ Const c
    alg (Y ix)    = Fix $ Y ix
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
    alg (Y ix)    = Right $ Fix $ Y ix
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

-- | Recompute standard errors from the Hessian at a given theta.
-- Used when a profile walk restarts from a new optimum.
recomputeStdErr :: EvalTree -> Target -> Target
recomputeStdErr et t = stdErr
  where
    k = U.length t
    ident = fromRowMajor k k (U.generate (k * k) (\ix -> let (i, j) = ix `divMod` k in if i == j then 1.0 else 0.0))
    hess = ctHessianNLL et t
    cov = unsafePerformIO $ catch (invChol hess) (\(_ :: SomeException) -> pure ident)
    covMat = toRowMajor cov
    stdErr = U.generate k (\ix -> sqrt $ abs (covMat U.! (ix * k + ix)))

-- calculate the profile likelihood of every parameter
-- restartLimit bounds recursive restarts when the optimizer finds a better point mid-profile
getAllProfiles :: PType -> EvalTree -> Target -> Target -> [CI] -> Double -> [ProfileT]
getAllProfiles ptype et theta stdErr estCIs alpha
  -- Defensive: if theta is too short for the EvalTree's distribution,
  -- return empty profiles instead of crashing (e.g. MSE loss with Gaussian dist)
  | U.length theta < 2 = []
  | otherwise = go 0 et theta stdErr estCIs
  where
    restartLimit = 5 :: Int

    go restarts et' theta' stdErr' estCIs'
      | restarts >= restartLimit = profileAll restarts et' theta' stdErr' estCIs'
      | otherwise = profileAll restarts et' theta' stdErr' estCIs'

    profileAll restarts et' theta' stdErr' estCIs' = go' 0 []
      where
        k = U.length theta'
        n = ctRows et'
        -- For profiling a single parameter, the threshold is chi2_1 (1 df),
        -- not chi2_k (k df). The profile likelihood ratio for ONE parameter
        -- follows chi2_1 under H0.
        tau_max  = sqrt $ quantile (fDistribution 1 (n - k)) (1 - 0.01)
        nll_opt   = ctNLL et' (ctOptimizer et' theta')
        chi2_1    = quantile (fDistribution 1 (n - k)) (1 - alpha)
        -- Profile likelihood CI: 2*(L(theta_hat) - L(theta)) <= chi2_1
        -- => ctNLL(theta) <= ctNLL(theta_hat) + chi2_1/2
        -- So tau_max for the constrained method = chi2_1/2
        tau_max'  = chi2_1 / 2

        -- If estCIs is empty, compute Laplace CIs as initial estimates
        -- (needed by ODE fallback for the last Gaussian parameter)
        estCIs'' = if null estCIs'
                     then let ident = U.generate (k * k) (\ix -> let (i, j) = ix `divMod` k in if i == j then 1.0 else 0.0)
                              hess = ctHessianNLL et' theta'
                              cov  = unsafePerformIO $ catch (invChol hess) (\(_ :: SomeException) -> pure (fromRowMajor k k ident))
                              covMat = toRowMajor cov
                              se = U.generate k (\ix -> sqrt $ abs (covMat U.! (ix * k + ix)))
                              tVal = quantile (studentT . fromIntegral $ n - k) (1 - alpha / 2.0)
                          in  map (\ix -> CI (theta' U.! ix) ((theta' U.! ix) - tVal * (se U.! ix)) ((theta' U.! ix) + tVal * (se U.! ix))) [0..k-1]
                     else estCIs'

        profFun ix = case ptype of
                        Bates       -> getProfile      et' theta' (stdErr' U.! ix) tau_max ix
                        ODE         -> getProfileODE   et' theta' (stdErr' U.! ix) (estCIs'' !! ix) tau_max ix
                        Constrained -> getProfileCnstr et' theta' (stdErr' U.! ix) tau_max' ix

        go' ix acc | ix == k = acc
        go' ix acc
          | ix == k-1 && ptype == Constrained && ctDist et' == Gaussian =
              case getProfileODE et' theta' (stdErr' U.! ix) (estCIs'' !! ix) tau_max ix of
                Left t  -> let tOpt = ctOptimizer et' t; se'' = recomputeStdErr et' tOpt
                           in  go (restarts + 1) et' tOpt se'' estCIs'
                Right p -> go' (ix + 1) (acc <> [p])
          | otherwise =
              case profFun ix of
                Left t  -> let tOpt = ctOptimizer et' t; se'' = recomputeStdErr et' tOpt
                           in  go (restarts + 1) et' tOpt se'' estCIs'
                Right p -> go' (ix + 1) (acc <> [p])

-- calculates the profile likelihood of a single parameter
getProfile :: EvalTree -> Target -> Double -> Double -> Int -> Either Target ProfileT
getProfile et theta stdErr_i tau_max ix
  | stdErr_i == 0.0 = pure $ ProfileT (U.fromList [-tau_max, tau_max]) [theta, theta] (theta U.! ix) (const (theta U.! ix)) (const tau_max)
  | otherwise =
  do negDelta <- go kmax (-stdErr_i / 8) 0 1 mempty
     let !negLen = length (fst negDelta)
         !negTauRange = if null (fst negDelta) then (0,0) else (minimum (fst negDelta), maximum (fst negDelta))
     posDelta <- go kmax  (stdErr_i / 8) 0 1 p0
     let !posLen = length (fst posDelta)
         !posTauRange = if null (fst posDelta) then (0,0) else (minimum (fst posDelta), maximum (fst posDelta))
     let (taus', thetas') = negDelta <> posDelta
         taus    = U.fromList taus'
         thetas  = thetas'
         (tau2theta, theta2tau) = createSplines taus thetas stdErr_i tau_max ix optTh
     pure $ ProfileT taus thetas optTh tau2theta theta2tau
   where
    p0        = ([0], [theta_opt])
    kmax      = 500
    nll_opt   = ctNLL et theta_opt
    theta_opt = ctOptimizer et theta
    optTh     = theta_opt U.! ix
    minimizer = ctOptimizerFixed et ix

    go 0 delta _ _         acc = Right acc
    go k delta t inv_slope acc@(taus, thetas)
      | isNaN inv_slope     = Right acc
      | nll_cond < nll_opt - 1e-6 * abs nll_opt  = Left theta_t
      | abs tau > tau_max   = Right acc'

      | otherwise           = go (k-1) delta (t + inv_slope) inv_slope' acc'
      where
        t_delta     = (theta_opt U.! ix) + delta * (t + inv_slope)
        theta_delta = updateS theta_opt [(ix, t_delta)]
        theta_t     = minimizer theta_delta
        (nll_cond, grad) = ctGradNLL et theta_t
        zv          = grad U.! ix
        -- For LeastSquares, the correct profile likelihood statistic is
        -- n * log(MSE(t)/MSE(opt)) ~ chi2_1, not 2*(MSE(t) - MSE(opt)).
        tau         = case ctDist et of
                        LeastSquares ->
                          let nD = fromIntegral (ctRows et) :: Double
                              r  = max nll_cond 1e-30 / max nll_opt 1e-30
                          in  signum delta * sqrt (max 0 (nD * log r))
                        _ -> signum delta * sqrt (max 0 (2*nll_cond - 2*nll_opt))
        inv_slope'  = if abs zv < 1e-12 * abs stdErr_i
                         then min 4.0 . max 0.0625 $ abs (delta * 8)
                         else min 4.0 . max 0.0625 . abs $ (tau / (stdErr_i * zv))
        acc'        = if nll_cond == nll_opt || maybe False (tau ==) (listToMaybe taus) || isNaN tau
                         then acc
                         else (tau:taus, theta_t:thetas)

-- Based on https://insysbio.github.io/LikelihoodProfiler.jl/latest/
-- Borisov, Ivan, and Evgeny Metelkin. "Confidence intervals by constrained optimization—An algorithm and software package for practical identifiability analysis in systems biology." PLOS Computational Biology 16.12 (2020): e1008495.
getProfileCnstr :: EvalTree -> Target -> Double -> Double -> Int -> Either Target ProfileT
getProfileCnstr et theta stdErr_i tau_max ix
  | stdErr_i == 0.0 = pure $ ProfileT taus thetas theta_i (const theta_i) (const tau_max)
  | otherwise       = pure $ ProfileT taus thetas theta_i tau2theta (const tau_max)
  where
    taus     = U.fromList [-tau_max, tau_max]
    thetas   = [theta, theta]
    theta_i  = theta U.! ix
    getPoint = getEndPoint et theta tau_max stdErr_i ix
    leftPt   = getPoint True
    rightPt  = getPoint False
    tau2theta tau = if tau < 0 then leftPt else rightPt

getEndPoint :: EvalTree -> Target -> Double -> Double -> Int -> Bool -> Double
getEndPoint et theta tau_max stdErr_i ix isLeft
  | isNaN mle   = 0/0  -- NaN: MLE itself is NaN
  | f mle >= 0 = 0/0  -- NaN: MLE violates constraint
  | isLeft && f lo <= 0 = 0/0  -- NaN: constraint satisfied at left bound
  | not isLeft && f hi <= 0 = 0/0  -- NaN: constraint satisfied at right bound
  | isLeft     = bisect lo mle 0
  | otherwise  = bisect mle hi 0
  where
    n = U.length theta
    theta_opt = ctOptimizer et theta
    nll_opt   = ctNLL et theta_opt
    loss_crit = nll_opt + tau_max
    mle       = theta_opt U.! ix
    -- Use a wide search range: 50x the standard error, with a minimum of 50x |mle|
    -- This ensures we don't miss the CI boundary for parameters near zero
    searchScale = max (abs mle * 50) (stdErr_i * 50)
    lo        = mle - searchScale
    hi        = mle + searchScale

    -- Profiled NLL: fix theta[ix]=t, re-optimize all other params
    f t = let x = U.generate n (\j -> if j == ix then t else theta_opt U.! j)
              reopt = ctOptimizerFixed et ix (G.convert x)
          in ctNLL et reopt - loss_crit

    bisect a b k
      | k >= 60 || abs (b - a) < 1e-12 = (a + b) / 2
      | f mid <= 0 = if isLeft then bisect a mid (k+1) else bisect mid b (k+1)
      | otherwise  = if isLeft then bisect mid b (k+1) else bisect a mid (k+1)
      where mid = (a + b) / 2
{-# INLINE getEndPoint #-}

-- Based on
-- Jian-Shen Chen & Robert I Jennrich (2002) Simple Accurate Approximation of Likelihood Profiles,
-- Journal of Computational and Graphical Statistics, 11:3, 714-732, DOI: 10.1198/106186002493
getProfileODE :: EvalTree -> Target -> Double -> CI -> Double -> Int -> Either Target ProfileT
getProfileODE et theta stdErr_i estCI tau_max ix
  | stdErr_i == 0.0 = pure dflt
  | otherwise = let (taus', thetas') = solLeft <> ([0], [theta_opt]) <> solRight
                    taus   = U.fromList taus'
                    thetas = thetas'
                    (tau2theta, theta2tau) = createSplines taus thetas stdErr_i tau_max ix optTh
                in pure $ ProfileT taus thetas optTh tau2theta theta2tau
  where
    dflt      = ProfileT (U.fromList [-tau_max, tau_max]) [theta, theta] (theta U.! ix) (const (theta U.! ix)) (const tau_max)
    theta_opt = ctOptimizer et theta
    grader    = snd . ctGradNLL et
    nll_opt   = ctNLL et theta_opt
    optTh     = theta_opt U.! ix
    p         = U.length theta
    p'        = p + 1

    odeFun gamma _ u =
        let grad     = grader u
            w        = ctHessianNLL et u
            m        = [ U.generate p' (\i ->
                            if i < p && j < p then (w !! j) U.! i
                            else if i == ix || j == ix then 1
                            else 0
                          )
                       | j <- [0 .. p'-1] ]
            v        = U.snoc (U.map (*(-gamma)) grad) 1
            dotTheta = unsafePerformIO $ luSolve m v
        in U.init dotTheta

    minRange    = max (abs (upper_ estCI - optTh)) (abs (lower_ estCI - optTh))
    scanRange   = max minRange (tau_max * abs stdErr_i)
    nPts        = max 50 (min 100 (ceiling (scanRange / minRange * 49) + 1))
    tsHi = linSpace nPts (optTh, optTh + scanRange)
    tsLo = linSpace nPts (optTh, optTh - scanRange)
    scanOn sig = foldMap (calcTau sig) . f . scanl (rk (odeFun sig)) (optTh, theta_opt)
                    where f = if sig==1 then id else reverse
    solRight = scanOn 1 tsHi
    solLeft  = scanOn (-1) tsLo
    calcTau s t = let nll_i = ctNLL et (snd t)
                      z     = signum ((snd t U.! ix) - optTh) * sqrt (2 * nll_i - 2 * nll_opt)
                  in if z == 0 || isNaN z then ([], []) else ([z], [snd t])

rk :: (Double -> Target -> Target) -> (Double, Target) -> Double -> (Double, Target)
rk f (t, y) t' = (t', U.zipWith5 (\y0 k1 k2 k3 k4 -> y0 + h/6 * (k1 + 2*k2 + 2*k3 + k4)) y k1 k2 k3 k4)
  where
    h  = t' - t
    k1 = f t y
    k2 = f (t + 0.5*h) (U.zipWith (\y0 k -> y0 + 0.5*h*k) y k1)
    k3 = f (t + 0.5*h) (U.zipWith (\y0 k -> y0 + 0.5*h*k) y k2)
    k4 = f (t + 1.0*h) (U.zipWith (\y0 k -> y0 + 1.0*h*k) y k3)
{-# INLINE rk #-}

-- tau0, tau1 theta0, thetaX = tau1 theta0 / tau0
getStatsFromModel :: Distribution -> Maybe Target -> Columns -> Target -> Fix SRTree -> Target -> BasicStats
getStatsFromModel dist mYerr xss ys tree theta = MkStats cov corr stdErr
  where
    k = U.length theta
    n = U.length ys
    nParams = fromIntegral k
    ident = fromRowMajor k k (U.generate (k * k) (\ix -> let (i, j) = ix `divMod` k in if i == j then 1.0 else 0.0))

    hess = hessianNLL dist mYerr xss ys tree theta

    fexcept :: SomeException -> IO Columns
    fexcept _ = pure ident

    covRaw = unsafePerformIO $ catch (invChol hess) fexcept

    -- For LeastSquares, the Hessian code computes sum(fx*fy - res*fxy) = X^T X,
    -- but the actual Hessian of the Gaussian NLL profile is -1/MSE * X^T X.
    -- So cov_code = inv(X^T X) and cov_correct = MSE * inv(X^T X) = MSE * cov_code.
    sigma2 = case dist of
      LeastSquares -> let mse = compileLoss xss (buildLoss (NLL LeastSquares) (fromIntegral n) tree) ys mYerr theta
                      in  max mse 1e-10  -- avoid division by zero
      _            -> 1.0  -- no scaling needed for NLL-based losses

    scaleFactor = case dist of
      LeastSquares -> sigma2
      _            -> 1.0

    cov = fromRowMajor k k $ U.map (* scaleFactor) (toRowMajor covRaw)

    covMat = toRowMajor cov
    stdErr = U.generate k (\ix -> sqrt $ max 0 (covMat U.! (ix * k + ix)))

    stdErrSq = case outer stdErr stdErr of
      Right v -> v
      Left _ -> []

    stdErrSqMat = toRowMajor stdErrSq
    corr = fromRowMajor k k $ U.generate (k * k) (\ix -> covMat U.! ix / stdErrSqMat U.! ix)

-- Create splines for profile-t
-- We enforce monotonicity of theta w.r.t. tau: if the profile walk produced
-- non-monotonic pairs (theta[i] < theta[i-1] for positive tau direction or vice versa),
-- we keep only the outermost monotonic subsequence to prevent spline extrapolation garbage.
createSplines :: Target -> Columns -> Double -> Double -> Int -> Double -> (Double -> Double, Double -> Double)
createSplines taus thetas se tau_max ix optTh
  | n < 2 = (genSplineFun [(-tau_max, -se), (tau_max, se)], genSplineFun [(-se, 0), (se, 1)])
  | otherwise = (tau2theta, theta2tau)
  where
    n = U.length taus
    cols = getCol ix thetas
    rawPairs = sortOnFirst taus cols
    monoPairs = enforceMonotonicTau rawPairs
    _ = trace ("createSplines: raw=" ++ show (length rawPairs) ++ " mono=" ++ show (length monoPairs) ++ " head=" ++ show (take 3 monoPairs) ++ " last=" ++ show (reverse $ take 3 $ reverse monoPairs)) ()
    tau2theta = genSplineFun monoPairs
    theta2tau = genSplineFun $ enforceMonotonicTheta optTh $ sortOnFirst cols taus

-- | Enforce monotonicity for (tau, theta) pairs sorted by tau.
-- Split at tau=0; both halves keep theta non-decreasing:
--   negative half: as tau increases from -tau_max toward 0, theta increases
--   positive half: as tau increases from 0 toward tau_max, theta increases
enforceMonotonicTau :: [(Double, Double)] -> [(Double, Double)]
enforceMonotonicTau []  = []
enforceMonotonicTau [p] = [p]
enforceMonotonicTau pts = negMono ++ posMono
  where
    (neg, pos) = span (\(t, _) -> t <= 0) pts
    negMono = monotoneInc neg
    posMono = monotoneInc pos

-- | Enforce monotonicity for (theta, tau) pairs sorted by theta.
-- Split at theta=optTh; both halves keep tau non-decreasing:
--   left half: as theta increases toward optTh, tau increases toward 0
--   right half: as theta increases from optTh, tau increases from 0
enforceMonotonicTheta :: Double -> [(Double, Double)] -> [(Double, Double)]
enforceMonotonicTheta _    []  = []
enforceMonotonicTheta _    [p] = [p]
enforceMonotonicTheta optTh pts = negMono ++ posMono
  where
    (neg, pos) = span (\(t, _) -> t <= optTh) pts
    negMono = monotoneInc neg
    posMono = monotoneInc pos

-- | Keep longest prefix of non-decreasing second elements.
monotoneInc :: [(Double, Double)] -> [(Double, Double)]
monotoneInc [] = []
monotoneInc [x] = [x]
monotoneInc ((t0,th0):(t1,th1):rest)
  | th1 >= th0 = (t0,th0) : monotoneInc ((t1,th1):rest)
  | otherwise  = monotoneInc ((t0,th0):rest)

-- | Keep longest prefix of non-increasing second elements.
monotoneDec :: [(Double, Double)] -> [(Double, Double)]
monotoneDec [] = []
monotoneDec [x] = [x]
monotoneDec ((t0,th0):(t1,th1):rest)
  | th1 <= th0 = (t0,th0) : monotoneDec ((t1,th1):rest)
  | otherwise  = monotoneDec ((t0,th0):rest)

getCol :: Int -> Columns -> Target
getCol ix mtx = U.generate (length mtx) (\j -> (mtx !! j) U.! ix)
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
    points = sortOn fst $ points' <> maybe [] (\(x,y) -> [(x + 2*pi, y)]) (listToMaybe points')
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
 
