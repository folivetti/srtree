{-# language ViewPatterns, ScopedTypeVariables, MultiWayIf, FlexibleContexts #-}
module Algorithm.SRTree.ConfidenceIntervals where

import qualified Data.Massiv.Array as A
import Data.Massiv.Array (Ix2(..), (*.), (!+!), (!*!))
import Statistics.Distribution hiding (Distribution)
import Statistics.Distribution.StudentT
import Statistics.Distribution.FDistribution
import Statistics.Distribution.ChiSquared
import qualified Data.Vector.Storable as VS
import qualified Data.Vector as V
import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Print
import Data.SRTree.Recursion ( cata, extract )
import Algorithm.SRTree.AD
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.Opt
import Data.List ( sortOn, nubBy )
import Algorithm.SRTree.NonlinearOpt
import Algorithm.Massiv.Utils
import System.IO.Unsafe ( unsafePerformIO )

import Debug.Trace ( trace, traceShow )

data PType = Bates | ODE | Constrained deriving (Show, Read)

data CIType = Laplace BasicStats | Profile BasicStats [ProfileT]

data BasicStats = MkStats { _cov    :: SRMatrix
                          , _corr   :: SRMatrix
                          , _stdErr :: PVector
                          } deriving (Eq, Show)

data CI = CI { est_   :: Double
             , lower_ :: Double
             , upper_ :: Double
             } deriving (Eq, Show, Read)

data ProfileT = ProfileT { _taus      :: PVector
                         , _thetas    :: SRMatrix
                         , _opt       :: Double
                         , _tau2theta :: Double -> Double
                         , _theta2tau :: Double -> Double
                         } 

showCI :: Int -> CI -> String
showCI n (CI x l h) = show (rnd l) <> " <= " <> show (rnd x) <> " <= " <> show (rnd h)
  where
      rnd = (/10^n) . (fromIntegral . round) . (*10^n)
printCI :: Int -> CI -> IO ()
printCI n = putStrLn . showCI n

paramCI :: CIType -> Int -> PVector -> Double -> [CI]
paramCI (Laplace stats) nSamples theta alpha = zipWith3 CI (A.toList theta) lows highs
  where
    (A.Sz k) = A.size theta
    t      = quantile (studentT . fromIntegral $ nSamples - k) (1 - alpha / 2.0)
    stdErr = _stdErr stats
    lows   = A.toList $ A.zipWith (-) theta $ A.map (*t) stdErr
    highs  = A.toList $ A.zipWith (+) theta $ A.map (*t) stdErr

paramCI (Profile stats profiles) nSamples _ alpha = zipWith3 CI theta lows highs
  where
    k        = length theta
    t        = sqrt $ quantile (fDistribution k (fromIntegral $ nSamples - k)) (1 - alpha)
    stdErr   = _stdErr stats
    lows     = map (\p -> _tau2theta p (-t)) profiles
    highs    = map (\p -> _tau2theta p t) profiles
    theta    = map _opt profiles

predictionCI :: CIType -> Distribution -> (SRMatrix -> PVector) -> (SRMatrix -> [PVector]) -> (CI -> PVector -> Fix SRTree -> (Double -> Double, Double)) -> SRMatrix -> Fix SRTree -> PVector -> Double -> [CI] -> [CI]
predictionCI (Laplace stats) _ predFun jacFun _ xss tree theta alpha _ = zipWith3 CI yhat lows highs
  where
    yhat     = A.toList $ predFun xss
    jac' :: A.Matrix A.S Double
    jac'     = A.fromLists' A.Seq $ map A.toList $ jacFun xss
    jac :: [PVector]
    jac      = A.toList $ A.outerSlices $ A.computeAs A.S $ A.transpose $ jac'
    n        = length yhat
    (A.Sz k) = A.size theta
    t        = quantile (studentT . fromIntegral $ n - k) (1 - alpha / 2.0)
    covs     = A.toList $ A.outerSlices $ _cov stats
    lows     = zipWith (-) yhat $ map (*t) resStdErr
    highs    = zipWith (+) yhat $ map (*t) resStdErr

    getResStdError row = sqrt $ (A.!.!) row $ A.fromList A.Seq $ map ((A.!.!) row) covs
    resStdErr          = map getResStdError jac

predictionCI (Profile _ _) dist predFun _ profFun xss tree theta alpha estPIs = zipWith3 f estPIs yhat $ take 10 xss'
  where
    yhat     = A.toList $ predFun xss
    theta'   = A.toStorableVector theta

    t        = sqrt $ quantile (fDistribution k (fromIntegral $ n - k)) (1 - alpha)
    (A.Sz k) = A.size theta
    n        = length yhat

    theta0  = calcTheta0 dist tree
    xss'    = A.toList $ A.outerSlices xss
    
    f estPI yh xs =
              let t'            = replaceParam0 tree $ evalVar xs theta0
                  (spline, yh') = profFun estPI (A.fromStorableVector A.Seq (theta' VS.// [(0, yh)])) t'
              in CI yh' (spline (-t)) (spline t)

inverseDist :: Floating p => Distribution -> p -> p
inverseDist Gaussian y  = y
inverseDist Bernoulli y = log(y/(1-y))
inverseDist Poisson y   = log y

replaceParam0 :: Fix SRTree -> Fix SRTree -> Fix SRTree
replaceParam0 tree t0 = cata alg tree
  where
    alg (Var ix)     = Fix $ Var ix
    alg (Param 0)    = t0
    alg (Param ix)   = Fix $ Param ix
    alg (Const c)    = Fix $ Const c
    alg (Uni g t)    = Fix $ Uni g t
    alg (Bin op l r) = Fix $ Bin op l r

evalVar :: PVector -> Fix SRTree -> Fix SRTree
evalVar xs = cata alg 
  where
    alg (Var ix)     = Fix $ Const (xs A.! ix)
    alg (Param ix)   = Fix $ Param ix
    alg (Const c)    = Fix $ Const c
    alg (Uni g t)    = Fix $ Uni g t
    alg (Bin op l r) = Fix $ Bin op l r

calcTheta0 :: Distribution -> Fix SRTree -> Fix SRTree
calcTheta0 dist tree = case cata alg tree of
                         Left g -> g $ inverseDist dist (Fix $ Param 0)
                         Right _ -> error "No theta0?"
  where
    alg (Var ix)     = Right $ Fix $ Var ix
    alg (Param 0)    = Left id
    alg (Param ix)   = Right $ Fix $ Param ix
    alg (Const c)    = Right $ Fix $ Const c
    alg (Uni g t)    = case t of
                         Left f  -> Left $ f . evalInverse g
                         Right v -> Right $ evalFun g v
    alg (Bin op l r) = case l of
                         Left f   -> case r of
                                       Left  _ -> error "This shouldn't happen!"
                                       Right v -> Left $ f . invright op v
                         Right vl -> case r of
                                       Left  g -> Left $ g . invleft op vl
                                       Right vr -> Right $ evalOp op vl vr
-- here
getAllProfiles :: PType -> Distribution -> Maybe Double -> SRMatrix -> PVector -> Fix SRTree -> PVector -> PVector -> [CI] -> Double -> [ProfileT]
getAllProfiles ptype dist mSErr xss ys tree theta stdErr estCIs alpha = reverse (getAll 0 [])
  where 
    (A.Sz k)   = A.size theta
    (A.Sz n)   = A.size ys
    tau_max    = sqrt $ quantile (fDistribution k (n - k)) (1 - 0.01)
    tau_max'   = sqrt $ quantile (fDistribution k (n - k)) (1 - alpha)

    profFun ix = case ptype of
                    Bates       -> getProfile      dist mSErr xss ys tree theta (stdErr A.! ix) tau_max ix
                    ODE         -> getProfileODE   dist mSErr xss ys tree theta (stdErr A.! ix) (estCIs !! ix) tau_max ix
                    Constrained -> getProfileCnstr dist mSErr xss ys tree theta (stdErr A.! ix) tau_max' ix

    getAll ix acc | ix == k   = acc
                  | otherwise = case profFun ix of
                                  Left t  -> getAllProfiles ptype dist mSErr xss ys tree t stdErr estCIs alpha
                                  Right p -> getAll (ix + 1) (p : acc)

getProfile :: Distribution 
           -> Maybe Double 
           -> SRMatrix
           -> PVector
           -> Fix SRTree 
           -> PVector
           -> Double
           -> Double
           -> Int 
           -> Either PVector ProfileT
getProfile dist mSErr xss ys tree theta stdErr_i tau_max ix
  | stdErr_i == 0.0 = pure $ ProfileT (A.fromList A.Seq [-tau_max, tau_max]) (A.fromLists' A.Seq [theta', theta']) (theta A.! ix) (const (theta A.! ix)) (const tau_max)
  | otherwise =
  do negDelta <- go kmax (-stdErr_i / 8) 0 1 mempty
     posDelta <- go kmax  (stdErr_i / 8) 0 1 p0
     let (A.fromList A.Seq -> taus, A.fromLists' A.Seq . map A.toList -> thetas) = negDelta <> posDelta
         (tau2theta, theta2tau)                       = createSplines taus thetas stdErr_i tau_max ix
     pure $ ProfileT taus thetas optTh tau2theta theta2tau
  where
    theta'    = A.toList theta
    p0        = ([0], [theta_opt])
    kmax      = 300
    nll_opt   = nll dist mSErr xss ys tree theta_opt
    theta_opt = fst $ minimizeNLLNonUnique dist mSErr 100 xss ys tree theta
    optTh     = theta_opt A.! ix
    minimizer = minimizeNLLWithFixedParam dist mSErr 100 xss ys tree ix

    -- after k iterations, interpolates to the endpoint
    go 0 delta _ _         acc = Right acc
    go k delta t inv_slope acc@(taus, thetas)
      | isNaN inv_slope     = Right acc    -- stop since we cannot move forward on discontinuity
      | nll_cond < nll_opt  = Left theta_t -- found a better optima
      | abs tau > tau_max   = Right acc'   -- we reached the endpoint
      | otherwise           = go (k-1) delta (t + inv_slope) inv_slope' acc'
      where
        t_delta     = (theta_opt A.! ix) + delta * (t + inv_slope)
        theta_delta = updateS theta_opt [(ix, t_delta)]
        theta_t     = minimizer theta_delta
        zv          = (A.computeAs A.S $ snd $ gradNLL dist mSErr xss ys tree theta_t) A.! ix
        zvs         = snd $ gradNLL dist mSErr xss ys tree theta_t
        inv_slope'  = min 4.0 . max 0.0625 . abs $ (tau / (stdErr_i * zv))
        nll_cond    = nll dist mSErr xss ys tree theta_t
        acc'        = if nll_cond == nll_opt || ( (not.null) taus && tau == head taus ) || isNaN tau
                         then acc
                         else (tau:taus, theta_t:thetas)
        tau         = signum delta * sqrt (2*nll_cond - 2*nll_opt)

-- Based on https://insysbio.github.io/LikelihoodProfiler.jl/latest/
-- Borisov, Ivan, and Evgeny Metelkin. "Confidence intervals by constrained optimization—An algorithm and software package for practical identifiability analysis in systems biology." PLOS Computational Biology 16.12 (2020): e1008495.
getProfileCnstr :: Distribution
                -> Maybe Double
                -> SRMatrix
                -> PVector
                -> Fix SRTree
                -> PVector
                -> Double -> Double
                -> Int
                -> Either PVector ProfileT
getProfileCnstr dist mSErr xss ys tree theta stdErr_i tau_max ix
  | stdErr_i == 0.0 = pure $ ProfileT taus thetas theta_i (const theta_i) (const tau_max)
  | otherwise       = pure $ ProfileT taus thetas theta_i tau2theta (const tau_max)
  where
    taus     = A.fromList A.Seq [-tau_max, tau_max]
    theta'   = A.toList theta
    thetas   = A.fromLists' A.Seq [theta', theta']
    theta_i  = theta A.! ix
    getPoint = getEndPoint dist mSErr xss ys tree theta tau_max ix
    leftPt   = getPoint True
    rightPt  = getPoint False
    tau2theta tau = if tau < 0 then leftPt else rightPt

getEndPoint dist mSErr xss ys tree theta tau_max ix isLeft =
  case minimizeAugLag problem (A.toStorableVector theta_opt) of
            Right sol -> solutionParams sol VS.! ix
            Left e    -> traceShow e $ theta_opt A.! ix
  where
    (A.Sz1 n) = A.size theta

    theta_opt = fst $ minimizeNLLNonUnique dist mSErr 100 xss ys tree theta
    nll_opt   = nll dist mSErr xss ys tree theta_opt
    loss_crit = nll_opt + tau_max

    loss      = (subtract loss_crit) . nll dist mSErr xss ys tree . A.fromStorableVector A.Seq
    obj       = (if isLeft then id else negate) . (VS.! ix)

    stop       = ObjectiveRelativeTolerance 1e-4 :| []
    localAlg   = NELDERMEAD obj [] Nothing
    local      = LocalProblem (fromIntegral n) stop localAlg
    constraint = InequalityConstraint (Scalar loss) 1e-6

    problem = AugLagProblem [] [] (AUGLAG_LOCAL local [constraint] [])
{-# INLINE getEndPoint #-}

-- Based on
-- Jian-Shen Chen & Robert I Jennrich (2002) Simple Accurate Approximation of Likelihood Profiles,
-- Journal of Computational and Graphical Statistics, 11:3, 714-732, DOI: 10.1198/106186002493
getProfileODE :: Distribution 
           -> Maybe Double 
           -> SRMatrix
           -> PVector
           -> Fix SRTree 
           -> PVector
           -> Double 
           -> CI
           -> Double 
           -> Int 
           -> Either PVector ProfileT
getProfileODE dist mSErr xss ys tree theta stdErr_i estCI tau_max ix
  | stdErr_i == 0.0 = pure dflt
  | otherwise = let (A.fromList A.Seq -> taus, A.fromLists' A.Seq . map (A.toList) -> thetas) = solLeft <> ([0], [theta_opt]) <> solRight
                    (tau2theta, theta2tau) = createSplines taus thetas stdErr_i tau_max ix
                in pure $ ProfileT taus thetas optTh tau2theta theta2tau
  where
    dflt      = ProfileT (A.fromList A.Seq [-tau_max, tau_max]) (A.fromLists' A.Seq [theta', theta']) (theta A.! ix) (const (theta A.! ix)) (const tau_max)
    minimizer = fst . minimizeNLLNonUnique dist mSErr 100 xss ys tree
    grader    = snd . gradNLLNonUnique dist mSErr xss ys tree
    theta_opt = minimizer theta
    theta'    = A.toList theta
    nll_opt   = nll dist mSErr xss ys tree theta_opt
    optTh     = theta_opt A.! ix
    p'        = p+1
    (A.Sz1 p) = A.size theta
    sErr = case mSErr of
                Nothing -> 1
                Just z  -> z
    getHess t = hessianNLL dist mSErr xss ys tree t

    odeFun gamma _ u = 
        let grad     = grader u
            w        = hessianNLL dist mSErr xss ys tree u
            m        = A.makeArray A.Seq (A.Sz (p' :. p'))
                         (\ (i :. j) -> if | i<p && j<p -> w A.! (i :. j)
                                           | i==ix      -> 1
                                           | j==ix      -> 1
                                           | otherwise  -> 0
                         )

            v        = A.computeAs A.S $ A.snoc (A.map (*(-gamma)) grad) 1
            dotTheta = unsafePerformIO $ luSolve m v
        in A.fromStorableVector A.Seq $ VS.init $ A.toStorableVector dotTheta
    tsHi = linSpace 50 (optTh, upper_ estCI)
    tsLo = linSpace 50 (optTh, lower_ estCI)
    scanOn sig = foldMap (calcTau sig) . f . scanl (rk (odeFun sig)) (optTh, theta_opt)
                    where f = if sig==1 then id else reverse
    solRight = scanOn 1 tsHi
    solLeft  = scanOn (-1) tsLo
    calcTau s t = let nll_i = nll dist mSErr xss ys tree $ snd t
                      z     = signum (((snd t) A.! ix) - optTh) * sqrt (2 * nll_i - 2 * nll_opt)
                   in if z == 0 || isNaN z then ([], []) else ([z], [snd t])

rk :: (Double -> PVector -> PVector) -> (Double, PVector) -> Double -> (Double, PVector)
rk f (t, y) t' = (t', y !+! ((1.0/6.0) *. h' !*! (k1 !+! (2.0 *. k2) !+! (2.0 *. k3) !+! k4)))
  where
    h  = t' - t
    h', k1, k2, k3, k4 :: PVector
    h' = A.replicate A.Seq (A.size y) h
    k1 = f t y
    k2 = f (t + 0.5*h) (A.computeAs A.S $ A.zipWith3 (g 0.5) y h' k1) -- (y !+! 0.5*.h' A.!*! k1)
    k3 = f (t + 0.5*h) (A.computeAs A.S $ A.zipWith3 (g 0.5) y h' k2) -- (y !+! 0.5*.h' A.!*! k2)
    k4 = f (t + 1.0*h) (A.computeAs A.S $ A.zipWith3 (g 1.0) y h' k3) -- (y !+! 1.0*.h'!*!k3)
    g a yi hi ki = yi + a * hi * ki
{-# INLINE rk #-}

-- tau0, tau1  theta0, thetaX = tau1 theta0 / tau0
getStatsFromModel :: Distribution -> Maybe Double -> SRMatrix -> PVector -> Fix SRTree -> PVector -> BasicStats
getStatsFromModel dist mSErr xss ys tree theta = MkStats cov corr stdErr
  where
    (A.Sz1 k) = A.size theta
    (A.Sz1 n) = A.size ys
    nParams = fromIntegral k
    ssr  = sse xss ys tree theta

    -- only for gaussian
    sErr  = sqrt $ ssr / fromIntegral (n - k)

    hess    = hessianNLL dist mSErr xss ys tree theta
    cov     = unsafePerformIO (invChol hess)
    
    stdErr   = A.makeArray A.Seq (A.Sz1 k) (\ix -> sqrt $ cov A.! (ix :. ix))
    stdErrSq = case outer stdErr stdErr of
                 Left _  -> error "stdErr size mismatch?"
                 Right v -> v

    corr     = A.computeAs A.S $ A.zipWith (/) cov stdErrSq

-- Create splines for profile-t
createSplines :: PVector -> SRMatrix -> Double -> Double -> Int -> (Double -> Double, Double -> Double)
createSplines taus thetas se tau_max ix
  | n < 2     = (genSplineFun [(-tau_max, -se), (tau_max, se)], genSplineFun [(-se, 0), (se, 1)])
  | otherwise = (tau2theta, theta2tau)
  where
    (A.Sz n)   = A.size taus
    cols       = getCol ix thetas
    nubOnFirst = nubBy (\x y -> fst x == fst y)
    tau2theta  = genSplineFun $ nubOnFirst $ sortOnFirst taus cols
    theta2tau  = genSplineFun $ nubOnFirst $ sortOnFirst cols taus

getCol :: Int -> SRMatrix -> PVector
getCol ix mtx = getCols mtx A.! ix
{-# inline getCol #-}

sortOnFirst :: PVector -> PVector -> [(Double, Double)]
sortOnFirst xs ys = sortOn fst $ zip (A.toList xs) (A.toList ys)
{-# inline sortOnFirst #-}

splinesSketches :: Double -> PVector -> PVector -> (Double -> Double) -> (Double -> Double)
splinesSketches tauScale (A.toList -> tau) (A.toList -> theta) theta2tau
  | length tau < 2 = id
  | otherwise      = genSplineFun gpq
  where
    gpq = sortOn fst [(x, acos y') | (x, y) <- zip tau theta
                                   , let y' = theta2tau y / tauScale
                                   , abs y' < 1 ]

approximateContour :: Int -> Int -> [ProfileT] -> Int -> Int -> Double -> [(Double, Double)]
approximateContour nParams nPoints profs ix1 ix2 alpha = go 0
  where
    -- get the info for ix1 and ix2
    (prof1, prof2)           = (profs !! ix1, profs !! ix2)
    (tau2theta1, theta2tau1) = (_tau2theta prof1, _theta2tau prof1)
    (tau2theta2, theta2tau2) = (_tau2theta prof2, _theta2tau prof2)

    -- calculate the spline for A-D
    tauScale = sqrt (fromIntegral nParams * quantile (fDistribution nParams (nPoints - nParams)) (1 - alpha))
    splineG1 = splinesSketches tauScale (_taus prof1) (getCol ix2 (_thetas prof1)) theta2tau2
    splineG2 = splinesSketches tauScale (_taus prof2) (getCol ix1 (_thetas prof2)) theta2tau1
    angles   = [ (0, splineG1 1), (splineG2 1, 0), (pi, splineG1 (-1)), (splineG2 (-1), pi) ]
    splineAD = genSplineFun points

    applyIfNeg (x, y) = if y < 0 then (-x, -y) else (x ,y)
    points   = sortOn fst
             $ [applyIfNeg ((x+y)/2, x - y) | (x, y) <- angles] 
            <> (\(x,y) -> [(x + 2*pi, y)]) (head points)

    -- generate the points of the curve
    go 100 = []
    go ix  = (p, q) : go (ix+1)
      where
        ai = ix * 2 * pi / 99 - pi
        di = splineAD ai
        taup = cos (ai + di / 2) * tauScale
        tauq = cos (ai - di / 2) * tauScale
        p = tau2theta1 taup
        q = tau2theta2 tauq
