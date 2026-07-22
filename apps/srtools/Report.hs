{--
   ____  _____  ____   _        ___   _   _
  / ___||_   _||  _ \ | |      / _ \ | \ | |
  \___ \  | |  | |_) || |     | | | ||  \| |
   ___) | | |  |  __/ | |___  | |_| || |\  |
  |____/  |_|  |_|    |_____|  \___/ |_| \_|

         report generation & statistics
--}
module Report where

import qualified Data.Vector.Unboxed as U
import Data.Maybe (fromMaybe)
import Statistics.Distribution.FDistribution (fDistribution)
import Statistics.Distribution (quantile)
import System.Random (StdGen, split, randomRs)

import Data.SRTree (SRTree(..), Fix(..), floatConstsToParam, paramsToConst, countNodes, var, relabelVars)
import Data.SRTree.Recursion (cata)
import Data.SRTree.Eval
import Data.SRTree.Datasets (loadDataset)
import Data.SRTree.Derivative (deriveByParam)
import Algorithm.SRTree.Compile
import Data.List (intercalate)
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.AD (ADBackEnd(..))
import Algorithm.SRTree.ModelSelection (logFunctional, logFunctionalFreq)
import qualified Algorithm.SRTree.Compile as C
import Algorithm.SRTree.ConfidenceIntervals
import Algorithm.SRTree.NonlinearOpt (minimizeNLL)
import Data.SRTree.Print (showExpr)

import Args

data Datasets = DS { _xTr     :: Columns
                   , _yTr     :: Target
                   , _xVal    :: Maybe Columns
                   , _yVal    :: Maybe Target
                   , _xTe     :: Maybe Columns
                   , _yTe     :: Maybe Target
                   , _yErrTr  :: Maybe Target
                   , _yErrVal :: Maybe Target
                   , _yErrTe  :: Maybe Target
                   }

data Plot = Plot { _contours :: [(Int, Int, [(Double, Double)])]
                 , _thetaTau :: [[(Double, Double)]]
                 , _piplot   :: [(Double, Double, Double, Double)]
                 }

data BasicInfo = Basic { _index   :: Int
                       , _fname   :: String
                       , _expr    :: Fix SRTree
                       , _nNodes  :: Int
                       , _nParams :: Int
                       , _params  :: [Double]
                       , _nEvals  :: Int
                       }

data SSE = SSE { _sseTr  :: Double
               , _sseVal :: Double
               , _sseTe  :: Double
               }

data Info = Info { _bic        :: Double
                 , _bicVal     :: Double
                 , _aic        :: Double
                 , _aicVal     :: Double
                 , _evidence   :: Double
                 , _evidenceVal :: Double
                 , _mdl        :: Double
                 , _mdlFreq    :: Double
                 , _mdlLatt    :: Double
                 , _mdlVal     :: Double
                 , _mdlFreqVal :: Double
                 , _mdlLattVal :: Double
                 , _nllTr      :: Double
                 , _nllVal     :: Double
                 , _nllTe      :: Double
                 , _cc         :: Double
                 , _cp         :: Double
                 , _fisher     :: [Double]
                 }

getDataset :: Args -> IO (Datasets, String, String)
getDataset args = do
  ((xTr, yTr, xVal, yVal), (yErrTr, yErrVal), varnames, tgname) <- loadDataset (dataset args) (hasHeader args)
  let (mXVal, mYVal) = if U.null yVal
                         then (Nothing, Nothing)
                         else (Just xVal, Just yVal)
  (mXTe, mYTe, mYErrTe) <- if null (test args)
                             then pure (Nothing, Nothing, Nothing)
                             else do ((xTe, yTe, _, _), (yErrTe, _), _, _) <- loadDataset (test args) (hasHeader args)
                                     pure (Just xTe, Just yTe, yErrTe)
  pure (DS xTr yTr mXVal mYVal mXTe mYTe yErrTr yErrVal mYErrTe, varnames, tgname)

getBasicStats :: Args -> StdGen -> Datasets -> Fix SRTree -> [Double] -> Int -> BasicInfo
getBasicStats args seed dset tree theta0 ix
  | anyNaN    = getBasicStats args (snd $ split seed) dset tree theta0 ix
  | otherwise = Basic ix (infile args) tOpt nNodes nParams' params nEvs
  where
    nModel = length theta0
    nParams' = case dist args of { Gaussian -> nModel; _ -> nModel }
    thetas = if restart args
                then U.fromList $ take nModel (randomRs (-1.0, 1.0) seed)
                else U.fromList theta0
    (t, _, nEvs) = minimizeNLL MultiThread (NLL (dist args)) (_yErrTr dset) (niter args) (_xTr dset) (_yTr dset) tree thetas
    tOpt = paramsToConst (U.toList t) tree
    nNodes = countNodes tOpt
    params = U.toList t
    anyNaN = any isNaN params

sseSet :: Columns -> Target -> Fix SRTree -> Target -> Double
sseSet xss y tree theta =
  let yhat = compile xss tree theta
      res  = U.zipWith (-) y yhat
  in U.sum (U.map (^2) res)

getSSE :: Datasets -> Fix SRTree -> SSE
getSSE dset tree = SSE trVal valVal teVal
  where
    (t, th) = floatConstsToParam tree
    thVec   = U.fromList th
    trVal   = sseSet (_xTr dset) (_yTr dset) t thVec
    valVal  = case (_xVal dset, _yVal dset) of
                (Just xv, Just yv) -> sseSet xv yv t thVec
                _                  -> 0.0
    teVal   = case (_xTe dset, _yTe dset) of
                (Just xt, Just yt) -> sseSet xt yt t thVec
                _                  -> 0.0

nllSet :: Distribution -> Maybe Target -> Columns -> Target -> Fix SRTree -> Target -> Double
nllSet dist mYerr xss y tree theta =
  let m = U.length y
  in compileLoss xss (buildLoss (NLL dist) (fromIntegral m) tree) y mYerr theta

getInfo :: Args -> Datasets -> Fix SRTree -> Fix SRTree -> Info
getInfo args dset tree treeVal = Info
    { _bic        = bicTr
    , _bicVal     = bicV
    , _aic        = aicTr
    , _aicVal     = aicV
    , _evidence   = evTr
    , _evidenceVal = evV
    , _mdl        = mdlTr
    , _mdlFreq    = mdlFreqTr
    , _mdlLatt    = mdlLattTr
    , _mdlVal     = mdlV
    , _mdlFreqVal = mdlFreqV
    , _mdlLattVal = mdlLattV
    , _nllTr      = nllTr
    , _nllVal     = nllV
    , _nllTe      = nllTe
    , _cc         = logFunctional tOpt
    , _cp         = logParams
    , _fisher     = U.toList $ fisherNLL dist' (_yErrTr dset) (_xTr dset) (_yTr dset) tOpt thetaOpt'
    }
  where
    (xTr, yTr) = (_xTr dset, _yTr dset)
    nTr         = U.length yTr

    (tOpt, thetaOpt_nosig) = floatConstsToParam tree
    thetaOpt    = if dist args == Gaussian
                     then thetaOpt_nosig <> [sigma args]
                     else thetaOpt_nosig
    thetaOpt'   = U.fromList thetaOpt
    nModel      = length thetaOpt_nosig
    nParams'    = length thetaOpt
    dist'       = dist args

    (tOptVal, thetaOptVal_nosig) = floatConstsToParam treeVal
    thetaOptVal = if dist args == Gaussian
                     then thetaOptVal_nosig <> [sigma args]
                     else thetaOptVal_nosig
    thetaOptVal' = U.fromList thetaOptVal

    nllTr    = nllSet dist' (_yErrTr dset) xTr yTr tOpt thetaOpt'
    nllTe    = case (_xTe dset, _yTe dset) of
                 (Just xt, Just yt) -> nllSet dist' (_yErrTe dset) xt yt tOpt thetaOpt'
                 _                  -> 0.0

    (nllV, nVal, tOptVal2, thetaOptVal2) = case (_xVal dset, _yVal dset) of
                                             (Just xv, Just yv) ->
                                               let nv = U.length yv
                                               in (nllSet dist' (_yErrVal dset) xv yv tOptVal thetaOptVal', nv, tOptVal, thetaOptVal')
                                             _ -> (0.0, 0, tOpt, thetaOpt')

    fisher    = fisherNLL dist' (_yErrTr dset) (_xTr dset) (_yTr dset) tOpt thetaOpt'
    logParams = C.logParameters fisher thetaOpt'
    kDbl = fromIntegral nParams'

    bicTr   = kDbl * log (fromIntegral nTr) + 2 * nllTr
    bicV    = if nVal == 0 then 0.0 else kDbl * log (fromIntegral nVal) + 2 * nllV
    aicTr   = 2 * kDbl + 2 * nllTr
    aicV    = if nVal == 0 then 0.0 else 2 * kDbl + 2 * nllV
    evTr    = (1 - bTr) * nllTr - kDbl / 2 * log bTr
      where bTr = 1 / sqrt (fromIntegral nTr)
    evV     = if nVal == 0 then 0.0 else (1 - bV) * nllV - kDbl / 2 * log bV
      where bV = 1 / sqrt (fromIntegral nVal)

    mdlTr     = nllTr + logFunctional tOpt + logParams
    mdlFreqTr = nllTr + logFunctionalFreq tOpt + logParams
    mdlLattTr = nllTr + logFunctional tOpt + logParams
    mdlV      = if nVal == 0 then 0.0 else nllV + logFunctional tOptVal2 + logParams
    mdlFreqV  = if nVal == 0 then 0.0 else nllV + logFunctionalFreq tOptVal2 + logParams
    mdlLattV  = if nVal == 0 then 0.0 else nllV + logFunctional tOptVal2 + logParams

jacobian :: Columns -> Target -> Fix SRTree -> [Target]
jacobian xss theta tree =
  [ compile xss (deriveByParam ix tree) theta
  | ix <- [0 .. U.length theta - 1] ]

getCI :: Args -> Datasets -> BasicInfo -> Double -> (BasicStats, [CI], [CI], [CI], [CI], Plot)
getCI args dset basic alpha' = (stats', cis, pisTr, pisVal, pisTe, Plot contours taus piplots)
  where
    (tree, _)  = floatConstsToParam (_expr basic)
    theta      = U.fromList (_params basic)
    nTr        = U.length (_yTr dset)
    nParams'   = _nParams basic
    tauMaxAl   = sqrt $ quantile (fDistribution (fromIntegral nParams') (fromIntegral (nTr - nParams'))) (1 - alpha')
    tauMax     = sqrt $ quantile (fDistribution (fromIntegral nParams') (fromIntegral (nTr - nParams'))) (1 - 0.01)
    xTr        = _xTr dset
    yTr        = _yTr dset
    dist'      = dist args
    et         = compileTree dist' xTr yTr (_yErrTr dset) tree

    stats'     = getStatsFromModel dist' (_yErrTr dset) xTr yTr tree theta
    laplaceCIs = paramCI (Laplace stats') nTr theta (raAlpha args)
      where raAlpha = alpha -- FIX: alpha from args is the significance level

    profiles   = getAllProfiles (ptype args) et theta (_stdErr stats') (estCIs) alpha'
    estCIs     = paramCI (Laplace stats') nTr theta 0.001

    method     = if useProfile args then Profile stats' profiles else Laplace stats'

    predFun x = compile x tree theta

    jac xss'  = jacobian xss' theta tree

    prof estPi th t =
      let et' = compileTree dist' xTr yTr (_yErrTr dset) t
          (thOpt, _, _) = minimizeNLL MultiThread (NLL dist') (_yErrTr dset) 100 xTr yTr t th
          stdErr = _stdErr stats' U.! 0
          fun = case ptype args of
                  Bates       -> getProfile      et' thOpt stdErr tauMax 0
                  ODE         -> getProfileODE   et' thOpt stdErr estPi tauMax 0
                  Constrained -> getProfileCnstr et' thOpt stdErr tauMaxAl 0
      in case fun of
           Left th' -> prof estPi th' t
           Right p  -> (_tau2theta p, _opt p)

    cis = paramCI method nTr theta alpha'

    predPIs  = predictionCI (Laplace stats') dist' predFun jac prof xTr tree theta alpha' []
    estPIsTr = predictionCI (Laplace stats') dist' predFun jac prof xTr tree theta alpha' []
    estPIsVal = case (_xVal dset, _yVal dset) of
                  (Just xv, _) -> predictionCI (Laplace stats') dist' predFun jac prof xv tree theta alpha' []
                  _            -> []
    estPIsTe = case (_xTe dset, _yTe dset) of
                 (Just xt, _) -> predictionCI (Laplace stats') dist' predFun jac prof xt tree theta alpha' []
                 _            -> []

    pisTr  = predictionCI method dist' predFun jac prof xTr tree theta alpha' predPIs
    pisVal = case (_xVal dset, _yVal dset) of
               (Just xv, _) -> predictionCI method dist' predFun jac prof xv tree theta alpha' estPIsVal
               _            -> []
    pisTe  = case (_xTe dset, _yTe dset) of
               (Just xt, _) -> predictionCI method dist' predFun jac prof xt tree theta alpha' estPIsTe
               _            -> []

    nTrueParams = if dist' == Gaussian then nParams' - 1 else nParams'
    contours    = if contour args
                    then [(ix, iy, approximateContour nTrueParams nTr profiles ix iy alpha')
                         | ix <- [0 .. nTrueParams-2], iy <- [ix+1 .. nTrueParams-1]]
                    else []

    getPts l u ps = [(x, _theta2tau ps x) | x <- [l, l+0.01 .. u]]
    taus = case method of
             Profile _ pfs -> [ getPts (lower_ ci) (upper_ ci) (pfs !! ix)
                              | (ix, ci) <- zip [0..] cis]
             _             -> []
    x0   = if null pisTe
             then U.toList (head xTr)
             else case _xTe dset of
                    Just xt -> U.toList (head xt)
                    Nothing -> U.toList (head xTr)
    piplots = [(xi, lower_ ci, upper_ ci, yi)
              | (xi, CI yi lo hi, ci) <- zip3 x0 (if null pisTe then pisTr else pisTe) (if null pisTe then pisTr else pisTe)]

getTransformedFeatures :: Fix SRTree -> (Fix SRTree, [Fix SRTree])
getTransformedFeatures = cata alg
  where
    alg (Var ix)           = (Fix (Var ix), [])
    alg (Param ix)         = (Fix (Param ix), [])
    alg (Const x)          = (Fix (Const x), [])
    alg (Uni f (t, vars))  = (Fix (Uni f t), vars)
    alg (Bin op (l, vs1) (r, vs2)) =
      case (hasNoParam l, hasNoParam r) of
        (False, True)  -> (Fix (Bin op l (var $ length vs)), vs <> [r])
          where vs = vs1 <> vs2
        (True, False)  -> (Fix (Bin op (var $ length vs) r), vs <> [l])
          where vs = vs1 <> vs2
        (_, _)         -> (Fix (Bin op l r), vs1 <> vs2)

    hasNoParam = cata hasNoParamAlg
    hasNoParamAlg (Var _)     = True
    hasNoParamAlg (Param _)   = False
    hasNoParamAlg (Const x)   = floor x == ceiling x
    hasNoParamAlg (Uni _ t)   = t
    hasNoParamAlg (Bin _ l r) = l && r

allAreVars :: [Fix SRTree] -> Bool
allAreVars = all isOnlyVar
  where
    isOnlyVar (Fix (Var _)) = True
    isOnlyVar _             = False

basicFields :: [String]
basicFields = [ "Index", "Filename", "Expression"
              , "Number_of_nodes", "Number_of_parameters"
              , "Parameters", "Number_of_evaluations" ]

optFields :: [String]
optFields = [ "SSE_train_orig", "SSE_val_orig", "SSE_test_orig"
            , "SSE_train_opt", "SSE_val_opt", "SSE_test_opt" ]

modelFields :: [String]
modelFields = [ "BIC", "BIC_val", "AIC", "AIC_val"
              , "Evidence", "EvidenceVal"
              , "MDL", "MDL_Freq", "MDL_Lattice"
              , "MDL_val", "MDL_Freq_val", "MDL_Lattice_val"
              , "NegLogLikelihood_train", "NegLogLikelihood_val", "NegLogLikelihood_test"
              , "LogFunctional", "LogParameters", "Fisher" ]

csvHeader :: String
csvHeader = intercalate "," (basicFields <> optFields <> modelFields)

csvHeaderSimple :: String
csvHeaderSimple = intercalate "," (basicFields <> optFields)
