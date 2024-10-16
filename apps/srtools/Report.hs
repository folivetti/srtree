module Report where

import qualified Data.Vector.Storable as VS
import qualified Data.Massiv.Array as A
import Data.Massiv.Array ( Sz(..) )
import Data.Maybe ( fromMaybe )
import Statistics.Distribution.FDistribution ( fDistribution )
import Statistics.Distribution.ChiSquared ( chiSquared )
import Statistics.Distribution ( quantile )
import System.Random ( StdGen, split )
import Data.Random.Normal ( normals )

import Data.SRTree ( SRTree, Fix (..), floatConstsToParam, paramsToConst, countNodes )
import Data.SRTree.Eval
import Algorithm.SRTree.AD ( reverseModeUnique, forwardModeUniqueJac )
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.ModelSelection ( aic, bic, evidence, logFunctional, logParameters, mdl, mdlFreq, mdlLatt )
import Algorithm.SRTree.ConfidenceIntervals
import Algorithm.SRTree.Opt (minimizeNLLWithFixedParam, minimizeNLL, minimizeNLLNonUnique)
import Data.SRTree.Datasets ( loadDataset )
import Data.SRTree.Print ( showExpr )
import Debug.Trace ( trace, traceShow )

import Args

-- store the datasets split into training, validation and test
data Datasets = DS { _xTr  :: SRMatrix
                   , _yTr  :: PVector
                   , _xVal :: Maybe SRMatrix
                   , _yVal :: Maybe PVector
                   , _xTe  :: Maybe SRMatrix
                   , _yTe  :: Maybe PVector
                   }

-- basic fields name
basicFields :: [String]
basicFields = [ "Index"
              , "Filename"
              , "Expression"
              , "Number_of_nodes"
              , "Number_of_parameters"
              , "Parameters"
              ]

-- basic information about the tree
data BasicInfo = Basic { _index   :: Int
                       , _fname   :: String
                       , _expr    :: Fix SRTree
                       , _nNodes  :: Int
                       , _nParams :: Int
                       , _params  :: [Double]
                       }

-- optimization fields
optFields :: [String]
optFields = [ "SSE_train_orig"
            , "SSE_val_orig"
            , "SSE_test_orig"
            , "SSE_train_opt"
            , "SSE_val_opt"
            , "SSE_test_opt"
            ]

-- optimization information
data SSE = SSE { _sseTr  :: Double
               , _sseVal :: Double
               , _sseTe  :: Double
               }

-- model selection fields
modelFields :: [String]
modelFields = [ "BIC"
              , "BIC_val"
              , "AIC"
              , "AIC_val"
              , "Evidence"
              , "EvidenceVal"
              , "MDL"
              , "MDL_Freq"
              , "MDL_Lattice"
              , "MDL_val"
              , "MDL_Freq_val"
              , "MDL_Lattice_val"
              , "NegLogLikelihood_train"
              , "NegLogLikelihood_val"
              , "NegLogLikelihood_test"
              , "LogFunctional"
              , "LogParameters"
              , "Fisher"
              ]

-- model selection information
data Info = Info { _bic     :: Double
                 , _bicVal  :: Double
                 , _aic     :: Double
                 , _aicVal  :: Double
                 , _evidence :: Double
                 , _evidenceVal :: Double
                 , _mdl     :: Double
                 , _mdlFreq :: Double
                 , _mdlLatt :: Double
                 , _mdlVal  :: Double
                 , _mdlFreqVal :: Double
                 , _mdlLattVal :: Double
                 , _nllTr   :: Double
                 , _nllVal  :: Double
                 , _nllTe   :: Double
                 , _cc      :: Double
                 , _cp      :: Double
                 , _fisher  :: [Double]
                 }

-- load the datasets
getDataset :: Args -> IO (Datasets, String, String)
getDataset args = do
  ((xTr, yTr, xVal, yVal), varnames, tgname) <- loadDataset (dataset args) (hasHeader args)
  let (A.Sz m) = A.size yVal
  let (mXVal, mYVal) = if m == 0
                         then (Nothing, Nothing)
                         else (Just xVal, Just yVal)
  (mXTe, mYTe) <- if null (test args)
                    then pure (Nothing, Nothing)
                    else do ((xTe, yTe, _, _), _, _) <- loadDataset (test args) (hasHeader args)
                            pure (Just xTe, Just yTe)
  pure (DS xTr yTr mXVal mYVal mXTe mYTe, varnames, tgname)

getBasicStats :: Args -> StdGen -> Datasets -> Fix SRTree -> [Double] -> Int -> BasicInfo
getBasicStats args seed dset tree theta0 ix
  | anyNaN    = getBasicStats args (snd $ split seed) dset tree theta0 ix
  | otherwise = Basic ix (infile args) tOpt nNodes nParams params
  where
    -- (tree', theta0) = floatConstsToParam tree
    thetas          = if restart args
                        then A.fromList A.Seq $ take nParams (normals seed)
                        else A.fromList A.Seq theta0
    t               = fst $ minimizeNLL (dist args) (msErr args) (niter args) (_xTr dset) (_yTr dset) tree thetas
    tOpt            = paramsToConst (A.toList t) tree
    nNodes          = countNodes tOpt :: Int
    nParams         = length theta0
    params          = A.toList t
    anyNaN          = A.any isNaN t

getSSE :: Datasets -> Fix SRTree -> SSE
getSSE dset tree = SSE tr val te
  where
    (t, th) = floatConstsToParam tree
    tr  = sse (_xTr dset) (_yTr dset) t (A.fromList A.Seq th)
    val = case (_xVal dset, _yVal dset) of
            (Nothing, _)           -> 0.0
            (_, Nothing)           -> 0.0
            (Just xVal, Just yVal) -> sse xVal yVal t (A.fromList A.Seq th)
    te  = case (_xTe dset, _yTe dset) of
            (Nothing, _)           -> 0.0
            (_, Nothing)           -> 0.0
            (Just xTe, Just yTe)   -> sse xTe yTe t (A.fromList A.Seq th)

getInfo :: Args -> Datasets -> Fix SRTree -> Fix SRTree -> Info
getInfo args dset tree treeVal =
  Info { _bic     = bic dist' msErr' xTr yTr thetaOpt' tOpt
       , _bicVal  = bicVal
       , _aic     = aic dist' msErr' xTr yTr thetaOpt' tOpt
       , _aicVal  = aicVal
       , _evidence = evidence dist' msErr' xTr yTr thetaOpt' tOpt
       , _evidenceVal = evidenceVal
       , _mdl     = mdl dist' msErr' xTr yTr thetaOpt' tOpt
       , _mdlFreq = mdlFreq dist' msErr' xTr yTr thetaOpt' tOpt
       , _mdlLatt = mdlLatt dist' msErr' xTr yTr thetaOpt' tOpt
       , _mdlVal  = mdlVal
       , _mdlFreqVal = mdlFreqVal
       , _mdlLattVal = mdlLattVal
       , _nllTr   = nllTr
       , _nllVal  = nllVal
       , _nllTe   = nllTe
       , _cc      = logFunctional tOpt
       , _cp      = logParameters dist' msErr' xTr yTr thetaOpt' tOpt
       , _fisher  = A.toList $ fisherNLL dist' (msErr args) xTr yTr tOpt thetaOpt'
       }
  where
    (xTr, yTr)       = (_xTr dset, _yTr dset)
    (xVal, yVal)     = case (_xVal dset, _yVal dset) of
                         (Nothing, _)     -> (xTr, yTr)
                         (_, Nothing)     -> (xTr, yTr)
                         (Just a, Just b) -> (a, b)
    (tOpt, thetaOpt) = floatConstsToParam tree
    thetaOpt'        = A.fromList A.Seq thetaOpt

    (tOptVal, thetaOptVal) = floatConstsToParam treeVal
    thetaOptVal'           = A.fromList A.Seq thetaOptVal

    dist'            = dist args
    msErr'           = msErr args
    nllTr            = nll dist' msErr' (_xTr dset) (_yTr dset) tOpt (A.fromList A.Seq thetaOpt)
    bicVal           = case (_xVal dset, _yVal dset) of
                         (Nothing, _) -> 0.0
                         (_, Nothing) -> 0.0
                         _            -> bic dist' msErr' xVal yVal thetaOptVal' tOptVal
    aicVal           = case (_xVal dset, _yVal dset) of
                         (Nothing, _) -> 0.0
                         (_, Nothing) -> 0.0
                         _            -> aic dist' msErr' xVal yVal thetaOptVal' tOptVal
    evidenceVal      = case (_xVal dset, _yVal dset) of
                         (Nothing, _) -> 0.0
                         (_, Nothing) -> 0.0
                         _            -> evidence dist' msErr' xVal yVal thetaOptVal' tOptVal
    nllVal           = case (_xVal dset, _yVal dset) of
                         (Nothing, _) -> 0.0
                         (_, Nothing) -> 0.0
                         _            -> nll dist' msErr' xVal yVal tOptVal (A.fromList A.Seq thetaOptVal)
    mdlVal           = case (_xVal dset, _yVal dset) of
                         (Nothing, _) -> 0.0
                         (_, Nothing) -> 0.0
                         _            -> mdl dist' msErr' xVal yVal thetaOptVal' tOptVal
    mdlFreqVal       = case (_xVal dset, _yVal dset) of
                         (Nothing, _) -> 0.0
                         (_, Nothing) -> 0.0
                         _            -> mdlFreq dist' msErr' xVal yVal thetaOptVal' tOptVal
    mdlLattVal       = case (_xVal dset, _yVal dset) of
                         (Nothing, _) -> 0.0
                         (_, Nothing) -> 0.0
                         _            -> mdlLatt dist' msErr' xVal yVal thetaOptVal' tOptVal
    nllTe            = case (_xTe dset, _yTe dset) of
                         (Nothing, _)           -> 0.0
                         (_, Nothing)           -> 0.0
                         (Just xTe, Just yTe) -> nll dist' msErr' xTe yTe tOpt (A.fromList A.Seq thetaOpt)

getCI :: Args -> Datasets -> BasicInfo -> Double -> (BasicStats, [CI], [CI], [CI], [CI])
getCI args dset basic alpha' = (stats', cis, pis_tr, pis_val, pis_te)
  where
    (Sz n)     = A.size yTr
    (tree, _)  = floatConstsToParam (_expr basic)
    theta      = _params basic
    tau_max    = (quantile (fDistribution (_nParams basic) (n - _nParams basic)) (1 - 0.01))
    tau_max'   = sqrt $ quantile (fDistribution (_nParams basic) (n - _nParams basic)) (1 - alpha')
    (xTr, yTr) = (_xTr dset, _yTr dset)
    dist'      = dist args
    msErr'     = msErr args
    stats'     = getStatsFromModel dist' msErr' xTr yTr tree (A.fromList A.Seq theta)
    profiles   = getAllProfiles (ptype args) dist' msErr' xTr yTr tree (A.fromList A.Seq theta) (_stdErr stats') estCIs alpha'
    method     = if useProfile args
                   then Profile stats' profiles
                   else Laplace stats'
    predFun   = A.computeAs A.S . predict dist' tree (A.fromList A.Seq theta)

    prof estPi th t =
                let (thOpt, _) = minimizeNLLNonUnique dist' (Just 1) 100 xTr yTr t th
                    ssr        = sse xTr yTr t thOpt
                    est        = sqrt $ ssr / fromIntegral (n - _nParams basic)
                    stdErr     = _stdErr stats' A.! 0
                    fun        = case ptype args of
                                   Bates       -> getProfile      dist' (Just est) xTr yTr t thOpt stdErr tau_max 0
                                   ODE         -> getProfileODE   dist' (Just est) xTr yTr t thOpt stdErr estPi tau_max 0
                                   Constrained -> getProfileCnstr dist' (Just est) xTr yTr t thOpt stdErr tau_max' 0
                in case fun of
                      Left th' -> trace "found better optima" $ prof estPi th' t
                      Right p  -> (_tau2theta p, _opt p)
    jac xss   = forwardModeUniqueJac xss (A.fromList A.Seq theta) tree -- FIX

    estCIs    = paramCI (Laplace stats') n (A.fromList A.Seq theta) 0.001
    cis       = paramCI method n (A.fromList A.Seq theta) alpha'

    estPIS_tr  = predictionCI (Laplace stats') dist' predFun jac prof xTr tree (A.fromList A.Seq theta) alpha' []
    estPIS_val = predictionCI (Laplace stats') dist' predFun jac prof xTr tree (A.fromList A.Seq theta) alpha' []
    estPIS_te  = predictionCI (Laplace stats') dist' predFun jac prof xTr tree (A.fromList A.Seq theta) alpha' []

    pis_tr    = predictionCI method dist' predFun jac prof xTr tree (A.fromList A.Seq theta) alpha' estPIS_tr
    pis_val   = case (_xVal dset, _yVal dset) of
                  (Nothing, _)   -> []
                  (Just xVal, _) -> predictionCI method dist' predFun jac prof xVal tree (A.fromList A.Seq theta) alpha' estPIS_val
    pis_te    = case (_xTe dset, _yTe dset) of
                  (Nothing, _)  -> []
                  (Just xTe, _) -> predictionCI method dist' predFun jac prof xTe tree (A.fromList A.Seq theta) alpha' estPIS_te
