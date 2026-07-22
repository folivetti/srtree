{--
   ____  _        _        _____
  |  _ \| |      | |      |_   _|
  | |_) | |      | |        | |
  |  __/| |___   | |___   _| |_
  |_|   |_____|  |_____| |_____|

         terminal & file output
--}
module IO where

import System.IO ( hClose, hPutStrLn, openFile, stderr, stdout, IOMode(WriteMode), Handle )
import Data.List (intercalate)
import Control.Monad (unless, forM_, when)
import System.Random (StdGen)

import Data.SRTree (Fix, SRTree(..), floatConstsToParam, paramsToConst, relabelVars)
import Algorithm.SRTree.Likelihoods (Distribution(..), Loss(..), buildLoss, fisherNLL, hessianNLL)
import Algorithm.SRTree.ConfidenceIntervals (printCI, BasicStats(_stdErr, _corr), CI(..), getCol)
import qualified Data.SRTree.Print as P
import Algorithm.SRTree.Compile (compileTree)
import Data.SRTree.Eval (Target, Columns, compileLoss)
import qualified Data.Vector.Unboxed as U

import Graphics.Gnuplot.Simple
import Graphics.Gnuplot.Terminal.PostScript

import Args (Args(..))
import Report (Datasets(..), Plot(..), BasicInfo(..), SSE(..), Info(..), basicFields, optFields, modelFields, csvHeader, csvHeaderSimple, getDataset, getBasicStats, getSSE, getInfo, getCI, getTransformedFeatures, allAreVars)



fitLine :: [(Double, Double, Double, Double)] -> [(Double, Double)]
fitLine xs = [(x, y) | (x, _, _, y) <- xs]

bandPolygon :: [(Double, Double, Double, Double)] -> [(Double, Double)]
bandPolygon xs =
  upper ++ reverse lower
  where
    upper  = [(x, yu) | (x, _, yu, _) <- xs]
    lower  = [(x, yl) | (x, yl, _, _) <- xs]

openWriteWithDefault :: Handle -> String -> IO Handle
openWriteWithDefault dflt ""    = pure dflt
openWriteWithDefault _    fname = openFile fname WriteMode
{-# INLINE openWriteWithDefault #-}

processTree :: Args -> StdGen -> Datasets -> Fix SRTree -> Int
            -> (BasicInfo, SSE, SSE, Info, (BasicStats, [CI], [CI], [CI], [CI], Plot))
processTree args seed dset t ix = (basic, sseOrig, sseOpt, info, cis)
  where
    (tree, theta0') = floatConstsToParam t
    theta0          = if dist args == Gaussian
                         then theta0' <> [sigma args]
                         else theta0'
    basic   = getBasicStats args seed dset tree theta0 ix
    treeVal = case (_xVal dset, _yVal dset) of
                (Nothing, _) -> _expr basic
                (_, Nothing) -> _expr basic
                (Just xV, Just yV) ->
                  _expr $ getBasicStats args seed dset{_xTr = xV, _yTr = yV} tree theta0 ix
    sseOrig = getSSE dset t
    sseOpt  = getSSE dset (_expr basic)
    info    = getInfo args dset (_expr basic) treeVal
    cis     = getCI args dset basic (alpha args)

processTreeSimple :: Args -> StdGen -> Datasets -> Fix SRTree -> Int
                  -> (BasicInfo, SSE, SSE)
processTreeSimple args seed dset t ix = (basic, sseOrig, sseOpt)
  where
    (tree, theta0') = floatConstsToParam t
    theta0          = if dist args == Gaussian
                         then theta0' <> [sigma args]
                         else theta0'
    basic   = getBasicStats args seed dset tree theta0 ix
    sseOrig = getSSE dset t
    sseOpt  = getSSE dset (_expr basic)

toCsv :: (BasicInfo, SSE, SSE, Info, e) -> [String] -> String
toCsv (basic, sseOrig, sseOpt, info, _) varnames =
  intercalate "," (sBasic <> sSSEOrig <> sSSEOpt <> sInfo)
  where
    sBasic   = [ show (_index basic), show (_fname basic)
               , P.showExprWithVars varnames (_expr basic)
               , show (_nNodes basic), show (_nParams basic)
               , intercalate ";" (map show (_params basic))
               , show (_nEvals basic)
               ]
    sSSEOrig = map (showF sseOrig) [_sseTr, _sseVal, _sseTe]
    sSSEOpt  = map (showF sseOpt)  [_sseTr, _sseVal, _sseTe]
    sInfo    = map (showF info) [_bic, _bicVal, _aic, _aicVal
                               , _evidence, _evidenceVal
                               , _mdl, _mdlFreq, _mdlLatt
                               , _mdlVal, _mdlFreqVal, _mdlLattVal
                               , _nllTr, _nllVal, _nllTe
                               , _cc, _cp
                               ]
            <> [ intercalate ";" (map show (_fisher info)) ]
    showF p f = show (f p)

toCsvSimple :: (BasicInfo, SSE, SSE) -> [String] -> String
toCsvSimple (basic, sseOrig, sseOpt) varnames =
  intercalate "," (sBasic <> sSSEOrig <> sSSEOpt)
  where
    sBasic   = [ show (_index basic), show (_fname basic)
               , P.showExprWithVars varnames (_expr basic)
               , show (_nNodes basic), show (_nParams basic)
               , intercalate ";" (map show (_params basic))
               , show (_nEvals basic)
               ]
    sSSEOrig = map (showF sseOrig) [_sseTr, _sseVal, _sseTe]
    sSSEOpt  = map (showF sseOpt)  [_sseTr, _sseVal, _sseTe]
    showF p f = show (f p)

printResults :: Args -> StdGen -> Datasets -> [String]
             -> [Either String (Fix SRTree)] -> IO ()
printResults args seed dset varnames exprs = do
  hStat <- openWriteWithDefault stdout (outfile args)
  hPutStrLn hStat csvHeader
  forM_ (zip [0..] exprs) $ \(ix, tree) ->
    case tree of
      Left err -> hPutStrLn stderr ("invalid expression: " <> err)
      Right t  -> let treeData = processTree args seed dset t ix
                  in hPutStrLn hStat (toCsv treeData varnames)
  unless (null (outfile args)) (hClose hStat)

printResultsSimple :: Args -> StdGen -> Datasets -> [String]
                   -> [Either String (Fix SRTree)] -> IO ()
printResultsSimple args seed dset varnames exprs = do
  hStat <- openWriteWithDefault stdout (outfile args)
  hPutStrLn hStat csvHeaderSimple
  forM_ (zip [0..] exprs) $ \(ix, tree) ->
    case tree of
      Left err -> hPutStrLn stderr ("invalid expression: " <> err)
      Right t  -> let treeData = processTreeSimple args seed dset t ix
                  in hPutStrLn hStat (toCsvSimple treeData varnames)
  unless (null (outfile args)) (hClose hStat)

printResultsScreen :: Args -> StdGen -> Datasets -> [String] -> String
                   -> [Either String (Fix SRTree)] -> IO ()
printResultsScreen args seed dset varnames targt exprs =
  forM_ (zip [0..] exprs) $ \(ix, tree) ->
    case tree of
      Left err -> putStrLn ("invalid expression: " <> err)
      Right t  -> let treeData = processTree args seed dset t ix
                  in printToScreen ix treeData varnames targt
  where
    decim n x = (fromIntegral (round (x * 10^n :: Double) :: Integer)) / 10^n
    sdecim n = show . decim n
    nplaces  = 4

    printToScreen :: Int -> (BasicInfo, SSE, SSE, Info, (BasicStats, [CI], [CI], [CI], [CI], Plot))
                  -> [String] -> String -> IO ()
    printToScreen ix (basic, _, sseOpt, info, (sts, cis, pisTr, pisVal, pisTe, plot)) _ targt = do
      putStrLn $ "=================== EXPR " <> show ix <> " =================="
      putStr $ targt <> " ~ f(" <> intercalate ", " varnames <> ") = "
      putStrLn $ P.showExprWithVars varnames (_expr basic)

      let (transformedT, newvars) = getTransformedFeatures (_expr basic)
          varnames' = ['z': show i | i <- [0 .. length newvars - 1]]
      unless (allAreVars newvars) $ do
        putStrLn "\nExpression and transformed features: "
        putStr $ targt <> " ~ f(" <> intercalate ", " varnames' <> ") = "
        putStrLn $ P.showExprWithVars varnames' (relabelVars transformedT)
        forM_ (zip varnames' newvars) $ \(vn, tv) ->
          putStrLn $ vn <> " = " <> P.showExprWithVars varnames tv

      putStrLn "\n---------General stats:---------\n"
      putStrLn $ "Number of nodes: " <> show (_nNodes basic)
      putStrLn $ "Number of params: " <> show (_nParams basic)
      putStrLn $ "theta = " <> show (_params basic)

      putStrLn "\n----------Performance:--------\n"
      putStrLn $ "SSE (train.): " <> sdecim nplaces (_sseTr sseOpt)
      putStrLn $ "SSE (val.): " <> sdecim nplaces (_sseVal sseOpt)
      putStrLn $ "SSE (test): " <> sdecim nplaces (_sseTe sseOpt)
      putStrLn $ "NegLogLiklihood (train.): " <> sdecim nplaces (_nllTr info)
      putStrLn $ "NegLogLiklihood (val.): " <> sdecim nplaces (_nllVal info)
      putStrLn $ "NegLogLiklihood (test): " <> sdecim nplaces (_nllTe info)

      putStrLn "\n------Selection criteria:-----\n"
      putStrLn $ "BIC: " <> sdecim nplaces (_bic info)
      putStrLn $ "AIC: " <> sdecim nplaces (_aic info)
      putStrLn $ "MDL: " <> sdecim nplaces (_mdl info)
      putStrLn $ "MDL (freq.): " <> sdecim nplaces (_mdlFreq info)
      putStrLn $ "Functional complexity: " <> sdecim nplaces (_cc info)
      putStrLn $ "Parameter complexity: " <> sdecim nplaces (_cp info)

      putStrLn "\n---------Uncertainties:----------\n"
      putStrLn "Correlation of parameters:"
      let corrRows = _corr sts
      forM_ corrRows $ \row ->
        putStrLn $ "  " ++ show (U.toList row)
      putStrLn $ "Std. Err.: " <> show (map (decim nplaces) (U.toList (_stdErr sts)))
      putStrLn "\nConfidence intervals:\n\nlower <= val <= upper"
      mapM_ (printCI nplaces) cis
      putStrLn "\nConfidence intervals (predictions training):\n\nlower <= val <= upper"
      mapM_ (printCI nplaces) pisTr
      unless (null pisVal) $ do
        putStrLn "\nConfidence intervals (predictions validation):\n\nlower <= val <= upper"
        mapM_ (printCI nplaces) pisVal
      unless (null pisTe) $ do
        putStrLn "\nConfidence intervals (predictions test):\n\nlower <= val <= upper"
        mapM_ (printCI nplaces) pisTe
      when (contour args) $ do
        let taus = _thetaTau plot
        unless (null taus) $ do
          forM_ (zip [0..] taus) $ \(j, pts) -> do
            let fname = "tau_" <> show j <> ".eps"
            plotPath
              [ Custom "terminal" ["postscript font 'Arial,22'"]
              , Title ("theta_" <> show j <> " x tau")
              , XLabel ("theta_" <> show j)
              , YLabel "tau"
              , Key Nothing
              , EPS fname
              ] pts
            putStrLn $ "Plot to " <> fname
            when (debug args) $ do
              putStrLn $ "\nPoints of " <> show j
              forM_ pts $ \(x, y) ->
                putStrLn $ show x <> " " <> show y
        let contours = _contours plot
        unless (null contours) $ do
          forM_ contours $ \(ix1, ix2, pts) -> do
            let fname = "contour_" <> show ix1 <> "_" <> show ix2 <> ".eps"
            plotPath
              [ Custom "terminal" ["postscript font 'Arial,22'"]
              , Title ("Contour of theta_" <> show ix1 <> " and theta_" <> show ix2)
              , XLabel ("theta_" <> show ix1)
              , YLabel ("theta_" <> show ix2)
              , Key Nothing
              , EPS fname
              ] pts
            putStrLn $ "Plot to " <> fname
            when (debug args) $ do
              putStrLn $ "\nPoints of " <> show ix1 <> " " <> show ix2
              forM_ pts $ \(x, y) ->
                putStrLn $ show x <> " " <> show y
        let piplot = _piplot plot
        unless (null piplot) $ do
          let fname = "pis.eps"
          plotPathsStyle
            [ Custom "terminal" ["postscript font 'Arial,22'"]
            , Title "Prediction Intervals"
            , EPS fname
            , XLabel "x"
            , YLabel "y"
            , Key Nothing
            , Custom "style" ["fill transparent solid 0.35 noborder"]
            ]
            [ (defaultStyle, bandPolygon piplot)
            , (defaultStyle{plotType = Lines}, fitLine piplot)
            , (defaultStyle{plotType = Points}, fitLine piplot)
            ]
          putStrLn $ "Plot to " <> fname
      putStrLn "============================================================="
