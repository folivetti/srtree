{-# language BlockArguments #-}
{-# language LambdaCase #-}
module IO where

import System.IO ( hClose, hPutStrLn, openFile, stderr, stdout, IOMode(WriteMode), Handle )
import qualified Data.Massiv.Array as A
import Data.List ( intercalate )
import Control.Monad ( unless, forM_ )
import System.Random ( StdGen )

import Data.SRTree ( SRTree (..), Fix (..), var, floatConstsToParam, relabelVars )
import Algorithm.SRTree.Opt ( estimateSErr )
import Algorithm.SRTree.Likelihoods ( Distribution (..) )
import Algorithm.SRTree.ConfidenceIntervals ( printCI, BasicStats(_stdErr, _corr), CI )
import qualified Data.SRTree.Print as P

import Args ( Args(outfile, alpha,msErr,dist,niter) )
import Report
import Data.SRTree.Recursion ( cata )

import Debug.Trace ( trace, traceShow )

-- Header of CSV file
csvHeader :: String
csvHeader = intercalate "," (basicFields <> optFields <> modelFields)
{-# inline csvHeader #-}

-- Open file if filename is not empty
openWriteWithDefault :: Handle -> String -> IO Handle
openWriteWithDefault dflt ""    = pure dflt
openWriteWithDefault _    fname = openFile fname WriteMode
{-# INLINE openWriteWithDefault #-}

-- procecss a single tree and return all the available stats
processTree :: Args        -- command line arguments
            -> StdGen      -- random number generator
            -> Datasets    -- datasets
            -> Fix SRTree  -- expression in tree format
            -> Int         -- index of the parsed expression 
            -> (BasicInfo, SSE, SSE, Info, (BasicStats, [CI], [CI], [CI], [CI]))
processTree args seed dset t ix = (basic, sseOrig, sseOpt, info, cis)
  where
    (tree, theta0)  = floatConstsToParam t
    mSErr'  = case dist args of
                Gaussian -> estimateSErr Gaussian (msErr args)  (_xTr dset) (_yTr dset) (A.fromList A.Seq theta0) tree (niter args)
                _        -> Nothing
    args'   = args{ msErr = mSErr' }
    basic   = getBasicStats args' seed dset tree theta0 ix
    treeVal = case (_xVal dset, _yVal dset) of
                (Nothing, _) -> _expr basic
                (_, Nothing) -> _expr basic
                (Just xV, Just yV) -> _expr $ getBasicStats args' seed dset{_xTr = xV, _yTr = yV} tree theta0 ix
    sseOrig = getSSE dset tree
    sseOpt  = getSSE dset (_expr basic)
    info    = getInfo args' dset (_expr basic) treeVal
    cis     = getCI args' dset basic (alpha args')

-- print the results to a csv format (except CI)
printResults :: Args -> StdGen -> Datasets -> [String] -> [Either String (Fix SRTree)] -> IO ()
printResults args seed dset varnames exprs  = do
  hStat <- openWriteWithDefault stdout (outfile args)
  hPutStrLn hStat csvHeader 
  forM_ (zip [0..] exprs) 
     \(ix, tree) -> 
         case tree of
           Left  err -> hPutStrLn stderr ("invalid expression: " <> err)
           Right t   -> let treeData = processTree args seed dset t ix
                        in hPutStrLn hStat (toCsv treeData varnames)
  unless (null (outfile args)) (hClose hStat)

-- change the stats into a string
toCsv :: (BasicInfo, SSE, SSE, Info, e) -> [String] -> String
toCsv (basic, sseOrig, sseOpt, info, _) varnames = intercalate "," (sBasic <> sSSEOrig <> sSSEOpt <> sInfo)
  where
    sBasic    = [ show (_index basic), show (_fname basic), P.showExprWithVars varnames (_expr basic)
                , show (_nNodes basic), show (_nParams basic)
                , intercalate ";" (map show (_params basic))
                ]
    sSSEOrig  = map (showF sseOrig) [_sseTr, _sseVal, _sseTe]
    sSSEOpt   = map (showF sseOpt)  [_sseTr, _sseVal, _sseTe]
    sInfo     = map (showF info) [_bic, _bicVal, _aic, _aicVal, _evidence, _evidenceVal, _mdl, _mdlFreq, _mdlLatt, _mdlVal, _mdlFreqVal, _mdlLattVal, _nllTr, _nllVal, _nllTe, _cc, _cp]
              <> [intercalate ";" (map show (_fisher info))]
    showF p f = show (f p)

-- get trees of transformed features
getTransformedFeatures :: Fix SRTree -> (Fix SRTree, [Fix SRTree])
getTransformedFeatures = cata $
  \case
     Var   ix                   -> (Fix $ Var ix, [])
     Param ix                   -> (Fix $ Param ix, [])
     Const  x                   -> (Fix $ Const x, [])
     Uni    f (t, vars)         -> (Fix $ Uni f t, vars)
     Bin   op (l, vs1) (r, vs2) -> case (hasNoParam l, hasNoParam r) of
                                     (False, True)  -> let vs = vs1 <> vs2
                                                       in (Fix $ Bin op l (var $ length vs), vs <> [r])
                                     (True, False)  -> let vs = vs1 <> vs2
                                                       in (Fix $ Bin op (var $ length vs) r, vs <> [l])
                                     (    _,    _)   -> (Fix $ Bin op l r, vs1 <> vs2) -- vs1 == vs2 == []

 where
   hasNoParam = cata $
     \case
        Var ix     -> True
        Param ix   -> False
        Const x    -> if floor x == ceiling x then True else False
        Uni f t    -> t
        Bin op l r -> l && r

allAreVars :: [Fix SRTree] -> Bool
allAreVars = all isOnlyVar
  where
    isOnlyVar (Fix (Var _)) = True
    isOnlyVar _             = False

-- print the information on screen (including CIs)
printResultsScreen :: Args -> StdGen -> Datasets -> [String] -> String -> [Either String (Fix SRTree)] -> IO ()
printResultsScreen args seed dset varnames targt exprs = do
  forM_ (zip [0..] exprs) 
    \(ix, tree) -> 
        case tree of
          Left  err -> do putStrLn ("invalid expression: " <> err)
          Right t   -> let treeData = processTree args seed dset t ix
                        in printToScreen ix treeData
  where
    decim :: Int -> Double -> Double
    decim n x = (fromIntegral . (round :: Double -> Integer)) (x * 10^n) / 10^n
    sdecim n  = show . decim n
    nplaces   = 4


    printToScreen ix (basic, _, sseOpt, info, (sts, cis, pis_tr, pis_val, pis_te)) =
      do let (transformedT, newvars) = getTransformedFeatures (_expr basic)
             varnames' = ['z': show ix | ix <- [0 .. length newvars - 1]]
         putStrLn $ "=================== EXPR " <> show ix <> " =================="
         putStr   $ targt <> " ~ f(" <> intercalate ", " varnames <> ") = "
         putStrLn $ P.showExprWithVars varnames (_expr basic)

         unless (allAreVars newvars) do
          putStrLn "\nExpression and transformed features: "
          putStr   $ targt <> " ~ f(" <> intercalate ", " varnames' <> ") = "
          putStrLn $ P.showExprWithVars varnames' (relabelVars transformedT)
          forM_ (zip varnames' newvars) \(vn, tv) -> do
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
         putStrLn "Correlation of parameters: " 
         putStrLn $ show $ A.map (decim 2) (_corr sts)
         putStrLn $ "Std. Err.: " <> show (A.map (decim nplaces) (_stdErr sts))
         putStrLn "\nConfidence intervals:\n\nlower <= val <= upper"
         mapM_ (printCI nplaces) cis
         putStrLn "\nConfidence intervals (predictions training):\n\nlower <= val <= upper"
         mapM_ (printCI nplaces) pis_tr
         unless (null pis_val) do
           putStrLn "\nConfidence intervals (predictions validation):\n\nlower <= val <= upper"
           mapM_ (printCI nplaces) pis_val
         unless (null pis_te) do
           putStrLn "\nConfidence intervals (predictions test):\n\nlower <= val <= upper"
           mapM_ (printCI nplaces) pis_te
         putStrLn "============================================================="
