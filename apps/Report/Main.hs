module Main (main) where

import Options.Applicative
import qualified Data.ByteString.Char8 as B
import qualified Data.Vector.Unboxed as U
import Data.SRTree
import Data.SRTree.Eval (Target, Columns, compileLoss)
import Data.SRTree.Datasets (loadTrainingOnly)
import Data.SRTree.Print (showExpr)
import Text.ParseSR (parseSR, SRAlgs(..))
import Algorithm.SRTree.Compile (compileTree, EvalTree(..), logParameters, logParametersLatt)
import Algorithm.SRTree.Likelihoods (Distribution(..), Loss(..), buildLoss, fisherNLL, hessianNLL)
import Algorithm.SRTree.ConfidenceIntervals
    ( getStatsFromModel, paramCI, CIType(..), CI(..), BasicStats(..)
    , ProfileT(..), PType(..), getAllProfiles, getCol
    )
import Algorithm.SRTree.ModelSelection (ModelEval(..), logFunctional, logFunctionalFreq)
import Statistics.Distribution (ContDistr(quantile))
import Statistics.Distribution.FDistribution (fDistribution)
import Control.Exception (try, SomeException)
import Data.List.Split (splitOn)
import Text.Printf (printf)
import Control.Monad (forM_, when)

----------------------------------------------------------------------
-- CLI argument types
----------------------------------------------------------------------
data CIMethod = LaplaceCI | ProfileCI deriving (Show)

data ProfileTypeArg = BatesArg | ODEArg | ConstrainedArg deriving (Read)
instance Show ProfileTypeArg where
  show BatesArg       = "Bates"
  show ODEArg         = "ODE"
  show ConstrainedArg = "Constrained"

data ReportArgs = ReportArgs
  { raExprs    :: !FilePath
  , raFormat   :: !SRAlgs
  , raData     :: !FilePath
  , raHeader   :: !Bool
  , raDist     :: !Distribution
  , raCriteria :: ![ModelEval]
  , raCI       :: !CIMethod
  , raAlpha    :: !Double
  , raCIType   :: !ProfileTypeArg
  , raDbg      :: !Bool
  }

----------------------------------------------------------------------
-- Argument parser
----------------------------------------------------------------------
argParser :: Parser ReportArgs
argParser = ReportArgs
  <$> strOption ( long "exprs" <> short 'e' <> help "File with expressions, one per line" <> metavar "FILE" )
  <*> option auto ( long "format" <> short 'f' <> help "Expression format: TIR, HL, OPERON, BINGO, GOMEA, PYSR, SBP, EPLEX" <> metavar "FMT" )
  <*> strOption ( long "data" <> short 'd' <> help "Dataset file (optionally with :start:end:target:features:y_err)" <> metavar "FILE" )
  <*> switch ( long "header" <> help "Dataset has a header row" )
  <*> option auto ( long "dist" <> value Gaussian <> help "Distribution: Gaussian, Bernoulli, Poisson, LeastSquares" <> metavar "DIST" <> showDefault )
  <*> option parseCriteria ( long "criteria" <> short 'c' <> value [RMSE, R2, AIC, BIC] <> help "Comma-separated criteria" <> metavar "CRITERIA" <> showDefault )
  <*> option parseCI ( long "ci" <> value LaplaceCI <> help "CI method: Laplace, Profile" <> metavar "METHOD" <> showDefault )
  <*> option auto ( long "alpha" <> value 0.05 <> help "Significance level" <> metavar "ALPHA" <> showDefault )
  <*> option parseProfileType ( long "ci-type" <> value BatesArg <> help "Profile CI type: Bates, ODE, Constrained" <> metavar "TYPE" <> showDefault )
  <*> switch ( long "dbg" <> help "Debug: dump profile tau/theta spline points" )

parseCriteria :: ReadM [ModelEval]
parseCriteria = eitherReader $ \s ->
  case traverse parseOne (splitOn "," s) of
    Right es -> Right es
    Left  e  -> Left e
  where
    parseOne "RMSE"     = Right RMSE
    parseOne "R2"       = Right R2
    parseOne "AIC"      = Right AIC
    parseOne "BIC"      = Right BIC
    parseOne "Evidence" = Right Evidence
    parseOne "FBF"      = Right FBF
    parseOne "MDL"      = Right MDL
    parseOne "MDLLatt"  = Right MDLLatt
    parseOne "MDLFreq"  = Right MDLFreq
    parseOne "NLL"      = Right (EvalLoss (NLL Gaussian))
    parseOne s          = Left ("unknown criterion: " ++ s)

parseCI :: ReadM CIMethod
parseCI = eitherReader $ \s -> case s of
  "Laplace" -> Right LaplaceCI
  "Profile" -> Right ProfileCI
  _         -> Left ("unknown CI method: " ++ s ++ " (use Laplace or Profile)")

parseProfileType :: ReadM ProfileTypeArg
parseProfileType = eitherReader $ \s -> case s of
  "Bates"       -> Right BatesArg
  "ODE"         -> Right ODEArg
  "Constrained" -> Right ConstrainedArg
  _             -> Left ("unknown profile type: " ++ s ++ " (use Bates, ODE, or Constrained)")

----------------------------------------------------------------------
-- Report data
----------------------------------------------------------------------
data ReportData = ReportData
  { rdTree      :: Fix SRTree
  , rdTheta     :: Target
  , rdStdErr    :: Target
  , rdCriteria  :: [(ModelEval, Double)]
  , rdCIs       :: [CI]
  }

----------------------------------------------------------------------
-- Main
----------------------------------------------------------------------
main :: IO ()
main = do
  args <- execParser (info (argParser <**> helper) fullDesc)
  (xss, ys, mYerr) <- loadTrainingOnly (raData args) (raHeader args)
  content <- B.readFile (raExprs args)
  let exprs = filter (not . B.null) $ B.lines content
  mapM_ (processOne args xss ys mYerr) (zip [(1 :: Int) ..] exprs)

----------------------------------------------------------------------
-- Process a single expression
----------------------------------------------------------------------
processOne :: ReportArgs -> Columns -> Target -> Maybe Target -> (Int, B.ByteString) -> IO ()
processOne args xss ys mYerr (idx, src) = do
  result <- try $ do
    tree <- case parseSR (raFormat args) B.empty True src of
      Left e  -> fail ("parse error: " ++ e)
      Right t -> return $! relabelParams t
    let dist  = raDist args
        nRows = U.length ys
        nModelParams = countParamsUniq tree
        nParams = nModelParams
                + case dist of
                    Gaussian  -> 1
                    ROXY      -> 3
                    _         -> 0

    let et     = compileTree dist xss ys mYerr tree
        theta0 = U.replicate nParams 1.0
        thetaOpt = ctOptimizer et theta0

    when (any isNaN (U.toList thetaOpt)) $
         fail "optimisation returned NaN"

    let mseTree  = buildLoss MSE (fromIntegral nRows) tree
        mseLoss  = compileLoss xss mseTree ys mYerr thetaOpt
        nllLoss  = ctNLL et thetaOpt
        tss      = ctVar et

    let fisherDiag = fisherNLL dist mYerr xss ys tree thetaOpt
        hessCols   = hessianNLL dist mYerr xss ys tree thetaOpt
        hessLists  = map U.toList hessCols
        logP       = logParameters fisherDiag thetaOpt
        logPLatt   = logParametersLatt hessLists fisherDiag thetaOpt
        logF       = logFunctional tree
        logFFreq   = logFunctionalFreq tree
        nF         = fromIntegral nRows
        kF         = fromIntegral nParams
        crits      = map (\c -> (c, evalOne c mseLoss nllLoss tss nF kF logP logPLatt logF logFFreq))
                         (raCriteria args)

    let stats = getStatsFromModel dist mYerr xss ys tree thetaOpt
        laplaceCIs = paramCI (Laplace stats) nRows thetaOpt (raAlpha args)
    let ptype = case raCIType args of
          BatesArg       -> Bates
          ODEArg         -> ODE
          ConstrainedArg -> Constrained
    let kInt = U.length thetaOpt
        nInt = U.length ys
        profT = sqrt $ quantile (fDistribution (fromIntegral kInt) (fromIntegral $ nInt - kInt)) (1 - raAlpha args)
    cis <- case raCI args of
      LaplaceCI -> return laplaceCIs
      ProfileCI -> do
        let profiles = getAllProfiles ptype et thetaOpt (_stdErr stats) laplaceCIs (raAlpha args)
        when (raDbg args) $ forM_ (zip [0..] profiles) $ \(i, ProfileT taus thetas _ tau2theta _) -> do
          putStrLn $ "DEBUG Profile " ++ show i ++ " (opt=" ++ show (thetaOpt U.! i) ++ "):"
          putStrLn $ "  tau range: [" ++ show (if U.null taus then 0 else U.head taus)
                   ++ ", " ++ show (if U.null taus then 0 else U.last taus) ++ "]"
          putStrLn $ "  t=" ++ show profT
          putStrLn $ "  tau2theta(-t)=" ++ show (tau2theta (-profT))
                   ++ "  tau2theta(+t)=" ++ show (tau2theta profT)
          putStrLn $ "  profile points:"
          let tausL = U.toList taus
              thetasL = U.toList (getCol i thetas)
          forM_ (zip tausL thetasL) $ \(tau, th) ->
            putStrLn $ "    tau=" ++ show tau ++ "  theta=" ++ show th
        return $ paramCI (Profile stats profiles) nRows thetaOpt (raAlpha args)

    return $! ReportData
      { rdTree     = tree
      , rdTheta    = thetaOpt
      , rdStdErr   = _stdErr stats
      , rdCriteria = crits
      , rdCIs      = cis
      }

  case result of
    Right rd -> printReport idx src rd
    Left  e  -> printFailure idx src (show (e :: SomeException))

----------------------------------------------------------------------
-- Evaluate a single ModelEval from base quantities
----------------------------------------------------------------------
evalOne :: ModelEval -> Double -> Double -> Double -> Double -> Double
        -> Double -> Double -> Double -> Double -> Double
evalOne RMSE     mse _   _   _ _ _ _ _ _ = sqrt mse
evalOne R2       mse _   tss n _ _ _ _ _ = 1 - n * mse / tss
evalOne AIC      _   nll _   _ k _ _ _ _ = 2*k + 2*nll
evalOne BIC      _   nll _   n k _ _ _ _ = k * log n + 2*nll
evalOne Evidence _   nll _   n k _ _ _ _ = (1 - b) * nll - k/2 * log b
  where b = 1 / sqrt n
evalOne FBF      _   nll _   n k _ _ _ _ = res
  where b = 1 / sqrt n; nup = exp (1 - log 3)
        res = (1 - b) * nll - k/2 * log b + k/2 * log (2*pi*nup)
evalOne MDL      _   nll _   _ _ logP  _ logF _    = nll + logF + logP
evalOne MDLLatt  _   nll _   _ _ _     logPL logF _ = nll + logF + logPL
evalOne MDLFreq  _   nll _   _ _ logP  _ _    logFF = nll + logFF + logP
evalOne (EvalLoss (NLL Gaussian))  _   nll _   _ _ _  _ _    _ = nll
evalOne _        _   _   _   _ _ _     _    _    _  = 0  -- unreachable

----------------------------------------------------------------------
-- Output
----------------------------------------------------------------------
printReport :: Int -> B.ByteString -> ReportData -> IO ()
printReport idx src rd = do
  putStrLn $ "=== Expression " ++ show idx ++ " ==="
  putStrLn $ "Tree: " ++ showExpr (rdTree rd)
  putStrLn "Parameters:"
  let thetaList = U.toList (rdTheta rd)
      ciList    = rdCIs rd
  forM_ (zip3 [0..] thetaList ciList) $ \(i, th, ci) ->
    putStrLn $ "  theta" ++ show i ++ ": " ++ fmt th
            ++ " [" ++ fmt (lower_ ci) ++ ", " ++ fmt (upper_ ci) ++ "]"
  putStrLn "Model Selection:"
  forM_ (rdCriteria rd) $ \(c, v) ->
    putStrLn $ "  " ++ padRight 12 (show c) ++ ": " ++ fmt v
  putStrLn ""
  where
    fmt x | abs x < 1e-10 = "0.0000"
          | abs x >= 1e4  = printf "%.4e" x
          | otherwise     = printf "%.6f" x
    padRight n s = s ++ replicate (max 0 (n - length s)) ' '

printFailure :: Int -> B.ByteString -> String -> IO ()
printFailure idx src msg = do
  putStrLn $ "=== Expression " ++ show idx ++ " ==="
  putStrLn $ "Tree: " ++ B.unpack src
  putStrLn $ "Error: " ++ msg
  putStrLn ""
