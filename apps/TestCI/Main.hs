{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import qualified Data.ByteString.Char8 as B
import Data.SRTree
import Data.SRTree.Print (showExpr)
import Data.SRTree.Eval (Target, Columns, compile)
import Data.SRTree.Datasets (loadDataset)
import Data.SRTree.Recursion (Fix(..))
import Algorithm.SRTree.ConfidenceIntervals
import Algorithm.SRTree.Compile (compileTree, EvalTree(..))
import Algorithm.SRTree.NonlinearOpt (minimizeNLL, minimizeNLLWith, compileLossAndGrad)
import Algorithm.SRTree.Likelihoods (Distribution(..), Loss(..))
import Algorithm.SRTree.AD (ADBackEnd(..))
import Algorithm.SRTree.AD.Unboxed (setMTPopParallel)
import Numeric.Optimization.NLOPT (LocalAlgorithm(..))
import Text.ParseSR (parseSR, SRAlgs(..))
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Generic as G
import Data.List (intercalate, foldl', maximumBy, isSuffixOf)
import Data.Maybe (fromMaybe)
import System.IO (hFlush, stdout, hPutStrLn, stderr)
import System.Environment (getArgs)
import System.Random (randomRIO)
import Control.Exception (catch, SomeException, evaluate)
import Control.Monad (forM_, when)
import Data.Either (isRight)

-- | A test case: expression string, description
data TestCase = TestCase
  { tcName        :: String
  , tcExpr        :: String
  , tcDesc        :: String
  } deriving (Show)

-- | All test cases
testCases :: [TestCase]
testCases =
  [ TestCase
      { tcName = "exp-param"
      , tcExpr = "Exp(t0 + (x1 * (t1 * ((x0 * x0) + t2))))"
      , tcDesc = "Parameterized exponential (similar shape to AGENTS.md example)"
      }
  , TestCase
      { tcName = "linear"
      , tcExpr = "t0 * x0 + t1"
      , tcDesc = "Simple linear model (well-conditioned)"
      }
  , TestCase
      { tcName = "quadratic"
      , tcExpr = "t0 * x0 * x0 + t1 * x0 + t2"
      , tcDesc = "Quadratic polynomial"
      }
  , TestCase
      { tcName = "rational"
      , tcExpr = "t0 / (t1 + x0)"
      , tcDesc = "Rational function (steep near pole)"
      }
  , TestCase
      { tcName = "sine"
      , tcExpr = "t0 * sin(t1 * x0 + t2)"
      , tcDesc = "Sinusoidal model"
      }
  , TestCase
      { tcName = "product"
      , tcExpr = "t0 * x0 * x1 + t1"
      , tcDesc = "Two-variable product"
      }
  , TestCase
      { tcName = "exp-linear"
      , tcExpr = "Exp(t0 * x0 + t1)"
      , tcDesc = "Exponential of linear (simpler than deep exp)"
      }
  , TestCase
      { tcName = "power"
      , tcExpr = "t0 * x0 ** t1"
      , tcDesc = "Power law"
      }
  , TestCase
      { tcName = "linear-mse"
      , tcExpr = "t0 * x0 + t1"
      , tcDesc = "Linear model fitted with MSE (Bates 1985 original use case)"
      }
  ]

main :: IO ()
main = do
  args <- getArgs
  let filterName = if null args then Nothing else Just (head args)

  putStrLn "========================================================================"
  putStrLn "  Profile Likelihood CI Backend Investigation"
  putStrLn "========================================================================"
  putStrLn ""

  -- Load dataset
  let dataSpec = "../eggp/gaussian_train.csv:::y_noise_02:x1,x2"
  putStrLn $ "Loading dataset: " ++ dataSpec
  hFlush stdout
  ((xTr, yTr, _xVal, _yVal), (mYErr, _), _varnames, _target) <-
    loadDataset dataSpec True `catch` (\(e :: SomeException) -> do
      putStrLn $ "ERROR loading dataset: " ++ show e
      error "Failed to load dataset")

  let nSamples = VU.length yTr
  putStrLn $ "  Samples: " ++ show nSamples
  putStrLn $ "  Features: " ++ show (length xTr)
  putStrLn ""

  let cases = case filterName of
        Nothing -> testCases
        Just name -> filter (\tc -> tcName tc == name) testCases

  mapM_ (runTestCase xTr yTr mYErr nSamples) cases

  putStrLn ""
  putStrLn "========================================================================"
  putStrLn "  Summary"
  putStrLn "========================================================================"
  putStrLn ""
  putStrLn "Key observations:"
  putStrLn "  - Laplace: uses Hessian inverse; fast but may be inaccurate for nonlinear models"
  putStrLn "  - Bates: classical profile walk; accurate but slow"
  putStrLn "  - ODE: Chen & Jennrich ODE-based profile; fast and accurate"
  putStrLn "  - Constrained: bisection on re-optimized endpoints; fast but may fail"
  putStrLn ""
  putStrLn "Issues to investigate:"
  putStrLn "  1. Constrained backend NaN on steep exponential expressions"
  putStrLn "  2. tau_max' threshold correctness for NLL Gaussian"
  putStrLn "  3. Nelder-Mead convergence in augmented Lagrangian"
  putStrLn "  4. One-sided CI failures"

-- | Run a single test case through all backends
runTestCase :: [VU.Vector Double] -> VU.Vector Double -> Maybe (VU.Vector Double) -> Int -> TestCase -> IO ()
runTestCase xTr yTr mYErr nSamples tc = do
  putStrLn "------------------------------------------------------------------------"
  putStrLn $ "Test: " ++ tcName tc
  putStrLn $ "  Description: " ++ tcDesc tc
  putStrLn $ "  Expression: " ++ tcExpr tc
  putStrLn ""

  -- Parse expression: convert String to ByteString for parseSR
  let parsed = parseSR TIR (B.pack "x0,x1") False (B.pack (tcExpr tc))
  case parsed of
    Left err -> putStrLn $ "  PARSE ERROR: " ++ err
    Right rawTree -> do
      let tree = relabelParams rawTree
      let nParams = countParamsUniq tree
      putStrLn $ "  Parsed tree: " ++ showExpr tree
      putStrLn $ "  Unique params: " ++ show nParams

      if nParams == 0
        then putStrLn "  SKIP: no parameters to profile"
        else do
          -- Detect MSE cases (name ends with "-mse")
          let useMSE = "-mse" `isSuffixOf` tcName tc
              dist = if useMSE then LeastSquares else Gaussian
              totalParams = if useMSE then nParams else nParams + 1  -- +1 for sigma when Gaussian

          putStrLn $ "  Loss: " ++ (if useMSE then "MSE (LeastSquares)" else "NLL Gaussian")
          putStrLn $ "  Total params: " ++ show totalParams
          putStrLn ""

          -- Fit with multiple restarts
          putStrLn "  Fitting..."
          hFlush stdout
          setMTPopParallel True
          results <- fitMultipleRestarts dist mYErr xTr yTr tree totalParams 5
          setMTPopParallel False

          let (bestNLL, bestTheta) = maximumBy (\(a,_) (b,_) -> compare a b) results
              theta_opt = bestTheta
              negNLL = negate bestNLL

          putStrLn $ "  Best loss: " ++ show negNLL
          putStrLn $ "  Theta: " ++ show (VU.toList theta_opt)
          putStrLn ""

          -- Compile the EvalTree for CI computation
          let et = compileTree dist xTr yTr mYErr tree

          -- Verify the optimizer agrees
          let theta_verify = ctOptimizer et theta_opt
              nll_verify = ctNLL et theta_verify
          putStrLn $ "  Verified loss (via EvalTree): " ++ show nll_verify

          -- Compute standard errors from Hessian
          let stats = getStatsFromModel dist mYErr xTr yTr tree theta_opt
              stdErrs = _stdErr stats
          putStrLn $ "  Std errors (Hessian): " ++ show (VU.toList stdErrs)
          putStrLn ""

          let paramNames = [ "t" ++ show i | i <- [0 .. nParams - 1] ]
                           ++ if useMSE then [] else ["sigma"]

          -- ---- LAPLACE ----
          putStrLn "  === LAPLACE ==="
          let laplaceCI = paramCI (Laplace stats) nSamples theta_opt 0.05
          putStrLn $ "  95% CIs:"
          putStrLn $ "    " ++ showCIList (zip paramNames laplaceCI)
          putStrLn ""

          -- ---- BATES (profile walk) ----
          putStrLn "  === BATES (profile walk) ==="
          catch (do
            let estCIs = laplaceCI
                profiles_bates = getAllProfiles Bates et theta_opt stdErrs estCIs 0.05
                batesCI = paramCI (Profile stats profiles_bates) nSamples theta_opt 0.05
            putStrLn $ "  95% CIs:"
            putStrLn $ "    " ++ showCIList (zip paramNames batesCI)
            putStrLn $ "  Widths: " ++ show (map (\(CI _ l h) -> h - l) batesCI)
            -- Debug: show first/last profile points
            forM_ (zip [0::Int ..] profiles_bates) $ \(ix, prof) -> do
              let taus = _taus prof
                  cols = _thetas prof
                  nT = VU.length taus
              putStrLn $ "  Profile t" ++ show ix ++ ": " ++ show nT ++ " points"
              when (nT > 0) $ do
                let firstTau = taus VU.! 0
                    lastTau = taus VU.! (nT - 1)
                    firstTh = (cols !! ix) VU.! 0
                    lastTh = (cols !! ix) VU.! (nT - 1)
                    optTh = theta_opt VU.! ix
                putStrLn $ "    tau=[" ++ show firstTau ++ ", " ++ show lastTau ++ "]"
                putStrLn $ "    theta=[" ++ show firstTh ++ ", " ++ show lastTh ++ "] opt=" ++ show optTh
            ) (\(e :: SomeException) -> putStrLn $ "  ERROR: " ++ show e)
          putStrLn ""

          -- ---- ODE (Chen & Jennrich) ----
          putStrLn "  === ODE (Chen & Jennrich) ==="
          catch (do
            let estCIs = laplaceCI
                profiles_ode = getAllProfiles ODE et theta_opt stdErrs estCIs 0.05
                odeCI = paramCI (Profile stats profiles_ode) nSamples theta_opt 0.05
            putStrLn $ "  95% CIs:"
            putStrLn $ "    " ++ showCIList (zip paramNames odeCI)
            putStrLn $ "  Widths: " ++ show (map (\(CI _ l h) -> h - l) odeCI)
            ) (\(e :: SomeException) -> putStrLn $ "  ERROR: " ++ show e)
          putStrLn ""

          -- ---- CONSTRAINED ----
          putStrLn "  === CONSTRAINED (bisection) ==="
          catch (do
            let profiles_cnstr = getAllProfiles Constrained et theta_opt stdErrs [] 0.05
                cnstrCI = paramCI (Profile stats profiles_cnstr) nSamples theta_opt 0.05
            putStrLn $ "  95% CIs:"
            putStrLn $ "    " ++ showCIList (zip paramNames cnstrCI)
            putStrLn $ "  Widths: " ++ show (map (\(CI _ l h) -> h - l) cnstrCI)
            -- Check for NaN
            let hasNaN = any (\(CI _ l h) -> isNaN l || isNaN h) cnstrCI
            when hasNaN $ putStrLn $ "  *** WARNING: NaN detected in Constrained CI ***"
            ) (\(e :: SomeException) -> putStrLn $ "  ERROR: " ++ show e)
          putStrLn ""

          -- ---- Detailed profiling of Constrained for the problematic case ----
          when (nParams >= 2) $ do
            putStrLn "  === DETAILED CONSTRAINED INVESTIGATION ==="
            investigateConstrained et theta_opt stdErrs totalParams
            putStrLn ""

-- | Fit with multiple random restarts
fitMultipleRestarts :: Distribution -> Maybe (VU.Vector Double) -> [VU.Vector Double] -> VU.Vector Double
                    -> Fix SRTree -> Int -> Int -> IO [(Double, VU.Vector Double)]
fitMultipleRestarts dist mYErr xTr yTr tree nParams nRep = do
  let funAndGrad = compileLossAndGrad MultiThread (NLL dist) mYErr xTr yTr tree
      runRestart = do
        theta0 <- VU.replicateM nParams (randomRIO (-2, 2))
        let (theta, lossVal, _) = minimizeNLLWith funAndGrad TNEWTON 200 theta0
        pure (negate lossVal, theta)
  results <- sequence [ runRestart | _ <- [1..nRep] ]
  -- Also try from zeros
  let theta0_zero = VU.replicate nParams 0.0
      (theta_zero, loss_zero, _) = minimizeNLLWith funAndGrad TNEWTON 200 theta0_zero
  pure $ (negate loss_zero, theta_zero) : results

-- | Show a list of CIs with parameter names
showCIList :: [(String, CI)] -> String
showCIList = intercalate "\n    " . map (\(name, CI est lo hi) ->
  name ++ ": " ++ showF lo ++ " <= " ++ showF est ++ " <= " ++ showF hi)
  where showF x
          | isNaN x     = "NaN"
          | isInfinite x = if x > 0 then "+Inf" else "-Inf"
          | otherwise   = show (fromIntegral (round (x * 1e4) :: Int) / 1e4 :: Double)

-- | Detailed investigation of the Constrained backend
investigateConstrained :: EvalTree -> VU.Vector Double -> VU.Vector Double -> Int -> IO ()
investigateConstrained et theta_opt stdErrs nParams = do
  let nll_opt = ctNLL et theta_opt
      n = ctRows et
      k = VU.length theta_opt
      chi2_1 = 3.841  -- chi2 quantile for 1 df at 0.95

  putStrLn $ "  nll_opt = " ++ show nll_opt
  putStrLn $ "  n = " ++ show n ++ ", k = " ++ show k
  putStrLn $ "  chi2_1(0.95) = " ++ show chi2_1
  putStrLn ""

  -- Corrected tau_max' calculation
  let tau_max' = chi2_1 / 2
      tau_max_old = nll_opt * chi2_1 / fromIntegral n  -- OLD (buggy)
  putStrLn $ "  Corrected tau_max' (chi2_1/2)          = " ++ show tau_max'
  putStrLn $ "  OLD tau_max' (nll_opt * chi2_1 / n)     = " ++ show tau_max_old ++ " (WRONG)"
  putStrLn ""

  -- Test each parameter
  forM_ [0 .. nParams - 1] $ \ix -> do
    putStrLn $ "  Parameter t" ++ show ix ++ ":"
    putStrLn $ "    MLE = " ++ show (theta_opt VU.! ix)
    putStrLn $ "    StdErr = " ++ show (stdErrs VU.! ix)

    -- Test getEndPoint directly
    let getPoint isLeft = getEndPoint et theta_opt tau_max' (stdErrs VU.! ix) ix isLeft
    catch (do
      let leftPt = getPoint True
          rightPt = getPoint False
      putStrLn $ "    Left endpoint  = " ++ show leftPt
      putStrLn $ "    Right endpoint = " ++ show rightPt
      when (isNaN leftPt || isNaN rightPt) $
        putStrLn $ "    *** NaN detected! ***"
      when (leftPt > rightPt) $
        putStrLn $ "    *** Left > Right: reversed interval! ***"
      ) (\(e :: SomeException) -> putStrLn $ "    ERROR in getEndPoint: " ++ show e)

    -- Test the profiling function (fix ix, re-optimize others)
    putStrLn $ "    Testing ctOptimizerFixed..."
    catch (do
      let delta = stdErrs VU.! ix * 0.5
          theta_left = VU.generate nParams (\j -> if j == ix then (theta_opt VU.! ix) - delta else theta_opt VU.! j)
          theta_right = VU.generate nParams (\j -> if j == ix then (theta_opt VU.! ix) + delta else theta_opt VU.! j)
          reopt_left = ctOptimizerFixed et ix theta_left
          reopt_right = ctOptimizerFixed et ix theta_right
          nll_left = ctNLL et reopt_left
          nll_right = ctNLL et reopt_right
      putStrLn $ "    theta_left  (fixed at " ++ show (theta_opt VU.! ix - delta) ++ ") -> reopt NLL = " ++ show nll_left
      putStrLn $ "    theta_right (fixed at " ++ show (theta_opt VU.! ix + delta) ++ ") -> reopt NLL = " ++ show nll_right
      putStrLn $ "    NLL increase left:  " ++ show (nll_left - nll_opt)
      putStrLn $ "    NLL increase right: " ++ show (nll_right - nll_opt)
      when (isNaN nll_left || isNaN nll_right) $
        putStrLn $ "    *** NaN in re-optimized NLL! ***"
      ) (\(e :: SomeException) -> putStrLn $ "    ERROR in ctOptimizerFixed: " ++ show e)
    putStrLn ""
