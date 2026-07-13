import Test.HUnit
import qualified Data.Vector.Unboxed as V
import Data.SRTree.Internal (param, var)
import Data.SRTree.Eval (compile, Target, Columns)
import Algorithm.SRTree.Likelihoods
  ( nll, gradNLL, gradNLLAD, gradLossAD
  , mae, mape, pinballLoss, rmse, r2
  , predict, buildLoss, buildDistLoss, buildPredictor
  , Distribution(..), Loss(..)
  )
import Algorithm.SRTree.Likelihood ( Likelihood(..), mkLikelihood )
import Algorithm.SRTree.ModelSelection
  ( ModelEval(..), buildEval, aic, bic, mdl, EvaluatedTree(..) )

-- Small epsilon compare for Doubles
eps :: Double
eps = 1e-9

approxEqual :: [Double] -> [Double] -> Bool
approxEqual a b = and $ zipWith (\x y -> abs (x - y) < eps) a b

test_compile :: Test
test_compile = TestCase $ do
  -- dataset: single column with three rows [1,2,3]
  let xss = [V.fromList [1.0, 2.0, 3.0]]
      -- tree: t0 * x0 + t1
      tree = var 0 * param 0 + param 1
      theta = V.fromList [2.0, 0.5]
      yhat = compile xss tree theta
      got = V.toList yhat
      expected = [2.5, 4.5, 6.5]
  assertBool ("compile produced " ++ show got ++ " expected " ++ show expected) (approxEqual got expected)

-- | Reference finite-difference gradient of an arbitrary scalar function,
-- used here as an independent ground truth (distinct from the library's
-- own 'gradNLL', which is hard-coded to the MSE objective regardless of
-- the distribution passed to it).
numericGrad :: (Target -> Double) -> Target -> Target
numericGrad f theta = V.generate p go
  where
    p  = V.length theta
    h  = 1e-6
    go i = let thp = theta V.// [(i, (theta V.! i) + h)]
               thm = theta V.// [(i, (theta V.! i) - h)]
           in (f thp - f thm) / (2 * h)

main :: IO ()
main = do
  let xss = [V.fromList [1.0, 2.0, 3.0]] :: Columns
      tree = var 0 * param 0 + param 1
      theta_true = V.fromList [2.0, 0.5]
      ys = compile xss tree theta_true

      -- test 1: compile correctness
      t1 = TestLabel "compile" test_compile

      -- test 2: nll at true theta should be zero for MSE
      test_nll = TestCase $ do
        let v = nll MSE Nothing xss ys tree theta_true
        assertBool ("nll at true theta should be ~0, got " ++ show v) (abs v < 1e-12)

      -- test 3: old finite-diff gradNLL vs new AD-based gradNLLAD, for MSE
      -- (the one case where gradNLL's hard-coded MSE objective is the
      -- correct objective, so both implementations should agree closely).
      -- Both are keyed on 'Distribution' here.
      test_grad_mse = TestCase $ do
        let theta = V.fromList [2.0, 0.6]
            (f_fd, g_fd) = gradNLL   MSE Nothing xss ys tree theta
            (f_ad, g_ad) = gradNLLAD MSE Nothing xss ys tree theta

        assertBool ("objective mismatch: fd " ++ show f_fd ++ " ad " ++ show f_ad)
                    (abs (f_fd - f_ad) < 1e-6)
        let diffs = V.toList $ V.zipWith (\x y -> abs (x - y)) g_fd g_ad
        assertBool ("grad mismatch " ++ show diffs) (all (< 1e-4) diffs)

      -- test 4: gradNLLAD's analytic (AD) gradient vs an independent
      -- numeric gradient of the *exact same* objective it computes (its
      -- own 'fst' component), for the Gaussian distribution. This is a
      -- classic gradient-check: it validates the AD backward pass
      -- without depending on 'nll' (whose Gaussian formula branches in a
      -- way that is not always consistent with 'buildDistLoss', which is
      -- what 'gradNLLAD' actually differentiates -- a separate,
      -- pre-existing inconsistency outside the scope of this change).
      test_grad_gaussian = TestCase $ do
        let thetaG      = V.fromList [2.0, 0.6, 0.1]  -- last param: log-variance
            objAt th     = fst $ gradNLLAD Gaussian Nothing xss ys tree th
            g_num        = numericGrad objAt thetaG
            (_, g_ad)    = gradNLLAD Gaussian Nothing xss ys tree thetaG
            diffs        = V.toList $ V.zipWith (\x y -> abs (x - y)) g_num g_ad
        assertBool ("Gaussian grad mismatch (numeric vs AD): " ++ show diffs)
                    (all (< 1e-3) diffs)

      -- test 5: the Likelihood abstraction (keyed on 'Distribution') wires
      -- up the same functions
      test_likelihood = TestCase $ do
        let lik   = mkLikelihood MSE
            theta = V.fromList [2.0, 0.6]
            (f_fd, g_fd) = likGradFD lik Nothing xss ys tree theta
            (f_ad, g_ad) = likGrad   lik Nothing xss ys tree theta
        assertBool "likDist mismatch" (likDist lik == MSE)
        assertBool ("Likelihood objective mismatch " ++ show (f_fd, f_ad))
                    (abs (f_fd - f_ad) < 1e-6)
        let diffs = V.toList $ V.zipWith (\x y -> abs (x - y)) g_fd g_ad
        assertBool ("Likelihood grad mismatch " ++ show diffs) (all (< 1e-4) diffs)

      -- test 6: buildLoss MAE / MAPE / Pinball produce per-row trees whose
      -- row-sum (as computed by 'gradLossAD', via "Algorithm.SRTree.AD")
      -- matches the corresponding data-level function ('mae', 'mape',
      -- 'pinballLoss').
      test_build_loss_mae_mape_pinball = TestCase $ do
        let theta    = V.fromList [2.0, 0.6]
            objMAE   = fst $ gradLossAD MAE Nothing xss ys tree theta
            expMAE   = mae xss ys tree theta

            objMAPE  = fst $ gradLossAD MAPE Nothing xss ys tree theta
            expMAPE  = mape xss ys tree theta

            tau      = 0.7
            objPin   = fst $ gradLossAD (Pinball tau) Nothing xss ys tree theta
            expPin   = pinballLoss tau xss ys tree theta

        assertBool ("MAE mismatch: got " ++ show objMAE ++ " expected " ++ show expMAE)
                    (abs (objMAE - expMAE) < 1e-6)
        assertBool ("MAPE mismatch: got " ++ show objMAPE ++ " expected " ++ show expMAPE)
                    (abs (objMAPE - expMAPE) < 1e-5) -- MAPE has an epsilon-guarded denominator
        assertBool ("Pinball mismatch: got " ++ show objPin ++ " expected " ++ show expPin)
                    (abs (objPin - expPin) < 1e-6)

      -- test 7: buildLoss (NLL dist) must delegate to 'buildDistLoss',
      -- so 'gradLossAD (NLL dist)' should match 'gradNLLAD dist' exactly.
      test_build_loss_nll_delegates = TestCase $ do
        let theta = V.fromList [2.0, 0.6]
            (fA, gA) = gradLossAD (NLL MSE) Nothing xss ys tree theta
            (fB, gB) = gradNLLAD  MSE       Nothing xss ys tree theta
        assertBool ("NLL delegation objective mismatch " ++ show (fA, fB))
                    (abs (fA - fB) < 1e-12)
        let diffs = V.toList $ V.zipWith (\x y -> abs (x - y)) gA gB
        assertBool ("NLL delegation grad mismatch " ++ show diffs) (all (< 1e-12) diffs)

      -- test 8: buildPredictor wraps the tree with the correct inverse
      -- link function ('exp' for Poisson, logistic for Bernoulli,
      -- identity otherwise), matching the data-level 'predict' function.
      -- Both are keyed on 'Distribution'.
      test_build_predictor = TestCase $ do
        let treeP  = param 0 + param 1 * var 0
            thetaP = V.fromList [0.5, 1.2]
            xssP   = [V.fromList [0.1, 0.2, 0.3]] :: Columns

            check lbl dist =
              let got = V.toList $ compile xssP (buildPredictor dist treeP) thetaP
                  exp' = V.toList $ predict dist treeP thetaP xssP
              in assertBool (lbl ++ " mismatch: got " ++ show got ++ " expected " ++ show exp')
                              (approxEqual got exp')

        check "buildPredictor Poisson"   Poisson
        check "buildPredictor Bernoulli" Bernoulli
        check "buildPredictor MSE"       MSE

      -- test 9: 'ModelEval'/'buildEval' dispatches to the right metric.
      -- We build an 'EvaluatedTree' directly (bypassing the
      -- compile/fisher/hessian machinery, which is irrelevant to what
      -- we're testing here: that 'buildEval' routes each 'ModelEval'
      -- constructor to the correct underlying computation).
      test_model_eval = TestCase $ do
        let theta = V.fromList [2.0, 0.6]
            et = EvaluatedTree
                   { valLoss             = mse' xss ys tree theta
                   , valTheta            = theta
                   , valRows             = fromIntegral (V.length ys)
                   , valParams           = fromIntegral (V.length theta)
                   , valTree             = tree
                   , valLogParams        = 0
                   , valLogParamsLattice = 0
                   }
            mse' = \x y t th -> nll MSE Nothing x y t th -- nll MSE == mse

            expRMSE   = rmse xss ys tree theta
            expR2     = r2   xss ys tree theta
            expAIC    = aic et
            expBIC    = bic et
            expMDL    = mdl et
            expMAE    = mae xss ys tree theta
            expNLLMSE = nll MSE Nothing xss ys tree theta

        assertBool "RMSE mismatch"  (abs (buildEval RMSE xss ys et - expRMSE) < 1e-9)
        assertBool "R2 mismatch"    (abs (buildEval R2   xss ys et - expR2)   < 1e-9)
        assertBool "AIC mismatch"   (abs (buildEval AIC  xss ys et - expAIC)  < 1e-9)
        assertBool "BIC mismatch"   (abs (buildEval BIC  xss ys et - expBIC)  < 1e-9)
        assertBool "MDL mismatch"   (abs (buildEval MDL  xss ys et - expMDL)  < 1e-9)
        assertBool "EvalLoss MAE mismatch"
                    (abs (buildEval (EvalLoss MAE) xss ys et - expMAE) < 1e-9)
        assertBool "EvalLoss (NLL MSE) mismatch"
                    (abs (buildEval (EvalLoss (NLL MSE)) xss ys et - expNLLMSE) < 1e-9)

  counts <- runTestTT $ TestList
    [ t1
    , TestLabel "nll" test_nll
    , TestLabel "grad-mse-fd-vs-ad" test_grad_mse
    , TestLabel "grad-gaussian-numeric-vs-ad" test_grad_gaussian
    , TestLabel "likelihood-abstraction" test_likelihood
    , TestLabel "build-loss-mae-mape-pinball" test_build_loss_mae_mape_pinball
    , TestLabel "build-loss-nll-delegates" test_build_loss_nll_delegates
    , TestLabel "build-predictor" test_build_predictor
    , TestLabel "model-eval" test_model_eval
    ]
  if failures counts /= 0 || errors counts /= 0
    then error "Some tests failed"
    else pure ()
