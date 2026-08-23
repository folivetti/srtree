module CITests (tests) where

import Test.HUnit
import Algorithm.SRTree.ConfidenceIntervals
  ( monotoneInc, monotoneDec, enforceMonotonicTau, enforceMonotonicTheta, createSplines )
import Algorithm.SRTree.Utils ( genSplineFun )
import qualified Data.Vector.Unboxed as U

eps :: Double
eps = 1e-9

approxEq :: Double -> Double -> Bool
approxEq a b = abs (a - b) < eps

-- | monotoneInc keeps longest non-decreasing prefix of second elements
test_monotoneInc :: Test
test_monotoneInc = TestLabel "monotoneInc" $ TestCase $ do
  -- already non-decreasing: keep all
  assertEqual "all kept" [(1,10),(2,20),(3,30)] (monotoneInc [(1,10),(2,20),(3,30)])
  -- drop trailing decrease
  assertEqual "drop tail" [(1,10),(2,20)] (monotoneInc [(1,10),(2,20),(3,15)])
  -- single element
  assertEqual "single" [(1,5)] (monotoneInc [(1,5)])
  -- empty
  assertEqual "empty" [] (monotoneInc [])
  -- flat is ok (non-decreasing)
  assertEqual "flat ok" [(1,5),(2,5),(3,5)] (monotoneInc [(1,5),(2,5),(3,5)])
  -- decrease at start: keeps first, skips the decrease, then keeps later increase
  assertEqual "early decrease" [(1,10),(3,15)] (monotoneInc [(1,10),(2,5),(3,15)])

-- | monotoneDec keeps longest non-increasing prefix of second elements
test_monotoneDec :: Test
test_monotoneDec = TestLabel "monotoneDec" $ TestCase $ do
  -- already non-increasing: keep all
  assertEqual "all kept" [(1,30),(2,20),(3,10)] (monotoneDec [(1,30),(2,20),(3,10)])
  -- drop trailing increase
  assertEqual "drop tail" [(1,30),(2,20)] (monotoneDec [(1,30),(2,20),(3,25)])
  -- single element
  assertEqual "single" [(1,5)] (monotoneDec [(1,5)])
  -- empty
  assertEqual "empty" [] (monotoneDec [])
  -- flat is ok (non-increasing)
  assertEqual "flat ok" [(1,5),(2,5),(3,5)] (monotoneDec [(1,5),(2,5),(3,5)])

-- | enforceMonotonicTau: split at tau=0, negative half non-increasing theta,
--   positive half non-decreasing theta
test_enforceMonotonicTau :: Test
test_enforceMonotonicTau = TestLabel "enforceMonotonicTau" $ TestCase $ do
  -- well-formed data (monotonic in both halves)
  let wellFormed = [(-2.0, 0.2), (-1.0, 0.5), (0.0, 1.0), (1.0, 1.5), (2.0, 1.8)]
  assertEqual "well-formed" wellFormed (enforceMonotonicTau wellFormed)

  -- non-monotonic negative half (bump): (-1.0, 0.5) then (-0.5, 0.7) is increasing
  let nonMonNeg = [(-2.0, 0.2), (-1.5, 0.4), (-1.0, 0.5), (-0.5, 0.7), (0.0, 1.0), (0.5, 1.3), (1.0, 1.5)]
  let result = enforceMonotonicTau nonMonNeg
  -- negative half: theta non-decreasing from -tau_max to 0, so all kept
  assertBool "negative half preserved" (length result >= 5)

  -- non-monotonic positive half: theta decreases at tau=1.5
  let nonMonPos = [(-1.0, 0.5), (0.0, 1.0), (0.5, 1.3), (1.0, 1.5), (1.5, 1.4), (2.0, 1.8)]
  let result2 = enforceMonotonicTau nonMonPos
  -- should drop (1.5, 1.4) since it breaks non-decreasing
  let posPart = filter (\(t,_) -> t > 0) result2
      pairs = zip posPart (tail posPart)
  assertBool "positive monotonic" (all (\((_,a), (_,b)) -> b >= a) pairs)
  where

-- | enforceMonotonicTheta: split at theta=optTh, left half non-increasing tau,
--   right half non-decreasing tau
test_enforceMonotonicTheta :: Test
test_enforceMonotonicTheta = TestLabel "enforceMonotonicTheta" $ TestCase $ do
  -- optTh = 1.0, data sorted by theta
  let optTh = 1.0
      wellFormed = [(0.2, -2.0), (0.5, -1.0), (1.0, 0.0), (1.5, 1.0), (2.0, 2.0)]
  assertEqual "well-formed" wellFormed (enforceMonotonicTheta optTh wellFormed)

  -- split at theta=1.0 (optTh), not theta=0
  -- data: theta < 1.0 should have negative tau, theta > 1.0 should have positive tau
  let mixedThetas = [(0.5, -1.0), (0.8, -0.5), (1.0, 0.0), (1.2, 0.5), (1.5, 1.0)]
  let result = enforceMonotonicTheta optTh mixedThetas
  assertEqual "all kept" mixedThetas result

  -- non-monotonic: tau jumps back at theta=1.2
  let nonMon = [(0.5, -1.0), (1.0, 0.0), (1.2, 0.8), (1.5, 0.6), (2.0, 2.0)]
  let result2 = enforceMonotonicTheta optTh nonMon
  -- right half (theta > 1.0): tau non-decreasing, so (1.5, 0.6) after (1.2, 0.8) is dropped
  assertBool "right half monotonic" (length result2 < length nonMon)

-- | createSplines: basic spline creation and evaluation
test_createSplines :: Test
test_createSplines = TestLabel "createSplines" $ TestCase $ do
  -- Create a simple linear profile: tau = theta - 1.0 (optTh = 1.0)
  let n = 20
      optTh = 1.0
      se = 0.5
      tau_max = 3.0
      taus = U.fromList [ -tau_max + 2*tau_max * fromIntegral i / fromIntegral (n-1) | i <- [0..n-1] ]
      -- theta = 1.0 + tau/3 (linear relationship)
      thetas = [ U.fromList [ optTh + (taus U.! i) / 3.0 | _ <- [0] ] | i <- [0..n-1] ]
      (tau2theta, _theta2tau) = createSplines taus thetas se tau_max 0 optTh

  -- at tau=0, should return approximately optTh
  let atZero = tau2theta 0.0
  assertBool ("tau2theta(0) ~ optTh: " ++ show atZero) (approxEq atZero optTh)

  -- at tau=tau_max, should be approximately optTh + tau_max/3
  let atMax = tau2theta tau_max
      expected_atMax = optTh + tau_max / 3.0
  assertBool ("tau2theta(tau_max) ~ expected: " ++ show atMax ++ " vs " ++ show expected_atMax)
    (abs (atMax - expected_atMax) < 0.5)  -- generous tolerance for spline overshoot

  -- at tau=-tau_max, should be approximately optTh - tau_max/3
  let atMin = tau2theta (-tau_max)
      expected_atMin = optTh - tau_max / 3.0
  assertBool ("tau2theta(-tau_max) ~ expected: " ++ show atMin ++ " vs " ++ show expected_atMin)
    (abs (atMin - expected_atMin) < 0.5)

-- | Regression: negative-tau data must not be dropped
test_negative_tau_preserved :: Test
test_negative_tau_preserved = TestLabel "negative_tau_preserved" $ TestCase $ do
  let optTh = 1.0
      se = 0.5
      tau_max = 3.0
      -- Monotonically decreasing theta for negative tau
      negTaus = [-2.5, -2.0, -1.5, -1.0, -0.5]
      posTaus = [0.5, 1.0, 1.5, 2.0, 2.5]
      taus = U.fromList (negTaus ++ [0.0] ++ posTaus)
      thetas = [ U.fromList [ optTh + (taus U.! i) / 3.0 ] | i <- [0 .. U.length taus - 1] ]
      (tau2theta, _) = createSplines taus thetas se tau_max 0 optTh

  -- The spline MUST give a value below optTh for negative tau
  let atNeg = tau2theta (-2.0)
  assertBool ("tau2theta(-2.0) < optTh: got " ++ show atNeg)
    (atNeg < optTh - 0.1)

  -- The spline MUST give a value above optTh for positive tau
  let atPos = tau2theta 2.0
  assertBool ("tau2theta(2.0) > optTh: got " ++ show atPos)
    (atPos > optTh + 0.1)

tests :: Test
tests = TestLabel "ConfidenceIntervals" $ TestList
  [ test_monotoneInc
  , test_monotoneDec
  , test_enforceMonotonicTau
  , test_enforceMonotonicTheta
  , test_createSplines
  , test_negative_tau_preserved
  ]
