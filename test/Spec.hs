import Test.HUnit
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Storable as VS
import Data.SRTree.Internal (param, var)
import Data.SRTree.Eval (compile)
import Algorithm.SRTree.AD.Unboxed (compileTree, compileTreeMulti, evalGrad, evalGradVec, evalGradMulti)
import qualified EqSatTests

-- Small epsilon compare for Doubles
eps :: Double
eps = 1e-9

approxEqual :: [Double] -> [Double] -> Bool
approxEqual a b = and $ zipWith (\x y -> abs (x - y) < eps) a b

test_compile :: Test
test_compile = TestCase $ do
  let xss = [VU.fromList [1.0, 2.0, 3.0]]
      tree = var 0 * param 0 + param 1
      theta = VU.fromList [2.0, 0.5]
      yhat = compile xss tree theta
      got = VU.toList yhat
      expected = [2.5, 4.5, 6.5]
  assertBool ("compile produced " ++ show got ++ " expected " ++ show expected) (approxEqual got expected)

-- Gradient correctness: the compact ctStatic layout must agree with finite
-- differences (objective) and with the row-fused `evalGrad` backend across
-- the vectorized `evalGradVec` and chunked `evalGradMulti` paths.
test_grad :: Test
test_grad = TestCase $ do
  let xss = [ VU.fromList [1.0, 2.0, 3.0, 4.0]
            , VU.fromList [0.5, 1.5, 2.5, 3.5]
            , VU.fromList [2.0, 1.0, 0.5, 0.25] ]
      y   = VU.fromList [3.1, 5.2, 7.3, 9.4]
      -- ((x0 + t0) * exp(x1)) / (x2 + t1)  -- mixes static and dynamic subtrees
      tree = (var 0 + param 0) * exp (var 1) / (var 2 + param 1)
      theta = VS.fromList [1.0, 0.5]
      ct   = compileTree xss y Nothing tree
      cts  = compileTreeMulti xss y Nothing tree
      (f0, g0) = evalGrad ct theta
      (f1, g1) = evalGradVec ct theta
      (f2, g2) = evalGradMulti cts theta
      -- finite-difference gradient
      h  = 1e-6
      gfd = VS.toList $ VS.generate (VS.length theta) $ \i ->
              let e    = VS.fromList (map (\j -> if j == i then h else 0) [0 .. VS.length theta - 1])
                  (fp, _) = evalGradVec ct (VS.zipWith (+) theta e)
                  (fm, _) = evalGradVec ct (VS.zipWith (-) theta e)
              in (fp - fm) / (2 * h)
  assertBool "evalGradVec objective != evalGrad"   (abs (f1 - f0) < 1e-6)
  assertBool "evalGradMulti objective != evalGrad" (abs (f2 - f0) < 1e-6)
  assertBool "evalGradVec gradient != finite diff"
    (and (zipWith (\a b -> abs (a - b) < 1e-4) (VS.toList g1) gfd))
  assertBool "evalGrad gradient != finite diff"
    (and (zipWith (\a b -> abs (a - b) < 1e-4) (VS.toList g0) gfd))

main :: IO ()
main = do
  let t1 = TestLabel "compile" test_compile
      t2 = TestLabel "grad" test_grad

  counts <- runTestTT $ TestList
    [ t1
    , t2
    , TestLabel "eqsat" EqSatTests.tests
    ]
  if failures counts /= 0 || errors counts /= 0
    then error "Some tests failed"
    else pure ()
