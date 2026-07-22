import Test.HUnit
import qualified Data.Vector.Unboxed as V
import Data.SRTree.Internal (param, var)
import Data.SRTree.Eval (compile)
import qualified EqSatTests

-- Small epsilon compare for Doubles
eps :: Double
eps = 1e-9

approxEqual :: [Double] -> [Double] -> Bool
approxEqual a b = and $ zipWith (\x y -> abs (x - y) < eps) a b

test_compile :: Test
test_compile = TestCase $ do
  let xss = [V.fromList [1.0, 2.0, 3.0]]
      tree = var 0 * param 0 + param 1
      theta = V.fromList [2.0, 0.5]
      yhat = compile xss tree theta
      got = V.toList yhat
      expected = [2.5, 4.5, 6.5]
  assertBool ("compile produced " ++ show got ++ " expected " ++ show expected) (approxEqual got expected)

main :: IO ()
main = do
  let t1 = TestLabel "compile" test_compile

  counts <- runTestTT $ TestList
    [ t1
    , TestLabel "eqsat" EqSatTests.tests
    ]
  if failures counts /= 0 || errors counts /= 0
    then error "Some tests failed"
    else pure ()
