import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Derivative
import Data.SRTree.AD

import qualified Data.Vector as V
import Numeric.AD.Double ( grad )
import Test.HUnit 

-- test expressions
exprs = [
    param 0 * sin ( param 1)
  , sin (param 0) + cos (param 1)
  , 0.5 * sin (param 0) + 0.7 * cos (param 1)
  , log (param 0) + param 0 * param 1 - sin (param 1)
  , 1 / param 0 * param 1
  , param 0 + param 1 + param 0 * param 1 + sin (param 0) + sin (param 1) + cos (param 0) + cos (param 1) + sin (param 0 * param 1) + cos (param 0 * param 1)
  , sin (exp (param 0) + param 1)
  ]

-- autodiff with multiple occurrences of vars
autoDiffMult :: [[Double]]
autoDiffMult =  [ grad (\[x,y] -> x * sin y) [2,3]
          , grad (\[x,y] -> sin x + cos y) [2,3]
          , grad (\[x,y] -> 0.5 * sin x + 0.7 * cos y) [2,3]
          , grad (\[x,y] -> log x + x*y - sin y) [2,3]
          , grad (\[x,y] -> 1 / x * y) [2,3]
          , grad (\[x,y] -> x + y + x * y + sin x + sin y + cos x + cos y + sin (x * y) + cos (x * y)) [2,3]
          , grad (\[x,y] -> sin (exp x + y)) [2,3]
          ]

-- autodiff with single occurrences of vars
autoDiffSingle :: [[Double]]
autoDiffSingle = [ grad (\[x,y] -> x * sin y) [2,3]
          , grad (\[x,y] -> sin x + cos y) [2,3]
          , grad (\[x,y] -> 0.5 * sin x + 0.7 * cos y) [2,3]
          , grad (\[x,y,v,w] -> log x + y*v - sin w) [2,3,2,3]
          , grad (\[x,y] -> 1 / x * y) [2,3]
          , grad (\[a,b,c,d,e,f,g,h,i,j,k,l] -> a + b + c * d + sin e + sin f + cos g + cos h + sin (i * j) + cos (k * l)) [2,3,2,3,2,3,2,3,2,3,2,3]
          , grad (\[x,y] -> sin (exp x + y)) [2,3]
          ]

-- xs is empty since we are interested in theta
xs :: V.Vector a
xs = V.empty
-- theta values
thetaMulti, thetaSingle :: V.Vector Double
thetaMulti  = V.fromList [2.0, 3.0]
thetaSingle = V.fromList [2.0, 3.0, 2.0, 3.0, 2.0, 3.0, 2.0, 3.0, 2.0, 3.0, 2.0, 3.0]

-- values from forward mode
forwardVals :: [[Double]]
forwardVals = map (forwardMode xs thetaMulti id) exprs

-- values from grad
-- we must relabel the parameters of the expression to sequence values
gradVals :: [(Double, [Double])]
gradVals = map (forwardModeUnique xs thetaSingle id . relabelParams) exprs

-- values of the evaluated expressions
exprVals :: [Double]
exprVals = map (evalTree xs thetaSingle id . relabelParams) exprs

refGrad :: [(Double, [Double])]
refGrad = zip exprVals autoDiffSingle

testDiff :: (Eq a, Show a) => String -> String -> a -> a -> Test
testDiff lbl name a b = TestLabel lbl $ TestCase (assertEqual name a b)

tests :: Test
tests = TestList $
     zipWith (testDiff "forward mode" "autodiff x forward mode") autoDiffMult forwardVals
  <> zipWith (testDiff "opt. grad. parameters" "(evalTree, autodiff) x gradVals") refGrad gradVals
  <> zipWith (testDiff "deriveByParam" "deriveByParam x autodiff") (map head autoDiffSingle) (map (head.snd) gradVals)

main :: IO ()
main = do
    result <- runTestTT tests
    putStrLn $ showCounts result
