import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Derivative
import Data.SRTree.Datasets
import Algorithm.SRTree.AD

import qualified Data.Vector as V
import Numeric.AD.Double ( grad )
import Test.HUnit 
import qualified Data.Massiv.Array as M
import Data.Massiv.Array (D, S, Ix1, Ix2, Comp(..), Sz(..))
import qualified Foreign as M

-- test expressions
exprs = [
    param 0 * sin ( param 1)
  , sin (param 0) + cos (param 1)
  , 0.5 * sin (param 0) + 0.7 * cos (param 1)
  , log (param 0) + param 0 * param 1 - sin (param 1)
  , 1 / param 0 * param 1
  , param 0 + param 1 + param 0 * param 1 + sin (param 0) + sin (param 1) + cos (param 0) + cos (param 1) + sin (param 0 * param 1) + cos (param 0 * param 1)
  , sin (exp (param 0) + param 1)
  , param 0 / param 1
  , param 0 ** param 1
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
          , grad (\[x,y] -> x/y) [2,3]
          , grad (\[x,y] -> x ** y) [2,3]
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
          , grad (\[x,y] -> x/y) [2,3]
          , grad (\[x,y] -> x ** y) [2,3]
          ]

-- xs is empty since we are interested in theta
xs :: M.Array S Ix2 Double
xs = M.singleton 0

xs' :: M.Array S Ix2 Double 
xs' = M.singleton 0 

err = M.singleton 1

-- theta values
thetaMulti, thetaSingle :: M.Array S Ix1 Double
thetaMulti  = M.fromList Seq [2.0, 3.0]
thetaSingle = M.fromList Seq [2.0, 3.0, 2.0, 3.0, 2.0, 3.0, 2.0, 3.0, 2.0, 3.0, 2.0, 3.0]

-- values from forward mode
-- forwardVals :: [[Double]]
forwardVals = map (M.toList . snd . forwardMode xs' thetaMulti err) exprs

-- values from grad
-- we must relabel the parameters of the expression to sequence values
--gradVals :: [(Double, [Double])]
gradVals = map (M.toList . snd . forwardModeUnique xs' thetaSingle err . relabelParams) exprs
gradVals' = map (M.toList . snd . reverseModeUnique xs' thetaSingle err . relabelParams) exprs

-- values of the evaluated expressions
--exprVals :: [Double]
exprVals = map (evalTree xs' thetaSingle . relabelParams) exprs

--refGrad :: [(Double, [Double])]
refGrad = zip exprVals autoDiffSingle

testDiff :: (Eq a, Show a) => String -> String -> a -> a -> Test
testDiff lbl name a b = TestLabel lbl $ TestCase (assertEqual name a b)

tests :: Test
tests = TestList $
     zipWith (testDiff "forward mode" "autodiff x forward mode") autoDiffMult forwardVals
  <> zipWith (testDiff "forward mode" "autodiff x forward mode unique") autoDiffSingle gradVals
  <> zipWith (testDiff "reverse mode" "autodiff x reverse mode unique") autoDiffSingle gradVals'

main :: IO ()
main = do
    result <- runTestTT tests
    putStrLn $ showCounts result
    --ds <- loadDataset "test/wine.csv:3:10:alcohol:liver,deaths,heart" True
    --print ds
