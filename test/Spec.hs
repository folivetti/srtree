import Test.HUnit
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Storable as VS
import Data.SRTree.Internal
import Data.SRTree.Recursion (Fix)
import Data.SRTree.Eval (compile)
import Algorithm.SRTree.AD.Unboxed (CompiledTree, compileTree, compileTreeMulti, evalGrad, evalGradVec, evalGradMulti)
import qualified EqSatTests
import Data.SRTree.Random (randomTree, tossBiased, randomFrom)
import System.Random (mkStdGen)
import Control.Monad.State.Strict (evalStateT)
import Data.SRTree.Datasets (loadDataset)
import Control.Monad (forM_)

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

test_benchgrad :: Test
test_benchgrad = TestCase $ do
  let genTerm    = do coin <- tossBiased 0.4
                      if coin then randomFrom [Fix $ Var ix | ix <- [0..8]] else randomFrom [Fix $ Param ix | ix <- [0..9]]
      genNonTerm = randomFrom [Bin Add () (), Bin Sub () (), Bin Mul () (), Uni LogAbs (), Uni SqrtAbs ()]
      genMultipleTrees 0 = pure []
      genMultipleTrees n = do
          t  <- randomTree 5 10 150 genTerm genNonTerm False
          ts <- genMultipleTrees (n-1)
          pure (t:ts)
      g = mkStdGen 42
  trees' <- evalStateT (genMultipleTrees 5) g
  ((dataset, y, _, _), _, _, _) <- loadDataset "data.tsv" True
  let thetaU = VU.fromList [1.0, 0.5, 0.2, 0.3, 0.1, 0.5, 0.9, 0.3, 0.2, 0.4]
      thetaS = VS.convert thetaU
      trees  = map relabelParamsOrder $ filter (\t -> let v = VU.sum (compile dataset t thetaU) in not (isInfinite v || isNaN v)) trees'
      h = 1e-6
      gfd :: CompiledTree -> VS.Vector Double
      gfd ct = VS.generate (VS.length thetaS) $ \i ->
          let e = VS.fromList (map (\j -> if j == i then h else 0) [0 .. VS.length thetaS - 1])
              (fp, _) = evalGradVec ct (VS.zipWith (+) thetaS e)
              (fm, _) = evalGradVec ct (VS.zipWith (-) thetaS e)
          in (fp - fm) / (2 * h)
  forM_ (zip [0..] trees) $ \(i, t) -> do
      let ct = compileTree dataset y Nothing t
          cts = compileTreeMulti dataset y Nothing t
          (f1, g1) = evalGradVec ct thetaS
          (f0, g0) = evalGrad ct thetaS
          (f2, g2) = evalGradMulti cts thetaS
          fd = gfd ct
      putStrLn ("benchgrad tree " ++ show i ++ " obj=" ++ show f1)
      assertBool ("tree " ++ show i ++ " evalGradVec objective != evalGrad") (abs (f1 - f0) < 1e-6 * max 1 (abs f0))
      assertBool ("tree " ++ show i ++ " evalGradMulti objective != evalGrad") (abs (f2 - f0) < 1e-6 * max 1 (abs f0))
      assertBool ("tree " ++ show i ++ " evalGradVec gradient mismatch") (and (zipWith (\a b -> abs (a - b) < 1e-3 * max 1 (abs a)) (VS.toList g1) (VS.toList fd)))
      assertBool ("tree " ++ show i ++ " evalGrad gradient mismatch") (and (zipWith (\a b -> abs (a - b) < 1e-3 * max 1 (abs a)) (VS.toList g0) (VS.toList fd)))
      assertBool ("tree " ++ show i ++ " evalGradMulti gradient != evalGrad") (and (zipWith (\a b -> abs (a - b) < 1e-9 * max 1 (abs a)) (VS.toList g0) (VS.toList g2)))

main :: IO ()
main = do
  let t1 = TestLabel "compile" test_compile
      t2 = TestLabel "grad" test_grad

  counts <- runTestTT $ TestList
    [ t1
    , t2
    , TestLabel "benchgrad" test_benchgrad
    , TestLabel "eqsat" EqSatTests.tests
    ]
  if failures counts /= 0 || errors counts /= 0
    then error "Some tests failed"
    else pure ()
