module Main where

import Data.SRTree
import Data.SRTree.Print
import Data.SRTree.Random
import Data.SRTree.Recursion hiding (fromList)
import Data.Vector (fromList, toList)
import System.Random
import Control.Monad.Reader
import Control.Monad.State
import Criterion.Main
import Numeric.AD.Double ( grad )

autograd t = grad (cata alg t)
  where
      alg (Var ix) = const 0
      alg (Param ix) = \xs -> xs !! ix
      alg (Const v) = const 1.0
      alg (Bin op l r) = \xs -> evalOp op (l xs) (r xs)
      alg (Uni f t) = \xs -> evalFun f (t xs)

xs = fromList [1.0, 2.0 .. 3000.0]
ps = fromList [0.1, 0.2 .. 110.0]

params = P [0,1] (-1.0, 1.0) (-2, 2) [Id] -- , Sin, Cos, Log, Exp]

runRnd g ns p = flip evalStateT g $ traverse (\n -> runReaderT (randomTree n) p) ns
runRndBalance g ns p = flip evalStateT g $ traverse (\n -> runReaderT (randomTreeBalanced n) p) ns

lens :: [Int]
lens = replicate 100 10 <> replicate 100 100 <> replicate 100 1000

g = mkStdGen 42

benchTree f h = do ts <- f g lens params
                   pure $ map (h xs ps id . relabelParams . fst . constsToParam) ts

benchAutodiff f = do ts <- f g lens params
                     let ps' = Data.Vector.toList ps
                     pure $ map ((`autograd` ps') . relabelParams . fst . constsToParam) ts
{-
main :: IO ()
main = defaultMain [
       bgroup "unbalanced"
         [ -- bench "forwardMode" $ nfIO (benchTree runRnd forwardMode)
          bench "grad" $ nfIO (benchTree runRnd gradParams)
         , bench "grad2" $ nfIO (benchTree runRnd gradParams2)
         , bench "autodiff" $ nfIO (benchAutodiff runRnd)
         ] ,
       bgroup "balanced"
         [ -- bench "forwardMode" $ nfIO (benchTree runRndBalance forwardMode)
          bench "grad" $ nfIO (benchTree runRndBalance gradParams)
         , bench "grad2" $ nfIO (benchTree runRndBalance gradParams2)
         , bench "autodiff" $ nfIO (benchAutodiff runRndBalance)
         ]
                   ]
-}

mkPySRTree :: Int -> Int -> Fix SRTree
mkPySRTree nvar np = relabelParams $ sum [mkWith ix | ix <- [0 .. nvar-1]]
  where
    mkWith ix = fst . (!!(np-1)) $ iterate (\(t, i) -> (cos (t + param i), i+1)) $ (cos (var ix + param 0), 1)

genBalancedTree :: Int -> Fix SRTree
genBalancedTree = relabelParams . go
  where
    go 0 = var 0
    go 1 = cos (var 0 + param 0)
    go n | even n = go (n `div` 2) * (param 0 + go (n `div` 2 - 1))
         | odd n  = cos (param 0 + go (n-1))

sizes = (,) <$> [1] <*> [10, 20 .. 1000]
--sizes = (,) <$> [1] <*> [500, 600 .. 2000]
--tests = map (\(ix, iy) -> (ix, iy, mkPySRTree ix iy)) sizes
tests = map (\(ix, iy) -> (ix, iy, genBalancedTree iy)) sizes

main :: IO ()
main = defaultMain [
       bgroup ("PySR " <> show ix <> " " <> show iy)
         [ bench "warmup" $ whnf (evalTree xs ps id) t
         -- , bench "forwardMode" $ whnf (sum . forwardMode xs ps id) t
         , bench "grad" $ whnf (sum . snd . gradParams xs ps id) t
         , bench "grad2" $ whnf (sum . snd . gradParams2 xs ps id) t
         , bench "autodiff" $ whnf (sum . (`autograd` (Data.Vector.toList ps))) t
         ] | (ix, iy, t) <- tests
                   ]

{-
comp (x, xs) (y, ys) = ((x + sum xs) - (y + sum ys))^2

main :: IO ()
main = do 
    let g = mkStdGen 42
    trees <- runRndBalance g lens params
    mapM_ (\(t,a,b) -> print (showExpr t, a, b, comp a b)) $ filter (\(t,a,b) -> let c = comp a b in not (isNaN c) && c >= 1e-20) [(t, gradParams xs ps id t, gradParams2 xs ps id t) | t' <- trees, let t = relabelParams (fst $ constsToParam t')] 
-}
