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

xs = fromList [1.0, 2.0]
ps = fromList [0.1, 0.2 .. 30.0]

params = P [0,1] (-1.0, 1.0) (-2, 2) [Id ..]

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
main :: IO ()
main = defaultMain [
       bgroup "unbalanced"
         [ bench "forwardMode" $ nfIO (benchTree runRnd forwardMode)
         , bench "grad" $ nfIO (benchTree runRnd gradParams)
         , bench "autodiff" $ nfIO (benchAutodiff runRnd)
         ] ,
       bgroup "balanced"
         [ bench "forwardMode" $ nfIO (benchTree runRndBalance forwardMode)
         , bench "grad" $ nfIO (benchTree runRndBalance gradParams)
         , bench "autodiff" $ nfIO (benchAutodiff runRndBalance)
         ]
                   ]
