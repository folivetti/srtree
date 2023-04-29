module Main where

import Data.SRTree
import Data.SRTree.Print
import Data.SRTree.Random
import Data.SRTree.Recursion hiding (fromList)
import Data.Vector (fromList)
import System.Random
import Control.Monad.Reader
import Control.Monad.State
import Criterion.Main

t = 1 + var 0 * (3.1 + param 0 * var 1 + var 0 * param 1) - var 0

xs = fromList [1.0, 2.0]
ps = fromList [0.5, 0.3]

params = P [0,1] (-1.0, 1.0) (-2, 2) [Id ..]  

runRnd g ns p = flip evalStateT g $ traverse (\n -> runReaderT (randomTree n) p) ns
runRndBalance g ns p = flip evalStateT g $ traverse (\n -> runReaderT (randomTreeBalanced n) p) ns

lens :: [Int]
lens = replicate 100 10 <> replicate 100 100 <> replicate 100 1000

g = mkStdGen 42

benchTree f h = do ts <- f g lens params
                   pure $ map (h xs ps id) ts

main :: IO ()
main = defaultMain [
       bgroup "unbalanced" 
         [ bench "forwardMode" $ nfIO (benchTree runRnd forwardMode)
         , bench "grad" $ nfIO (benchTree runRnd gradParams)
         ] ,
       bgroup "balanced" 
         [ bench "forwardMode" $ nfIO (benchTree runRndBalance forwardMode)
         , bench "grad" $ nfIO (benchTree runRndBalance gradParams)
         ] 
                   ]
