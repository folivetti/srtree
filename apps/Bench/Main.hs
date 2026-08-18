{-# LANGUAGE BangPatterns #-}

import Criterion.Main
import Control.DeepSeq (force, NFData)
import Control.Exception (evaluate)
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector as VB
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Storable as VS

import Data.SRTree
import Data.SRTree.Print
import Data.SRTree.Datasets
import Data.SRTree.Eval
import Data.SRTree.Random
import System.Random
import Control.Monad.State.Strict
import Algorithm.SRTree.NonlinearOpt
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.AD

-- Assuming these are exported by your project modules:
-- import SRTree
-- import Compiler
-- import DatasetLoader

-- Mock signatures based on your provided functions
-- randomTree :: Int -> Int -> Int -> IO Term -> IO NonTerm -> Bool -> IO Tree
-- loadDataset :: FilePath -> Bool -> IO [V.Vector Double]
-- evalTree :: Tree -> [V.Vector Double] -> V.Vector Double
-- compile :: [V.Vector Double] -> Tree -> (Theta -> V.Vector Double)

genTerm    = do coin <- tossBiased 0.4
                if coin then randomFrom [Fix $ Var ix | ix <- [0..8]] else randomFrom [Fix $ Param ix | ix <- [0..9]]
genNonTerm = randomFrom [Bin Add () (), Bin Sub () (), Bin Mul () (), Uni LogAbs (), Uni SqrtAbs ()]

genMultipleTrees 0 = pure []
genMultipleTrees n = do
    t <- randomTree 5 10 150 genTerm genNonTerm False
    ts <- genMultipleTrees (n-1)
    pure (t:ts)

getF (_, x, _) = x
{-# INLINE getF #-}
getT (t, _, _) = t
{-# INLINE getT #-}

main :: IO ()
main = do
    -- 1. Initialization: Load the dataset
    putStrLn "Loading dataset..."
    ((dataset, y, _, _), _, _, _) <- loadDataset "data.tsv" True

    -- 2. Initialization: Generate the random expression tree
    putStrLn "Generating random tree..."
    -- Replace 'genTerm' and 'genNonTerm' with your actual generators
    --g <- getStdGen
    let g = mkStdGen 42
    -- tree <- evalStateT (randomTree 7 10 150 genTerm genNonTerm True) g
    trees' <- evalStateT (genMultipleTrees 5) g
    -- let trees' = [Fix (Uni LogAbs (Fix (Bin PowerAbs (param 0) (param 1 * var 0))))] :: [Fix SRTree]

    -- IMPORTANT: Force deep evaluation of the tree and dataset.
    -- If we do not do this, GHC's lazy evaluation will cause the benchmark
    -- to measure the time it takes to parse the CSV and build the tree in memory!
    -- _ <- evaluate (force tree)
    _ <- evaluate (force dataset)


    -- 3. Initialization: Pre-compile the tree
    -- We evaluate this strictly (!) so the one-time compilation cost
    -- is not included in the runtime benchmark.
    putStrLn "Compiling tree..."
    let !compiledFn = [compile dataset tree | tree <- trees]
        evalTree x th t = compile x t th
        -- Mock theta (parameter vector) to pass into the closures
        !theta = V.fromList [1.0, 0.5, 0.2, 0.3, 0.1, 0.5, 0.9, 0.3, 0.2, 0.4]
        !theta1 = V.fromList [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
        trees = map relabelParamsOrder $ filter (\t -> let v = V.sum (evalTree dataset theta t) in not (isInfinite v || isNaN v)) trees'
        naiveEval = evalTree dataset theta
        dataset' = map G.convert dataset
        y' = G.convert y
        theta1' = G.convert theta1

    _ <- evaluate (force theta)
    _ <- evaluate (force theta1)
    print $ sum $ map (\t ->  V.sum $ naiveEval t) trees
    print $ sum $ map (\t ->  V.sum $ t theta) compiledFn
    print $ sum $ map (\t -> getF $ minimizeNLL MultiThread MSE Nothing 0 dataset y t theta1) trees
    --print $ sum $ map (\t -> getF $ minimizeNLLCompiled MSE Nothing 0 dataset y t theta1) trees

    --print $ sum $ map (\t -> VS.sum . snd $ gradNLLGraph MSE dataset' y' Nothing t theta1') trees
    --print $ sum $ map (\t -> VS.sum . snd $ gradNLLGraphO MSE dataset' y' Nothing t theta1') trees
    --print $ sum $ map (\t -> VS.sum . snd $ compileGrad dataset' y' Nothing t 100 theta1') trees
    --print $ sum $ map (\ct -> V.sum $ ct theta) compiledFn
    --print $ sum $ map (\ct -> V.sum $ executeVM ct rowDataset theta) bytecodes
    -- print $ V.sum $ evalTree dataset theta tree
    -- print $ V.sum $ compiledFn theta

    putStrLn "Running benchmarks..."

    -- 4. The Benchmarks
    defaultMain [
          bgroup "Tree Evaluation (Fixed Dataset)" [

           -- The slow version: dynamically traversing the AST at runtime
           bench "evalTree (Naive AST Traversal)" $
                nf (\ts -> sum [V.sum $ evalTree dataset theta1 t | t <- ts]) trees,


            -- The fast version: executing the pre-compiled, stream-fused closure
            bench "compile (Compiled Closure)" $
                nf (\t -> sum [V.sum (ct t) | ct <- compiledFn]) theta1,

            -- The fast version: executing the pre-compiled, stream-fused closure
            bench "minimizeNLLCompiled (Compiled Closure)" $
                nf (\ts -> sum [V.sum . getT $ minimizeNLL MultiThread MSE Nothing 100 dataset' y' t theta1' | t <- ts]) trees

            --bench "minimizeNLLO (Naive optimized AST Traversal)" $
            --    nf (\ts -> sum [V.sum . getT $ minimizeNLLO MSE Nothing 100 dataset y t theta1 | t <- ts]) trees

            -- The slow version: dynamically traversing the AST at runtime
            --bench "minimizeNLL (Naive AST Traversal)" $
            --    nf (\ts -> sum [V.sum . getT $ minimizeNLL (NLL MSE) Nothing 100 dataset y t theta1 | t <- ts]) trees

        ]
      ]
