{-# LANGUAGE OverloadedStrings #-}

module Main where 

import qualified Data.Massiv.Array as M
import Data.SRTree 
import Data.SRTree.Eval
import Algorithm.SRTree.Opt
import Data.SRTree.Datasets
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.NonlinearOpt 

powabs l r = Fix $ Bin PowerAbs l r
recip' x = Fix $ Uni Recip x 

main = do
    ((x, y, _, _), (mXerr, mYerr, _, _), _, _) <- loadDataset "datasets/RARpre.csv:::gobs:gbar,logX,logY,logXErr,logYErr:e_gobs:e_gbar" True
    ((x1,y1,_, _), _, _, _) <-loadDataset "datasets/nikuradse_2.csv" True
    --let theta = M.fromList M.Seq [1.39e-5, 0.911, 0.0722, 0.0806, -0.503, 0.74]
        -- tree = "x0" - powabs "t0" ("t1" - powabs "x0" "t2") :: Fix SRTree
    let --theta = M.fromList M.Seq [0.018, -0.276, -0.297, 1.752, 0.0806, -0.503, 0.74]
        --theta0 = M.fromList M.Seq [0.02, -0.2, -0.3, 1.8, 0.08, -0.5, 0.7]
        --theta0 = M.fromList M.Seq [1.0, 0.5, -0.08, -0.5, -0.7]
        theta1 = M.fromList M.Seq [0.301, 0.673, -0.253, 0.6] -- [-0.06670815906321582, 1.291358194319714, -2.9665840067763725]
        --tree = Fix $ Uni Recip $ ("t0" + powabs ("t1" + powabs "x0" "t2") "t3")
        --tree = (powabs (("x0") / (("t0") + ("x0"))) "t1") + "x0"
        tree1 = "t0" / (recip' ("t1" + "x0") - powabs "t2" "x0")
        --(t, f, n) = minimizeNLL ROXY mXerr mYerr 30 x y tree theta0
        (t1, f1, n1) = minimizeNLL' LBFGS Gaussian Nothing Nothing 10000 x1 y1 tree1 theta1 
    --print $ nll ROXY mXerr mYerr x y tree theta0
    --print $ (0.5*) $ M.sum $ evalTree x theta0 (nllROXY tree)
    --print (t, f, n)
    print $ nll Gaussian Nothing Nothing x1 y1 tree1 theta1 
    print (t1, f1, n1)
    print $ mse x1 y1 tree1 t1

