{-# LANGUAGE OverloadedStrings #-}

module Main where 

import qualified Data.Massiv.Array as M
import Data.SRTree 
import Algorithm.SRTree.Opt
import Data.SRTree.Datasets
import Algorithm.SRTree.Likelihoods

powabs l r = Fix $ Bin PowerAbs l r 

main = do
    ((x, y, _, _), (mXerr, mYerr, _, _), _, _) <- loadDataset "datasets/RAR.csv:::gobs:gbar:e_gobs:e_gbar" True
    --let theta = M.fromList M.Seq [1.39e-5, 0.911, 0.0722, 0.0806, -0.503, 0.74]
        -- tree = "x0" - powabs "t0" ("t1" - powabs "x0" "t2") :: Fix SRTree
    let theta = M.fromList M.Seq [0.018, -0.276, -0.297, 1.752, 0.0806, -0.503, 0.74]
        theta0 = M.fromList M.Seq [0.02, -0.2, -0.3, 1.8, 0.08, -0.5, 0.7]
        tree = Fix $ Uni Recip $ ("t0" + powabs ("t1" + powabs "x0" "t2") "t3")
        (t, f, n) = minimizeNLL ROXY mXerr mYerr 10 x y tree theta0
    print $ nll ROXY mXerr mYerr x y tree theta
    print (t, f, n)

