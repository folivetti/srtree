module Main where

import Data.SRTree 
import Data.SRTree.EqSat1 
import Data.SRTree.Print 
import qualified Data.Map as Map
import qualified Data.IntMap as IM
import Control.Monad.State.Lazy

main :: IO ()
main = do 
    let t1 = var 0 + 12.0
        t2 = 3.2 * var 0
        t3 = 3.2 * var 0 / (var 0 + 12.0)
        t4 = var 0 + sin (var 0)
        (v, eg) = fromTrees [t3,t1,t2,t4]
        roots = findRootClasses eg
        ecId = _eNodeToEClass eg Map.! (Var 0)
        eg' = (updateConsts >> calculateHeights) `execState` eg
    putStr "Parents of x0: "
    print $ _parents $ _eClass eg IM.! ecId    
    putStrLn "\nexpressions from root: "
    mapM_ (putStrLn . showExpr . getExpressionFrom eg) roots
    putStrLn "\nexpressions from each e-class: "
    mapM_ (putStrLn . showExpr . getExpressionFrom eg) (IM.keys $ _eClass eg)
    mapM_ (print . _height . _info) (IM.elems $ _eClass eg')
