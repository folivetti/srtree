module Main (main) where

import GP
import Data.SRTree
import Data.SRTree.Print 
import System.Random
import Control.Monad.State
import Data.SRTree.Datasets 

terms = [var 0, param 0]
nonterms = [Right (+), Right (-), Right (*), Right (/), Right (\l r -> abs l ** r), Left (1/)]
--nonterms = [Right (+), Right (-), Right (*)]

--terms = [VarT 0, ParamT]
--nonterms = [Right AddT, Right SubT, Right MulT, Right DivT, Right PowT, Left InvT]
main :: IO ()
main = do g <- getStdGen 
          ((x, y, _, _), _) <- loadDataset "nikuradse_2.csv" True
          let hp = HP 2 4 10 200 2 0.3 0.25 terms nonterms
          pop <- evalStateT (evolution 500 hp (fitness x y)) g
          --print (fmap _fit pop)
          putStrLn "Fin"
