import Data.SRTree
import Data.SRTree.Random
import Data.SRTree.Print

import System.Random
import Control.Monad.State
import Control.Monad.Reader

runThing g n = flip evalStateT g . runReaderT (randomTree n)

main :: IO ()
main = do
  g <- getStdGen
  t <- runThing g 10 $ P [0,1] (-1.0, 1.0) (-3, 3) [Id, Sin]
  print (t :: SRTree Int Double)
  putStrLn $ showDefault t
  putStrLn $ showTikz t
