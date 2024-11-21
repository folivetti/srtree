module Main (main) where

import GP ( HyperParams(HP), fitness, evolution )
import Data.SRTree ( param, var )
import System.Random ( getStdGen )
import Control.Monad.State ( evalStateT )
import Data.SRTree.Datasets ( loadDataset ) 
import Options.Applicative
import Data.Massiv.Array 

-- Data type to store command line arguments
data Args = Args
  { dataset :: String,
    popSize :: Int,
    gens    :: Int,
    pc      :: Double,
    pm      :: Double
  }
  deriving (Show)

-- parser of command line arguments
opt :: Parser Args
opt = Args
   <$> strOption
       ( long "dataset"
       <> short 'd'
       <> metavar "INPUT-FILE"
       <> help "CSV dataset." )
   <*> option auto
       ( long "population"
       <> short 'p'
       <> metavar "POP-SIZE"
       <> showDefault
       <> value 100
       <> help "Population size." )
   <*> option auto
      ( long "generations"
      <> short 'g'
      <> metavar "GENS"
      <> showDefault
      <> value 100
      <> help "Number of generations." )
   <*> option auto
      ( long "probCx"
      <> metavar "PC"
      <> showDefault
      <> value 0.9
      <> help "Crossover probability." )
   <*> option auto
      ( long "probMut"
      <> metavar "PM"
      <> showDefault
      <> value 0.3
      <> help "Mutation probability." )

nonterms = [Right (+), Right (-), Right (*), Right (/), Right (\l r -> abs l ** r), Left (1/)]
--nonterms = [Right (+), Right (-), Right (*)]

main :: IO ()
main = do
  args <- execParser opts
  g <- getStdGen
  ((x, y, _, _), _, _, _) <- loadDataset (dataset args) True
  let hp = HP 2 4 25 (popSize args) 2 (pc args) (pm args) terms nonterms 
      (Sz2 _ nFeats) = size x
      terms = [var ix | ix <- [0 .. nFeats-1]] <> [param ix | ix <- [0 .. 5]]
  pop <- evalStateT (evolution (gens args) hp (fitness x y)) g
  putStrLn "Fin"
  where
    opts = info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )
