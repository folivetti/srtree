module Main (main) where

import GP ( HyperParams(HP), fitness, evolution, printFinal )
import Data.SRTree
import System.Random ( getStdGen )
import Control.Monad.State ( evalStateT )
import Data.SRTree.Datasets ( loadDataset ) 
import Options.Applicative
import Data.Massiv.Array 
import Util

-- Data type to store command line arguments
data Args = Args
  { dataset   :: String,
    _testData :: String,
    popSize   :: Int,
    gens      :: Int,
    _maxSize  :: Int,
    pc        :: Double,
    pm        :: Double,
    _nonterminals :: String,
    _nTournament  :: Int
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
   <*> strOption
       ( long "test"
       <> value ""
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
      ( long "max-size"
      <> metavar "SIZE"
      <> showDefault
      <> value 20
      <> help "maximum expression size." )
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
   <*> strOption
       ( long "non-terminals"
       <> value "Add,Sub,Mul,Div,PowerAbs,Recip"
       <> showDefault
       <> help "set of non-terminals to use in the search."
       )
   <*> option auto
       ( long "tournament-size"
       <> value 2
       <> showDefault
       <> help "tournament size."
       )

nonterms = [Right (+), Right (-), Right (*), Right (/), Right (\l r -> Fix $ Bin PowerAbs l r), Left recip, Left log, Left exp, Left (\t -> Fix $ Uni SqrtAbs t)]

main :: IO ()
main = do
  args <- execParser opts
  g <- getStdGen
  (x, y, _) <- loadTrainingOnly (dataset args) True
  (x_test, y_test, _) <- loadTrainingOnly (_testData args) True
  let hp = HP 3 10 (_maxSize args) (popSize args) (_nTournament args) (pc args) (pm args) terms (parseNonTerms $ _nonterminals args)
      (Sz2 _ nFeats) = size x
      terms = [var ix | ix <- [0 .. nFeats-1]] <> [param ix | ix <- [0 .. 5]]
  best <- evalStateT (evolution (gens args) hp (fitness x y)) g
  printFinal best x y x_test y_test
  where
    opts = info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )
