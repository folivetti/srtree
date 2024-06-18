module Main (main) where

import Options.Applicative
import Text.ParseSR.IO ( withInput )
import System.Random ( getStdGen, mkStdGen )

import Args
import IO
import Report

main :: IO ()
main = do
  args             <- execParser opts
  g                <- getStdGen
  (dset, varnames) <- getDataset args
  let seed = if rseed args < 0 
               then g 
               else mkStdGen (rseed args)
  withInput (infile args) (from args) varnames False (simpl args)
    >>= if toScreen args
          then printResultsScreen args seed dset  -- full report on screne
          else printResults args seed dset -- csv file
  where    
    opts = info (opt <**> helper)
            ( fullDesc <> progDesc "Optimize the parameters of\
                                   \ Symbolic Regression expressions."
           <> header "srtree-opt - a CLI tool to (re)optimize the numeric\
                     \ parameters of symbolic regression expressions"
            )
