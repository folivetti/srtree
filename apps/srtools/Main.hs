module Main (main) where

import Data.ByteString.Char8 ( pack, unpack, split )
import Options.Applicative
import System.Random ( getStdGen, mkStdGen )
import Text.ParseSR.IO ( withInput )

import Args
import IO
import Report

main :: IO ()
main = do
  args             <- execParser opts
  g                <- getStdGen
  (dset, varnames, tgname) <- getDataset args
  let seed = if rseed args < 0 
               then g 
               else mkStdGen (rseed args)
      varnames' = map unpack $ split ',' $ pack varnames
  withInput (infile args) (from args) varnames False (simpl args)
    >>= if toScreen args
          then printResultsScreen args seed dset varnames' tgname  -- full report on screne
          else printResults args seed dset varnames' -- csv file
  where    
    opts = info (opt <**> helper)
            ( fullDesc <> progDesc "Optimize the parameters of\
                                   \ Symbolic Regression expressions."
           <> header "srtools - a CLI tool to (re)optimize the numeric\
                     \ parameters of symbolic regression expressions"
            )
