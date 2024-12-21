{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}
{-# LANGUAGE  MultiWayIf #-}
{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE  FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}

module Main where 

import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.Opt
import Control.Monad.State.Strict

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Build
import Algorithm.EqSat.Info
import Algorithm.EqSat.Queries
import Algorithm.EqSat.DB
import Algorithm.EqSat.Simplify

import qualified Data.IntMap as IM
import Data.Massiv.Array as MA hiding (forM_, forM, Continue)
import Data.Maybe (fromJust, isNothing, isJust)
import Data.SRTree
import Data.SRTree.Recursion
import Data.SRTree.Datasets
import Data.SRTree.Eval
import Data.SRTree.Random (randomTree)
import Data.SRTree.Print hiding ( printExpr )
import Options.Applicative as Opt hiding (Const, columns)
import System.Random
import qualified Data.HashSet as Set
import Data.List ( sort, sortOn )
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntMap.Strict as IntMap
import Data.Char ( toLower )
import Debug.Trace
import Algorithm.EqSat (runEqSat)

import System.Console.Repline hiding (Repl)
import Util
import Commands
import Data.List ( isPrefixOf, intercalate, nub )
import Text.Read
import Control.Monad ( forM, when )
import Data.Binary ( encode, decode )
import qualified Data.ByteString.Lazy as BS
import Data.Maybe ( fromMaybe )
import Text.ParseSR (SRAlgs(..), parseSR, parsePat)
import qualified Data.ByteString.Char8 as B
import qualified Data.IntSet as IntSet
import qualified Data.Set as SSet

data Args = Args
  { _dataset      :: String,
    _testData     :: String,
    _distribution :: Distribution,
    _dumpTo       :: String,
    _loadFrom     :: String,
    _calcDL       :: Bool
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
       <> short 't'
       <> value ""
       <> showDefault
       <> help "test data")
  <*> option auto
       ( long "distribution"
       <> value Gaussian
       <> showDefault
       <> help "distribution of the data.")
  <*> strOption
       ( long "dump-to"
       <> value ""
       <> showDefault
       <> help "dump final e-graph to a file."
       )
  <*> strOption
       ( long "load-from"
       <> help "load initial e-graph from a file."
       )
  <*> switch
       ( long "calculate-dl"
       <> help "(re)calculate DL."
       )

runIfRight cmd = case cmd of
                    Left err -> io.print $ "wrong command format."
                    Right c  -> run c

topCmd :: [String] -> Repl ()
topCmd []    = helpCmd ["top"]
topCmd args  = do
  let cmd = parseCmd parseTop (B.pack $ unwords args)
  runIfRight cmd

distCmd :: [String] -> Repl ()
distCmd []   = helpCmd ["distribution"]
distCmd args = do
  let cmd = parseCmd parseDist (B.pack $ unwords args)
  runIfRight cmd

reportCmd :: Distribution -> DataSet -> DataSet -> [String] -> Repl ()
reportCmd _ _ _ [] = helpCmd ["report"]
reportCmd dist trainData testData args =
  case readMaybe @Int (head args) of
    Nothing -> io.putStrLn $ "The id must be an integer."
    Just n  -> run (Report n (dist, trainData, testData))

optimizeCmd :: Distribution -> DataSet -> DataSet -> [String] -> Repl ()
optimizeCmd _ _ _ [] = helpCmd ["optimize"]
optimizeCmd dist trainData testData args =
  case readMaybe @Int (head args) of
    Nothing -> io.putStrLn $ "The id must be an integer."
    Just n  -> do let nIters = if length args > 1 then fromMaybe 100 (readMaybe @Int (args !! 1)) else 100
                  run (Optimize n nIters (dist, trainData, trainData))

subtreesCmd :: [String] -> Repl ()
subtreesCmd [] = helpCmd ["subtrees"]
subtreesCmd (arg:_) = case readMaybe @Int arg of
                        Nothing -> io.putStrLn $ "The argument must be an integer."
                        Just n  -> run (Subtrees n)

insertCmd :: Distribution -> DataSet -> DataSet -> [String] -> Repl ()
insertCmd dist trainData testData [] = helpCmd ["insert"]
insertCmd dist trainData testData args = do
  let etree = parseSR TIR "" False $ B.pack (unwords args)
  case etree of
    Left _     -> io.putStrLn $ "no parse for " <> unwords args
    Right tree -> do ec <- egraph $ fromTree myCost tree
                     run (Optimize ec 100 (dist, trainData, trainData))

paretoCmd :: [String] -> Repl ()
paretoCmd []   = run (Pareto ByFitness)
paretoCmd args = case (Prelude.map toLower $ unwords args) of
                    "by fitness" -> run (Pareto ByFitness )
                    "by dl"      -> run (Pareto ByDL)

countPatCmd :: [String] -> Repl ()
countPatCmd []   = helpCmd ["count-pattern"]
countPatCmd args = run (CountPat (unwords args))

saveCmd :: [String] -> Repl ()
saveCmd [] = helpCmd ["save"]
saveCmd args = run (Save (unwords args))

loadCmd :: [String] -> Repl ()
loadCmd [] = helpCmd ["load"]
loadCmd args = run (Load (unwords args))

commands = ["help", "top", "report", "optimize", "subtrees", "insert", "count-pattern", "distribution", "pareto", "save", "load"]

hlpMap = Map.fromList $ Prelude.zip commands
                            [ "help <cmd>: shows a brief explanation for the command."
                            , "top <n> [size]: displays the top-n expression sorted by fitness. If <size> is provided, then it will retrieve the top-n with that size."
                            , "report <n>: displays a detailed report for the expression with id n."
                            , "optimize <n>: (re)optimize expression with id n."
                            , "subtrees <n>: shows the subtrees for the tree rotted with id <n>."
                            , "insert <expr>: inserts a new tree and evaluates."
                            , "count-pattern <pat> : count the occurrence of the pattern <pat> in the evaluated expressions."
                            , "distribution: shows the distribution of patterns."
                            , "pareto: shows the pareto front."
                            , "save: save current e-graph to a file."
                            , "load: load current e-graph from a file."
                            ]

-- Evaluation
cmd :: Map String ([String] -> Repl ()) -> String -> Repl ()
cmd cmdMap input = do let (cmd':args) = words input
                      case cmdMap Map.!? cmd' of
                        Nothing -> io.putStrLn $ "Command not found!!!"
                        Just f  -> f args

helpCmd :: [String] -> Repl ()
helpCmd []    = io . putStrLn $ "Usage: help <command-name>."
helpCmd (x:_) = case hlpMap Map.!? x of
                  Nothing -> io.putStrLn $ "Command not found!!!"
                  Just hlp -> io.putStrLn $ hlp
-- Completion
comp :: (Monad m, MonadState EGraph m) => WordCompleter m
comp n = pure $ filter (isPrefixOf n) commands

ini :: Repl ()
ini = do (io . putStrLn) "Welcome to Incredible e-graph equation explorer.\nPress Ctrl-D to exit.\nPress <TAB> to see the commands."
         pure ()

final :: Repl ExitDecision
final = do io.print $ "good-bye!"
           return Exit
-- TODO: DL is sorted by min not max as the fitness
main :: IO ()
main = do
  args <- execParser opts
  g <- getStdGen
  dataTrain <- loadTrainingOnly (_dataset args) True
  dataTest  <- if null (_testData args)
                  then pure dataTrain
                  else loadTrainingOnly (_testData args) True
  eg <- decode <$> BS.readFile (_loadFrom args)
  let --alg = evalStateT (repl dataTrain dataVal dataTest args) emptyGraph
      dist = _distribution args
      funs = [ helpCmd
             , topCmd
             , reportCmd dist dataTrain dataTest
             , optimizeCmd dist dataTrain dataTest
             , subtreesCmd
             , insertCmd dist dataTrain dataTest
             , countPatCmd
             , distCmd
             , paretoCmd
             , saveCmd
             , loadCmd
             ]
      cmdMap = Map.fromList $ Prelude.zip commands funs

      repl = evalRepl (const $ pure ">>> ") (cmd cmdMap) [] Nothing Nothing (Word comp) ini final
      crDB = if _calcDL args then (createDB >> fillDL dist dataTrain) else (createDB >> pure ())
  when (_calcDL args) $ putStrLn "Calculating DL..."
  eg' <- execStateT crDB eg
  evalStateT repl eg'


  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )

