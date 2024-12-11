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
import Data.SRTree.Datasets
import Data.SRTree.Eval
import Data.SRTree.Random (randomTree)
import Data.SRTree.Print hiding ( printExpr )
import Options.Applicative as Opt hiding (Const, columns)
import System.Random
import qualified Data.Set as Set
import Data.List ( sort )
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntMap.Strict as IntMap

import Debug.Trace
import Algorithm.EqSat (runEqSat)

import System.Console.Repline hiding (Repl)
import Util
import Data.List ( isPrefixOf, intercalate, nub )
import Text.Read
import Control.Monad ( forM )
import Data.Binary ( encode, decode )
import qualified Data.ByteString.Lazy as BS
import Data.Maybe ( fromMaybe )
import Text.ParseSR (SRAlgs(..), parseSR, parsePat)
import qualified Data.ByteString.Char8 as B

data Args = Args
  { _dataset      :: String,
    _testData     :: String,
    _distribution :: Distribution,
    _dumpTo       :: String,
    _loadFrom     :: String
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



top :: [String] -> Repl ()
top []    = helpCmd ["top"]
top [arg] = case readMaybe @Int arg of
              Nothing -> io.putStrLn $ "The first argument should be an integer."
              Just n  -> do ids <- egraph $ getTopECLassThat n (const True)
                            printSimpleMultiExprs ids
top (arg1:arg2:_) = case (readMaybe @Int arg1, readMaybe @Int arg2) of
                      (Just n, Just sz) -> do ids <- egraph $ getTopECLassWithSize sz n
                                              printSimpleMultiExprs ids
                      (Just n, Nothing) -> top [arg1]
                      _                 -> helpCmd ["top"]



report :: Distribution -> DataSet -> DataSet -> [String] -> Repl ()
report _ _ _ [] = helpCmd ["report"]
report dist trainData testData args =
  case readMaybe @Int (head args) of
    Nothing -> io.putStrLn $ "The id must be an integer."
    Just n  -> do egraph $ printExpr trainData testData dist n

optimize :: Distribution -> DataSet -> DataSet -> [String] -> Repl ()
optimize _ _ _ [] = helpCmd ["optimize"]
optimize dist trainData testData args =
  case readMaybe @Int (head args) of
    Nothing -> io.putStrLn $ "The id must be an integer."
    Just n  -> do let nIters = if length args > 1 then fromMaybe 100 (readMaybe @Int (args !! 1)) else 100
                  t <- egraph $ getBestExpr n
                  (f, theta) <- egraph $ fitnessFunRep nIters dist trainData trainData t
                  egraph $ insertFitness n f theta
                  printSimpleMultiExprs [n]

subtrees :: [String] -> Repl ()
subtrees [] = helpCmd ["subtrees"]
subtrees (arg:_) = case readMaybe @Int arg of
                     Nothing -> io.putStrLn $ "The argument must be an integer."
                     Just n  -> do isValid <- egraph $ gets ((IntMap.member n) . _eClass)
                                   if isValid
                                      then do ids <- egraph $ getAllChildEClasses n
                                              printSimpleMultiExprs ids
                                      else io.putStrLn $ "Invalid id."

insert :: Distribution -> DataSet -> DataSet -> [String] -> Repl ()
insert dist trainData testData [] = helpCmd ["insert"]
insert dist trainData testData args = do
  let etree = parseSR TIR "" False $ B.pack (unwords args)
  case etree of
    Left _ -> io.putStrLn $ "no parse for " <> unwords args
    Right tree -> do ec <- egraph $ fromTree myCost tree
                     optimize dist trainData testData [show ec, "100"]

topPat :: [String] -> Repl ()
topPat []  = helpCmd ["topPat"]
topPat [x] = helpCmd ["topPat"]
topPat (sn:spat) = case readMaybe @Int sn of
                       Nothing -> io.putStrLn $ "The first argument must be an integer."
                       Just n  -> do let etree = parsePat $ B.pack (unwords spat)
                                     case etree of
                                          Left _     -> io.putStrLn $ "no parse for " <> unwords spat
                                          Right pat  -> do mm <- egraph $ match pat
                                                           ecs' <- egraph $ (Prelude.map fromLeft . Prelude.filter isLeft . Prelude.map snd) <$> match pat
                                                           ecs <- egraph $ Prelude.mapM canonical ecs'
                                                           ids <- egraph $ getTopECLassIn n ecs
                                                           printSimpleMultiExprs (nub ids)
  where
    isLeft (Left _)   = True
    isLeft _          = False
    fromLeft (Left x) = x
    fromLeft _        = undefined

commands = ["help", "top", "report", "optimize", "subtrees", "insert", "top-patterns"]

hlpMap = Map.fromList $ Prelude.zip commands
                            [ "help <cmd>: shows a brief explanation for the command."
                            , "top <n> [size]: displays the top-n expression sorted by fitness. If <size> is provided, then it will retrieve the top-n with that size."
                            , "report <n>: displays a detailed report for the expression with id n."
                            , "optimize <n>: (re)optimize expression with id n."
                            , "subtrees <n>: shows the subtrees for the tree rotted with id <n>."
                            , "insert <expr>: inserts a new tree and evaluates."
                            , "top-patterns <n> <pat>: displays the top-n expressions following the pattern <pat>."
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
             , top
             , report dist dataTrain dataTest
             , optimize dist dataTrain dataTest
             , subtrees
             , insert dist dataTrain dataTest
             , topPat
             ]
      cmdMap = Map.fromList $ Prelude.zip commands funs

      repl = evalRepl (const $ pure ">>> ") (cmd cmdMap) [] Nothing Nothing (Word comp) ini final
  eg' <- execStateT createDB eg
  evalStateT repl eg'


  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )

