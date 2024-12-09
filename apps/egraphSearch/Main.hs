{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}
{-# LANGUAGE  MultiWayIf #-}
{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE  BangPatterns #-}
{-# LANGUAGE  TypeSynonymInstances, FlexibleInstances #-}

module Main where 

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Simplify
import Algorithm.EqSat.Build
import Algorithm.EqSat.Queries
import Algorithm.EqSat.Info
import Algorithm.EqSat.DB
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.ModelSelection
import Control.Monad ( forM_, forM, when )
import Control.Monad.State.Strict
import qualified Data.IntMap.Strict as IM
import Data.Massiv.Array as MA hiding (forM_, forM)
import Data.Maybe ( fromJust, isNothing )
import Data.SRTree
import Data.SRTree.Print ( showExpr )
import Options.Applicative as Opt hiding (Const)
import Random
import System.Random
import Data.List ( intercalate )
import qualified Data.IntSet as IntSet
import Algorithm.EqSat (runEqSat)

import Debug.Trace

import Util

data Alg = OnlyRandom | BestFirst deriving (Show, Read, Eq)

egraphSearch :: DataSet -> DataSet -> DataSet -> Args -> StateT EGraph (StateT StdGen IO) ()
-- terms nEvals maxSize printPareto printTrace slowIter slowRep =
egraphSearch dataTrain dataVal dataTest args = do
  ecFst <- insertRndExpr (_maxSize args) rndTerm rndNonTerm2
  --ecFst <- insertBestExpr -- use only to debug
  updateIfNothing fitFun ecFst
  insertTerms
  evaluateUnevaluated fitFun
  runEqSat myCost rewritesParams 1
  cleanDB
  nCls <- gets (IM.size . _eClass)
  nUnev <- gets (IntSet.size . _unevaluated . _eDB)
  let nEvs = nCls - nUnev

  while ((<(_gens args)) . snd) (10, nEvs) $
    \(radius, nEvs) ->
      do
       nCls  <- gets (IM.size . _eClass)
       --nUnev <- gets (IntSet.size . _unevaluated . _eDB)
       --let nEvs = nCls - nUnev -- WARNING: see if it affects results

       ecN <- case (_alg args) of
                    OnlyRandom -> do let ratio = fromIntegral nEvs / fromIntegral nCls
                                     b <- rnd (tossBiased ratio)
                                     ec <- if b && ratio > 0.99
                                              then insertRndExpr (_maxSize args) rndTerm rndNonTerm2 >>= canonical
                                              else do mEc <- pickRndSubTree -- evaluateRndUnevaluated fitFun >>= canonical
                                                      case mEc of
                                                           Nothing ->insertRndExpr (_maxSize args) rndTerm rndNonTerm2 >>= canonical
                                                           Just ec' -> pure ec'
                                     pure ec
                    BestFirst  -> do
                      ecsPareto <- getParetoEcsUpTo 50 (_maxSize args)
                      ecPareto     <- combineFrom ecsPareto >>= canonical
                      curFitPareto <- getFitness ecPareto

                      if isNothing curFitPareto
                        then pure ecPareto
                        else do ecsBest    <- getTopECLassThat 100 (isSizeOf (<(_maxSize args)))
                                ecBest     <- combineFrom ecsBest >>= canonical
                                curFitBest <- getFitness ecBest
                                if isNothing curFitBest
                                  then pure ecBest
                                  else do ee <- pickRndSubTree
                                          case ee of
                                            Nothing -> insertRndExpr (_maxSize args) rndTerm rndNonTerm2 >>= canonical
                                            Just c  -> pure c

       -- when upd $
       ecN' <- canonical ecN
       upd <- updateIfNothing fitFun ecN'
       when upd $ runEqSat myCost rewritesParams 1 >> cleanDB


       when (upd && (_trace args))
         do
            ecN'' <- canonical ecN'
            _tree <- getBestExpr ecN''
            fi <- negate . fromJust <$> getFitness ecN''
            theta <- fromJust <$> getTheta ecN''
            let thetaStr   = intercalate ";" $ Prelude.map show (MA.toList theta)
            io . putStrLn $ showExpr _tree <> "," <> thetaStr <> "," <> show fi
            pure ()
       let radius' = if (not upd) then (max 10 $ min (500 `div` (_maxSize args)) (radius+1)) else (max 10 $ radius-1)
           nEvs'    = nEvs + if upd then 1 else 0
       pure (radius', nEvs')
  io $ putStrLn csvHeader
  if (_printPareto args)
    then paretoFront (_maxSize args) printExpr
    else printBest printExpr

  where
    fitFun = fitnessFunRep (_optRepeat args) (_optIter args) (_distribution args) dataTrain dataVal

    combineFrom [] = pure 0 -- this is the first terminal and it will always be already evaluated
    combineFrom ecs = do
        nt  <- rnd rndNonTerm
        p1  <- rnd (randomFrom ecs)
        p2  <- rnd (randomFrom ecs)
        l1  <- rnd (randomFrom [2..(_maxSize args)-2]) -- sz 10: [2..8]

        e1  <- randomChildFrom p1 l1 >>= canonical
        ml  <- gets (_size . _info . (IM.! e1) . _eClass)
        l2  <- rnd (randomFrom [1..((_maxSize args) - ml - 1)]) -- maxSize - maxSize + 2 - 2= 0 -- sz 10: [1..7] (2) / [1..1] (8)
        e2  <- randomChildFrom p2 l2 >>= canonical
        case nt of
          Uni Id ()    -> canonical e1
          Uni f ()     -> add myCost (Uni f e1) >>= canonical
          Bin op () () -> do b <- rnd toss
                             if b
                              then add myCost (Bin op e1 e2) >>= canonical
                              else add myCost (Bin op e2 e1) >>= canonical
          _            -> canonical e1 -- it is a terminal, should it happen?

    randomChildFrom ec' maxL = do
      p <- rnd toss -- whether to go deeper or return this level
      ec <- canonical ec'
      l <- gets (_size . _info . (IM.! ec) . _eClass )

      if p || l > maxL
          then do --enodes <- gets (_eNodes . (IM.! ec) . _eClass)
                  enode  <- gets (_best . _info . (IM.! ec) . _eClass) -- we should return the best otherwise we may build larger exprs
                  case enode of
                      Uni _ eci     -> randomChildFrom eci maxL
                      Bin _ ecl ecr -> do coin <- rnd toss
                                          if coin
                                            then randomChildFrom ecl maxL
                                            else randomChildFrom ecr maxL
                      _ -> pure ec -- this shouldn't happen unless maxL==0
          else pure ec

    nonTerms   = parseNonTerms (_nonterminals args)
    --[ Bin Add () (), Bin Sub () (), Bin Mul () (), Bin Div () (), Bin PowerAbs () (),  Uni Recip ()]
    (Sz2 _ nFeats) = MA.size (getX dataTrain)
    terms          = if _distribution args == ROXY
                          then [var 0, param 0]
                          else [var ix | ix <- [0 .. nFeats-1]] <> [param 0]

    rndTerm    = Random.randomFrom terms
    rndNonTerm = Random.randomFrom $ (Uni Id ()) : nonTerms
    rndNonTerm2 = Random.randomFrom nonTerms

    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical

    printExpr :: Int -> EClassId -> RndEGraph ()
    printExpr ix ec = do 
        theta <- gets (fromJust . _theta . _info . (IM.! ec) . _eClass)
        bestExpr <- getBestExpr ec
        let (x, y, mYErr) = dataTrain
            (x_val, y_val, mYErr_val) = dataVal
            (x_te, y_te, mYErr_te) = dataTest
            distribution = _distribution args
            best'     = relabelParams bestExpr
            expr      = paramsToConst (MA.toList theta) best'
            mse_train = mse x y best' theta
            mse_val   = mse x_val y_val best' theta
            mse_te    = mse x_te y_te best' theta
            r2_train  = r2 x y best' theta
            r2_val    = r2 x_val y_val best' theta
            r2_te     = r2 x_te y_te best' theta
            nll_train  = nll distribution mYErr x y best' theta
            nll_val    = nll distribution mYErr_val x_val y_val best' theta
            nll_te     = nll distribution mYErr_te x_te y_te best' theta
            mdl_train  = mdl distribution mYErr x y theta best'
            mdl_val    = mdl distribution mYErr_val x_val y_val theta best'
            mdl_te     = mdl distribution mYErr_te x_te y_te theta best'
            vals       = intercalate ","
                       $ Prelude.map show [mse_train, mse_val, mse_te
                                          , r2_train, r2_val, r2_te
                                          , nll_train, nll_val, nll_te
                                          , mdl_train, mdl_val, mdl_te]
            thetaStr   = intercalate ";" $ Prelude.map show (MA.toList theta)
        io . putStrLn $ show ix <> "," <> showExpr expr <> ","
                      <> thetaStr <> "," <> show (countNodes $ convertProtectedOps expr)
                      <> "," <> vals


data Args = Args
  { _dataset      :: String,
    _testData     :: String,
    _gens         :: Int,
    _alg          :: Alg,
    _maxSize      :: Int,
    _split        :: Int,
    _printPareto  :: Bool,
    _trace        :: Bool,
    _distribution :: Distribution,
    _optIter      :: Int,
    _optRepeat    :: Int,
    _nonterminals :: String
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
      ( long "generations"
      <> short 'g'
      <> metavar "GENS"
      <> showDefault
      <> value 100
      <> help "Number of generations." )
   <*> option auto
       ( long "algorithm"
       <> short 'a'
       <> metavar "ALG"
       <> help "Algorithm." )
  <*> option auto
       ( long "maxSize"
       <> short 's'
       <> help "max-size." )
  <*> option auto
       ( long "split"
       <> short 'k'
       <> value 1 
       <> showDefault
       <> help "k-split ratio training-validation")
  <*> switch
       ( long "print-pareto"
       <> help "print Pareto front instead of best found expression")
  <*> switch
       ( long "trace"
       <> help "print all evaluated expressions.")
  <*> option auto
       ( long "distribution"
       <> value Gaussian
       <> showDefault
       <> help "distribution of the data.")
  <*> option auto
       ( long "opt-iter"
       <> value 30
       <> showDefault
       <> help "number of iterations in parameter optimization.")
  <*> option auto
       ( long "opt-retries"
       <> value 1
       <> showDefault
       <> help "number of retries of parameter fitting.")
  <*> option auto
       ( long "non-terminals"
       <> value "Add,Sub,Mul,Div,PowerAbs,Recip"
       <> showDefault
       <> help "set of non-terminals to use in the search."
       )

main :: IO ()
main = do
  args <- execParser opts
  g    <- getStdGen
  dataTrain' <- loadTrainingOnly (_dataset args) True
  dataTest   <- if null (_testData args)
                  then pure dataTrain'
                  else loadTrainingOnly (_testData args) True
  let ((dataTrain, dataVal), g') = runState (splitData dataTrain' $ _split args) g
      alg = evalStateT (egraphSearch dataTrain dataVal dataTest args) emptyGraph
  evalStateT alg g'

  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )
