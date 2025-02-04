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
import Control.Monad ( forM_, forM, when, filterM )
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
import Data.Binary ( encode, decode )
import qualified Data.ByteString.Lazy as BS
import Debug.Trace
import qualified Data.HashSet as Set
import Control.Lens (over)
import qualified Data.Map.Strict as Map

import Util

data Alg = OnlyRandom | BestFirst deriving (Show, Read, Eq)

egraphSearch :: [(DataSet, DataSet)] -> [DataSet] -> Args -> StateT EGraph (StateT StdGen IO) ()
-- terms nEvals maxSize printPareto printTrace slowIter slowRep =
egraphSearch dataTrainVals dataTests args = do
  if null (_loadFrom args)
    then do ecFst <- insertRndExpr (_maxSize args) rndTerm rndNonTerm2
            --ecFst <- insertBestExpr -- use only to debug
            updateIfNothing fitFun ecFst
            insertTerms
            evaluateUnevaluated fitFun
            runEqSat myCost (if _nParams args == 0 then rewritesWithConstant else rewritesParams) 1
            cleanDB
    else (io $ BS.readFile (_loadFrom args)) >>= \eg -> put (decode eg)
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
                        else do ecsBest    <- getTopFitEClassThat 100 (isSizeOf (<(_maxSize args)))
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
       when upd $ runEqSat myCost (if _nParams args == 0 then rewritesWithConstant else rewritesParams) 1 >> cleanDB >> refitChanged


       when (upd && (_trace args))
         do
            ecN'' <- canonical ecN'
            _tree <- getBestExpr ecN''
            fi <- negate . fromJust <$> getFitness ecN''
            thetas <- getTheta ecN''
            let thetaStr   = intercalate "_" $ Prelude.map (intercalate ";" . Prelude.map show . MA.toList) thetas
            io . putStrLn $ showExpr _tree <> "," <> thetaStr <> "," <> show fi
            pure ()
       let radius' = if (not upd) then (max 10 $ min (500 `div` (_maxSize args)) (radius+1)) else (max 10 $ radius-1)
           nEvs'    = nEvs + if upd then 1 else 0
       pure (radius', nEvs')
  io $ putStrLn csvHeader
  if (_printPareto args)
    then paretoFront (_maxSize args) printExpr
    else printBest printExpr
  when ((not.null) (_dumpTo args)) $ get >>= (io . BS.writeFile (_dumpTo args) . encode )
  where
    maxSize = _maxSize args
    relabel        = if (_nParams args == -1) then relabelParams else relabelParamsOrder
    fitFun = fitnessMV (_optRepeat args) (_optIter args) (_distribution args) dataTrainVals

    refitChanged = do ids <- gets (_refits . _eDB) >>= Prelude.mapM canonical . Set.toList
                      modify' $ over (eDB . refits) (const Set.empty)
                      forM_ ids $ \ec -> do t <- getBestExpr ec
                                            (f, p) <- fitFun t
                                            insertFitness ec f p

    combineFrom [] = pure 0
    combineFrom ecs = do
      p1  <- rnd (randomFrom ecs) >>= canonical
      p2  <- rnd (randomFrom ecs) >>= canonical
      coin <- rnd toss
      if coin
         then crossover p1 p2 >>= canonical
         else mutate p1 >>= canonical

    combineFrom' [] = pure 0 -- this is the first terminal and it will always be already evaluated
    combineFrom' ecs = do
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
    (Sz2 _ nFeats) = MA.size (getX . fst . head $ dataTrainVals)
    terms          = if _distribution args == ROXY
                          then [var 0, param 0]
                          else [var ix | ix <- [0 .. nFeats-1]]
                               <> if _nParams args == -1
                                     then [param 0]
                                     else Prelude.map param [0 .. _nParams args - 1]
    rndTerm    = Random.randomFrom terms
    rndNonTerm = Random.randomFrom $ (Uni Id ()) : nonTerms
    rndNonTerm2 = Random.randomFrom nonTerms
    uniNonTerms = Prelude.filter isUni nonTerms
    binNonTerms = Prelude.filter isBin nonTerms
    isUni (Uni _ _) = True
    isUni _         = False
    isBin (Bin _ _ _) = True
    isBin _           = False

    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical

    printExpr :: Int -> EClassId -> RndEGraph ()
    printExpr ix ec = do 
        thetas' <- gets (_theta . _info . (IM.! ec) . _eClass)
        bestExpr <- getBestExpr ec
        let nParams = countParams bestExpr
            fromSz (MA.Sz x) = x 
            nThetas = Prelude.map (fromSz . MA.size) thetas'
        (_, thetas) <- if Prelude.any (/=nParams) nThetas
                        then fitFun bestExpr
                        else pure (1.0, thetas')

        forM_ (Prelude.zip3 dataTrainVals dataTests thetas) $ \((dataTrain, dataVal), dataTest, theta) -> do
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

    -- From eggp
    crossover p1 p2 = do sz <- getSize p1
                         if sz == 1
                          then rnd (randomFrom [p1, p2])
                          else do pos <- rnd $ randomRange (1, sz-1)
                                  cands <- getAllSubClasses p2
                                  tree <- getSubtree pos 0 Nothing [] cands p1
                                  fromTree myCost (relabel tree) >>= canonical

    getSubtree :: Int -> Int -> Maybe (EClassId -> ENode) -> [Maybe (EClassId -> ENode)] -> [EClassId] -> EClassId -> RndEGraph (Fix SRTree)
    getSubtree 0 sz (Just parent) mGrandParents cands p' = do
      p <- canonical p'
      candidates' <- filterM (\c -> (<maxSize-sz) <$> getSize c) cands
      candidates  <- filterM (\c -> doesNotExistGens mGrandParents (parent c)) candidates'
                        >>= traverse canonical
      if null candidates
          then getBestExpr p
          else do subtree <- rnd (randomFrom candidates)
                  getBestExpr subtree
    getSubtree pos sz parent mGrandParents cands p' = do
      p <- canonical p'
      root <- getBestENode p >>= canonize
      case root of
        Param ix -> pure . Fix $ Param ix
        Const x  -> pure . Fix $ Const x
        Var   ix -> pure . Fix $ Var ix
        Uni f t' -> do t <- canonical t'
                       (Fix . Uni f) <$> getSubtree (pos-1) (sz+1) (Just $ Uni f) (parent:mGrandParents) cands t
        Bin op l'' r'' ->
                      do  l <- canonical l''
                          r <- canonical r''
                          szLft <- getSize l
                          szRgt <- getSize r
                          if szLft < pos
                            then do l' <- getBestExpr l
                                    r' <- getSubtree (pos-szLft-1) (sz+szLft+1) (Just $ Bin op l) (parent:mGrandParents) cands r
                                    pure . Fix $ Bin op l' r'
                            else do l' <- getSubtree (pos-1) (sz+szRgt+1) (Just (\t -> Bin op t r)) (parent:mGrandParents) cands l
                                    r' <- getBestExpr r
                                    pure . Fix $ Bin op l' r'

    getAllSubClasses p' = do
      p  <- canonical p'
      en <- getBestENode p
      case en of
        Bin _ l r -> do ls <- getAllSubClasses l
                        rs <- getAllSubClasses r
                        pure (p : (ls <> rs))
        Uni _ t   -> (p:) <$> getAllSubClasses t
        _         -> pure [p]

    mutate p = do sz <- getSize p
                  pos <- rnd $ randomRange (0, sz-1)
                  tree <- mutAt pos maxSize Nothing p
                  fromTree myCost (relabel tree) >>= canonical

    peel :: Fix SRTree -> SRTree ()
    peel (Fix (Bin op l r)) = Bin op () ()
    peel (Fix (Uni f t)) = Uni f ()
    peel (Fix (Param ix)) = Param ix
    peel (Fix (Var ix)) = Var ix
    peel (Fix (Const x)) = Const x

    mutAt :: Int -> Int -> Maybe (EClassId -> ENode) -> EClassId -> RndEGraph (Fix SRTree)
    mutAt 0 sizeLeft Nothing       _ = (insertRndExpr sizeLeft rndTerm rndNonTerm >>= canonical) >>= getBestExpr -- we chose to mutate the root
    mutAt 0 1        _             _ = rnd $ randomFrom terms -- we don't have size left
    mutAt 0 sizeLeft (Just parent) _ = do -- we reached the mutation place
      ec    <- insertRndExpr sizeLeft rndTerm rndNonTerm >>= canonical -- create a random expression with the size limit
      (Fix tree) <- getBestExpr ec           --
      root  <- getBestENode ec
      exist <- canonize (parent ec) >>= doesExist
      if exist
          -- the expression `parent ec` already exists, try to fix
          then do let children = childrenOf root
                  candidates <- case length children of
                                0  -> filterM (checkToken parent . (replaceChildren children)) (Prelude.map peel terms)
                                1 -> filterM (checkToken parent . (replaceChildren children)) uniNonTerms
                                2 -> filterM (checkToken parent . (replaceChildren children)) binNonTerms
                  if null candidates
                      then pure $ Fix tree -- there's no candidate, so we failed and admit defeat
                      else do newToken <- rnd (randomFrom candidates)
                              pure . Fix $ replaceChildren (childrenOf tree) newToken

          else pure . Fix $ tree

    mutAt pos sizeLeft parent p' = do
        p <- canonical p'
        root <- getBestENode p >>= canonize
        case root of
          Param ix -> pure . Fix $ Param ix
          Const x  -> pure . Fix $ Const x
          Var   ix -> pure . Fix $ Var ix
          Uni f t'  -> canonical t' >>= \t -> (Fix . Uni f) <$> mutAt (pos-1) (sizeLeft-1) (Just $ Uni f) t
          Bin op ln rn -> do  l <- canonical ln
                              r <- canonical rn
                              szLft <- getSize l
                              szRgt <- getSize r
                              if szLft < pos
                                then do l' <- getBestExpr l
                                        r' <- mutAt (pos-szLft-1) (sizeLeft-szLft-1) (Just $ Bin op l) r
                                        pure . Fix $ Bin op l' r'
                                else do l' <- mutAt (pos-1) (sizeLeft-szRgt-1) (Just (\t -> Bin op t r)) l
                                        r' <- getBestExpr r
                                        pure . Fix $ Bin op l' r'

    checkToken parent en' = do  en <- canonize en'
                                mEc <- gets ((Map.!? en) . _eNodeToEClass)
                                case mEc of
                                    Nothing -> pure True
                                    Just ec -> do ec' <- canonical ec
                                                  ec'' <- canonize (parent ec')
                                                  not <$> doesExist ec''
    doesExist, doesNotExist :: ENode -> RndEGraph Bool
    doesExist en = gets ((Map.member en) . _eNodeToEClass)
    doesNotExist en = gets ((Map.notMember en) . _eNodeToEClass)

    doesNotExistGens :: [Maybe (EClassId -> ENode)] -> ENode -> RndEGraph Bool
    doesNotExistGens []              en = gets ((Map.notMember en) . _eNodeToEClass)
    doesNotExistGens (mGrand:grands) en = do  b <- gets ((Map.notMember en) . _eNodeToEClass)
                                              if b
                                                then pure True
                                                else case mGrand of
                                                    Nothing -> pure False
                                                    Just gf -> do ec  <- gets ((Map.! en) . _eNodeToEClass)
                                                                  en' <- canonize (gf ec)
                                                                  doesNotExistGens grands en'

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
    _nParams      :: Int,
    _nonterminals :: String,
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
       ( long "loss"
       <> value MSE
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
       ( long "number-params"
       <> value (-1)
       <> showDefault
       <> help "maximum number of parameters in the model. If this argument is absent, the number is bounded by the maximum size of the expression and there will be no repeated parameter.")
  <*> strOption
       ( long "non-terminals"
       <> value "Add,Sub,Mul,Div,PowerAbs,Recip"
       <> showDefault
       <> help "set of non-terminals to use in the search."
       )
  <*> strOption
       ( long "dump-to"
       <> value ""
       <> showDefault
       <> help "dump final e-graph to a file."
       )
  <*> strOption
       ( long "load-from"
       <> value ""
       <> showDefault
       <> help "load initial e-graph from a file."
       )

main :: IO ()
main = do
  args <- execParser opts
  g    <- getStdGen
  let datasets = words (_dataset args)
  dataTrains' <- Prelude.mapM (flip loadTrainingOnly True) datasets -- load all datasets 
  dataTests   <- if null (_testData args)
                  then pure dataTrains'
                  else Prelude.mapM (flip loadTrainingOnly True) $ words (_testData args)

  let (dataTrainVals, g') = runState (Prelude.mapM (`splitData` (_split args)) dataTrains') g
      alg = evalStateT (egraphSearch dataTrainVals dataTests args) emptyGraph
  evalStateT alg g'

  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Symbolic Regression search algorithm\
                                   \ exploiting the potentials of equality saturation\
                                   \ and e-graphs."
           <> header "SymRegg - symbolic regression with e-graphs."
            )
