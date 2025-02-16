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
import Algorithm.SRTree.Opt
import Control.Lens (element, makeLenses, over, (&), (+~), (-~), (.~), (^.))
import Control.Monad (foldM, forM_, forM, when, unless, filterM, (>=>), replicateM, replicateM_)
import Control.Monad.State.Strict
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import Data.Massiv.Array as MA hiding (forM_, forM)
import Data.Maybe (fromJust, isNothing, isJust)
import Data.SRTree
import Data.SRTree.Datasets
import Data.SRTree.Eval
import Data.SRTree.Random (randomTree)
import Data.SRTree.Print
import Options.Applicative as Opt hiding (Const)
import Random
import System.Random
import qualified Data.HashSet as Set
import Data.List ( sort, maximumBy, intercalate, sortOn, intersperse, nub )
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as FingerTree
import Data.Function ( on )
import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IntMap
import List.Shuffle ( shuffle )
import Algorithm.SRTree.NonlinearOpt
import Data.Binary ( encode, decode )
import qualified Data.ByteString.Lazy as BS

import Debug.Trace
import Algorithm.EqSat (runEqSat,applySingleMergeOnlyEqSat)

import GHC.IO (unsafePerformIO)
import Control.Scheduler 
import Control.Monad.IO.Unlift
import Data.SRTree (convertProtectedOps)

import Util

egraphGP :: [(DataSet, DataSet)] -> [DataSet] -> Args -> StateT EGraph (StateT StdGen IO) ()
egraphGP dataTrainVals dataTests args = do
  when ((not.null) (_loadFrom args)) $ (io $ BS.readFile (_loadFrom args)) >>= \eg -> put (decode eg)

  pop <- replicateM (_nPop args) $ do ec <- insertRndExpr (_maxSize args) rndTerm rndNonTerm >>= canonical
                                      updateIfNothing fitFun ec
                                      pure ec
  insertTerms
  --runEqSat myCost rewritesParams 1
  --cleanDB
  evaluateUnevaluated fitFun
  pop' <- Prelude.mapM canonical pop
  when (_trace args) $ printPop pop'
  let m = (_nPop args) `div` (_maxSize args)

  finalPop <- iterateFor (_gens args) pop' $ \it ps' -> do
    -- ps <- Prelude.mapM canonical ps'
    --let chunks = 1
    --    (parts, r) = _nPop args `divMod` chunks -- chunks of 50
    --    genChunk = Prelude.mapM canonical ps' >>= \ps -> replicateM chunks (tournament ps) >>= Prelude.mapM combine
    --    genPart  = genChunk >>= \chunk -> (runEqSat myCost rewritesSimple 1 >> cleanDB) >> pure chunk
    --newPop' <- (<>) <$> (concat <$> (replicateM parts genPart)) <*> (concat <$> replicateM r genPart)
    --parents <- replicateM (_nPop args - if (_moo args) then (_maxSize args) else 0) (tournament ps)
    --newPop' <- Prelude.mapM combine parents
    --runEqSat myCost rewritesSimple 1 --applySingleMergeOnlyEqSat myCost rewritesSimple
    --cleanDB
    newPop' <- replicateM (_nPop args) (evolve ps')
    --applySingleMergeOnlyEqSat myCost rewritesParams >> cleanDB
    --newPop' <- Prelude.mapM (\eId -> canonical eId >>= \eId' -> (updateIfNothing fitFun eId' >> pure eId')) newPop''
    --Prelude.mapM_ (updateIfNothing fitFun) newPop'

    totSz <- gets (IntMap.size . _eClass)
    let full = totSz > max maxMem (_nPop args)
    when full cleanEGraph

    newPop <- if (_moo args)
                then do
                        let n_paretos = (_nPop args) `div` (_maxSize args)
                        pareto <- concat <$> (forM [1 .. _maxSize args] $ \n -> getTopFitEClassWithSize n 2)
                        let remainder = _nPop args - length pareto
                        lft <- if full
                                  then getTopFitEClassThat remainder (const True)
                                  else pure $ Prelude.take remainder newPop'
                        Prelude.mapM canonical (pareto <> lft)
                else if full
                       then getTopFitEClassThat (_nPop args) (const True)
                       else Prelude.mapM canonical newPop'
    when (_trace args) $ printPop newPop


    pure newPop

  io $ putStrLn "id,Expression,theta,size,MSE_train,MSE_val,MSE_test,R2_train,R2_val,R2_test,nll_train,nll_val,nll_test,mdl_train,mdl_val,mdl_test"
  if (_printPareto args)
    then paretoFront fitFun (_maxSize args) printExpr
    else printBest fitFun printExpr
  when ((not.null) (_dumpTo args)) $ get >>= (io . BS.writeFile (_dumpTo args) . encode )
  where
    maxSize = (_maxSize args)
    maxMem = 300000 -- running 1 iter of eqsat for each new individual will consume ~3GB
    fitFun = fitnessMV shouldReparam (_optRepeat args) (_optIter args) (_distribution args) dataTrainVals
    nonTerms   = parseNonTerms (_nonterminals args)
    (Sz2 _ nFeats) = MA.size (getX .fst . head $ dataTrainVals)
    params         = if _nParams args == -1 then [param 0] else Prelude.map param [0 .. _nParams args - 1]
    shouldReparam  = _nParams args == -1
    relabel        = if shouldReparam then relabelParams else relabelParamsOrder
    terms          = if _distribution args == ROXY
                          then (var 0 : params)
                          else [var ix | ix <- [0 .. nFeats-1]] <> params
    uniNonTerms = [t | t <- nonTerms, isUni t]
    binNonTerms = [t | t <- nonTerms, isBin t]
    isUni (Uni _ _)   = True
    isUni _           = False
    isBin (Bin _ _ _) = True
    isBin _           = False

    -- TODO: merge two or more egraphs
    cleanEGraph = do let nParetos = (maxMem `div` 5) `div` _maxSize args
                     io . putStrLn $ "cleaning"
                     pareto <- (concat <$> (forM [1 .. _maxSize args] $ \n -> getTopFitEClassWithSize n nParetos))
                                 >>= Prelude.mapM canonical
                     infos  <- forM pareto (\c -> gets (_info . (IntMap.! c) . _eClass))
                     exprs  <- forM pareto getBestExpr
                     put emptyGraph
                     newIds <- fromTrees myCost $ Prelude.map relabel exprs
                     forM_ (Prelude.zip newIds (Prelude.reverse infos)) $ \(eId, info) ->
                         insertFitness eId (fromJust $ _fitness info) (_theta info)

    rndTerm    = Random.randomFrom terms
    rndNonTerm = Random.randomFrom nonTerms

    refitChanged = do ids <- gets (_refits . _eDB) >>= Prelude.mapM canonical . Set.toList >>= pure . nub
                      modify' $ over (eDB . refits) (const Set.empty)
                      forM_ ids $ \ec -> do t <- getBestExpr ec
                                            (f, p) <- fitFun t
                                            insertFitness ec f p

    iterateFor 0 xs f = pure xs
    iterateFor n xs f = do xs' <- f n xs
                           iterateFor (n-1) xs' f

    evolve xs' = do xs <- Prelude.mapM canonical xs'
                    parents <- tournament xs
                    offspring <- combine parents
                    --applySingleMergeOnlyEqSat myCost rewritesParams >> cleanDB
                    if _nParams args == 0
                       then runEqSat myCost rewritesWithConstant 1 >> cleanDB >> refitChanged
                       else runEqSat myCost rewritesParams 1 >> cleanDB >> refitChanged
                    canonical offspring >>= updateIfNothing fitFun
                    canonical offspring
                    --pure offspring

    tournament xs = do p1 <- applyTournament xs >>= canonical
                       p2 <- applyTournament xs >>= canonical
                       pure (p1, p2)

    applyTournament :: [EClassId] -> RndEGraph EClassId
    applyTournament xs = do challengers <- replicateM (_nTournament args) (rnd $ randomFrom xs) >>= traverse canonical
                            fits <- Prelude.map fromJust <$> Prelude.mapM getFitness challengers
                            pure . snd . maximumBy (compare `on` fst) $ Prelude.zip fits challengers

    combine (p1, p2) = (crossover p1 p2 >>= mutate) >>= canonical

    crossover p1 p2 = do sz <- getSize p1
                         coin <- rnd $ tossBiased (_pc args)
                         if sz == 1 || not coin
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
                      do l <- canonical l''
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
                  coin <- rnd $ tossBiased (_pm args)
                  if coin
                     then do pos <- rnd $ randomRange (0, sz-1)
                             tree <- mutAt pos maxSize Nothing p
                             fromTree myCost (relabel tree) >>= canonical
                     else pure p

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
          Bin op ln rn -> do l <- canonical ln
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

    checkToken parent en' = do en <- canonize en'
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
    doesNotExistGens (mGrand:grands) en = do b <- gets ((Map.notMember en) . _eNodeToEClass)
                                             if b
                                               then pure True
                                               else case mGrand of
                                                    Nothing -> pure False
                                                    Just gf -> do ec  <- gets ((Map.! en) . _eNodeToEClass)
                                                                  en' <- canonize (gf ec)
                                                                  doesNotExistGens grands en'

    printExpr :: Int -> EClassId -> RndEGraph ()
    printExpr ix ec = do
        thetas' <- gets (_theta . _info . (IM.! ec) . _eClass)
        bestExpr <- (if _simplify args then simplifyEqSatDefault else id) <$> getBestExpr ec
        let nParams = countParamsUniq bestExpr
            fromSz (MA.Sz x) = x 
            nThetas  = Prelude.map (fromSz . MA.size) thetas'
        (_, thetas) <- if Prelude.any (/=nParams) nThetas || _simplify args
                        then fitFun bestExpr
                        else pure (1.0, thetas')

        forM_ (Prelude.zip3 dataTrainVals dataTests thetas) $ \((dataTrain, dataVal), dataTest, theta) -> do
            let (x, y, mYErr) = dataTrain
                (x_val, y_val, mYErr_val) = dataVal
                (x_te, y_te, mYErr_te) = dataTest
                distribution = _distribution args
                best'     = if shouldReparam then relabelParams bestExpr else relabelParamsOrder bestExpr
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
                showFun    = if _numpy args then showPython best' else showExpr expr
            io . putStrLn $ show ix <> "," <> showFun <> ","
                          <> thetaStr <> "," <> show (countNodes $ convertProtectedOps expr)
                          <> "," <> vals

    printPop pop = forM_ pop $ \ecN'-> do
            ecN'' <- canonical ecN'
            _tree <- getBestExpr ecN''
            fi <- fromJust <$> getFitness ecN''
            thetas <- getTheta ecN''
            let thetaStr   = intercalate "_" $ Prelude.map (intercalate ";" . Prelude.map show . MA.toList) thetas
                tree = if _simplify args then simplifyEqSatDefault _tree else _tree
                showFun = if _numpy args then showPython else showExpr
            io . putStrLn $ showFun tree <> "," <> thetaStr <> "," <> show fi
            pure ()

    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical

data Args = Args
  { _dataset      :: String,
    _testData     :: String,
    _gens         :: Int,
    _maxSize      :: Int,
    _split        :: Int,
    _printPareto  :: Bool,
    _trace        :: Bool,
    _distribution :: Distribution,
    _optIter      :: Int,
    _optRepeat    :: Int,
    _nParams      :: Int,
    _nPop         :: Int,
    _nTournament  :: Int,
    _pc           :: Double,
    _pm           :: Double,
    _nonterminals :: String,
    _dumpTo       :: String,
    _loadFrom     :: String,
    _moo          :: Bool,
    _numpy        :: Bool,
    _simplify     :: Bool
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
       <> help "loss function: MSE, Gaussian, Poisson, Bernoulli.")
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
  <*> option auto
       ( long "nPop"
       <> value 100
       <> showDefault
       <> help "population size (Default: 100).")
  <*> option auto
       ( long "tournament-size"
       <> value 2
       <> showDefault
       <> help "tournament size.")
  <*> option auto
       ( long "pc"
       <> value 1.0
       <> showDefault
       <> help "probability of crossover.")
  <*> option auto
       ( long "pm"
       <> value 0.3
       <> showDefault
       <> help "probability of mutation.")
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
  <*> switch
       ( long "moo"
       <> help "replace the current population with the pareto front instead of replacing it with the generated children."
       )
  <*> switch
       ( long "to-numpy"
       <> help "outputs the expressions using a numpy format."
       )
  <*> switch
       ( long "simplify"
       <> help "simplify the expressions before displaying them."
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
      alg = evalStateT (egraphGP dataTrainVals dataTests args) emptyGraph
  evalStateT alg g'
  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "An implementation of GP with modified crossover and mutation\
                                   \ operators designed to exploit equality saturation and e-graphs.\
                                   \ https://arxiv.org/abs/2501.17848\n"
           <> header "eggp - E-graph Genetic Programming for Symbolic Regression." )
