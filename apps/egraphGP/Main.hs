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
import Data.List ( sort, maximumBy, intercalate, sortOn, intersperse )
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as FingerTree
import Data.Function ( on )
import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IntMap
import List.Shuffle ( shuffle )
import Algorithm.SRTree.NonlinearOpt

import Debug.Trace
import Algorithm.EqSat (runEqSat)

import GHC.IO (unsafePerformIO)
import Control.Scheduler 
import Control.Monad.IO.Unlift
import Data.SRTree (convertProtectedOps)


type RndEGraph a = EGraphST (StateT StdGen IO) a

io = lift . lift
{-# INLINE io #-}
rnd = lift
{-# INLINE rnd #-}

myCost :: SRTree Int -> Int
myCost (Var _)      = 1
myCost (Const _)    = 1
myCost (Param _)    = 1
myCost (Bin op l r) = 2 + l + r
myCost (Uni _ t)    = 3 + t

-- experiment 1 80/30
fitnessFun :: Int -> Distribution -> SRMatrix -> PVector -> Maybe PVector -> SRMatrix -> PVector -> Maybe PVector -> Fix SRTree -> PVector -> (Double, PVector)
fitnessFun nIter distribution x y mYErr x_val y_val mYErr_val _tree thetaOrig =
  if isNaN val || isNaN tr
    then (-(1/0), theta) -- infinity
    else (min tr val, theta)
  where
    tree         = relabelParams _tree
    nParams      = countParams tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    (Sz2 m' _)    = MA.size x
    (theta, fit, nEvs) = minimizeNLL' VAR1 distribution mYErr nIter x y tree thetaOrig
    evalF a b c  = negate $ nll distribution c a b tree $ if nParams == 0 then thetaOrig else theta
    tr           = evalF x y mYErr
    val          = evalF x_val y_val mYErr_val

{-# INLINE fitnessFun #-}

fitnessFunRep :: Int -> Int -> Distribution -> SRMatrix -> PVector -> Maybe PVector -> SRMatrix -> PVector -> Maybe PVector -> Fix SRTree -> RndEGraph (Double, PVector)
fitnessFunRep nRep nIter distribution x y mYErr x_val y_val mYErr_val _tree = do
    let tree = relabelParams _tree
        nParams = countParams tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    thetaOrigs <- replicateM nRep (rnd $ randomVec nParams)
    let fits = Prelude.map (fitnessFun nIter distribution x y mYErr x_val y_val mYErr_val _tree) thetaOrigs
    --replicateM nRep (fitnessFun nIter distribution x y mYErr x_val y_val mYErr_val _tree)
    pure (maximumBy (compare `on` fst) fits)
{-# INLINE fitnessFunRep #-}

-- helper query functions

getFitness :: EClassId -> RndEGraph (Maybe Double)
getFitness c = gets (_fitness . _info . (IM.! c) . _eClass)
{-# INLINE getFitness #-}
getTheta :: EClassId -> RndEGraph (Maybe PVector)
getTheta c = gets (_theta . _info . (IM.! c) . _eClass)
{-# INLINE getTheta #-}
getSize :: EClassId -> RndEGraph Int
getSize c = gets (_size . _info . (IM.! c) . _eClass)
{-# INLINE getSize #-}

egraphGP distribution x y mYErr x_val y_val mYErr_val x_te y_te mYErr_te terms nPop nIters tournamentSize pc pm maxSize printPareto printTrace optIter optRep = do

  pop <- replicateM nPop $ do ec <- insertRndExpr maxSize >>= canonical
                              updateIfNothing ec
                              pure ec
  insertTerms
  runEqSat myCost rewritesParams 1
  cleanDB
  pop' <- Prelude.mapM canonical pop
  when printTrace $ printPop pop'

  finalPop <- iterateFor nIters pop' $ \ps' -> do
    ps <- Prelude.mapM canonical ps'
    parents <- replicateM nPop (tournament ps)
    newPop' <- Prelude.mapM (combine >=> canonical) parents
    runEqSat myCost rewritesParams 1
    cleanDB
    newPop <- Prelude.mapM canonical newPop'
    when printTrace $ printPop newPop
    pure newPop

  io $ putStrLn "id,Expression,theta,size,MSE_train,MSE_val,MSE_test,R2_train,R2_val,R2_test,nll_train,nll_val,nll_test,mdl_train,mdl_val,mdl_test"
  if printPareto
    then paretoFront
    else printBest

  where
    iterateFor 0 xs f = pure xs
    iterateFor n xs f = do xs' <- f xs
                           iterateFor (n-1) xs' f

    tournament xs = do p1 <- applyTournament xs >>= canonical
                       p2 <- applyTournament xs >>= canonical
                       pure (p1, p2)

    applyTournament :: [EClassId] -> RndEGraph EClassId
    applyTournament xs = do challengers <- replicateM tournamentSize (rnd $ randomFrom xs)
                            fits <- Prelude.map fromJust <$> Prelude.mapM getFitness challengers
                            pure . snd . maximumBy (compare `on` fst) $ Prelude.zip fits challengers

    combine (p1, p2) = do child <- (crossover p1 p2 >>= mutate) >>= canonical
                          updateIfNothing child
                          pure child

    crossover p1 p2 = do sz <- getSize p1
                         coin <- rnd $ tossBiased pc
                         if sz == 1 || not coin
                            then pure p2
                            else do pos <- rnd $ randomRange (1, sz-1)
                                    cands <- getAllSubClasses p2
                                    tree <- getSubtree pos 0 Nothing [] cands p1
                                    fromTree myCost tree >>= canonical

    -- TODO: add grandparent
    getSubtree :: Int -> Int -> Maybe (EClassId -> ENode) -> [Maybe (EClassId -> ENode)] -> [EClassId] -> EClassId -> RndEGraph (Fix SRTree)
    getSubtree 0 sz (Just parent) mGrandParents cands p' = do
      p <- canonical p'
      candidates' <- filterM (\c -> (<maxSize-sz) <$> getSize c) cands
      candidates  <- filterM (\c -> doesNotExistGens mGrandParents (parent c)) candidates'
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
        Uni f t  -> (Fix . Uni f) <$> getSubtree (pos-1) (sz+1) (Just $ Uni f) (parent:mGrandParents) cands t
        Bin op l r -> do szLft <- getSize l
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
                  coin <- rnd $ tossBiased pm
                  if coin
                     then do pos <- rnd $ randomRange (0, sz-1)
                             tree <- mutAt pos maxSize Nothing p
                             fromTree myCost tree >>= canonical
                     else pure p

    peel :: Fix SRTree -> SRTree ()
    peel (Fix (Bin op l r)) = Bin op () ()
    peel (Fix (Uni f t)) = Uni f ()
    peel (Fix (Param ix)) = Param ix
    peel (Fix (Var ix)) = Var ix
    peel (Fix (Const x)) = Const x

    mutAt :: Int -> Int -> Maybe (EClassId -> ENode) -> EClassId -> RndEGraph (Fix SRTree)
    mutAt 0 sizeLeft Nothing       _ = (insertRndExpr sizeLeft >>= canonical) >>= getBestExpr -- we chose to mutate the root
    mutAt 0 1        _             _ = rnd $ randomFrom terms -- we don't have size left
    mutAt 0 sizeLeft (Just parent) _ = do -- we reached the mutation place
      ec    <- insertRndExpr sizeLeft >>= canonical -- create a random expression with the size limit
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
          Uni f t  -> (Fix . Uni f) <$> mutAt (pos-1) (sizeLeft-1) (Just $ Uni f) t
          Bin op l r -> do szLft <- getSize l
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




      -- choose point of mutation
      -- replace with something unseen node

    printPop pop = forM_ pop $ \ecN'-> do
            ecN'' <- canonical ecN'
            _tree <- getBestExpr ecN''
            fi <- negate . fromJust <$> getFitness ecN''
            theta <- fromJust <$> getTheta ecN''
            let thetaStr   = intercalate ";" $ Prelude.map show (MA.toList theta)
            io . putStrLn $ showExpr _tree <> "," <> thetaStr <> "," <> show fi
            pure ()


    updateIfNothing ec = do
      mf <- getFitness ec
      case mf of
        Nothing -> do
          t <- getBestExpr ec
          (f, p) <- fitnessFunRep optRep optIter distribution x y mYErr x_val y_val mYErr_val t
          insertFitness ec f p
          --io $ print f
          pure True
        Just _ -> pure False


    getParetoEcsUpTo n = concat <$> forM [1..maxSize] (\i -> getTopECLassWithSize  i n)


    uniNonTerms = [Uni Recip ()]
    binNonTerms = [Bin Add () (), Bin Sub () (), Bin Mul () (), Bin Div () (), Bin PowerAbs () ()]
    nonTerms   = uniNonTerms <> binNonTerms
    rndTerm    = Random.randomFrom terms
    rndNonTerm = Random.randomFrom nonTerms

    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical

    insertRndExpr :: Int -> RndEGraph EClassId
    insertRndExpr maxSize =
      do grow <- rnd toss
         n <- rnd (randomFrom [if maxSize > 4 then 4 else 1 .. maxSize])
         t <- rnd $ Random.randomTree 3 8 n rndTerm rndNonTerm grow
         fromTree myCost t >>= canonical


    getBestExprWithSize n =
        do ec <- getTopECLassWithSize n 1 >>= traverse canonical
           if (not (null ec))
            then do
              bestFit <- getFitness $ head ec
              bestP   <- gets (_theta . _info . (IM.! (head ec)) . _eClass)
              (:[]) . (,bestP) . (,bestFit) . (,ec) <$> getBestExpr (head ec)
            else pure []




    printExpr ix ec = do
        fit <- fromJust <$> getFitness ec 
        theta <- gets (fromJust . _theta . _info . (IM.! ec) . _eClass)
        --((best, mf), mtheta) <- (,theta) . (,fit) <$> getBest ec
        best <- getBestExpr ec
        --(_, theta) <- fitnessFunRep longRep longIter distribution x y mYErr x_val y_val mYErr_val best
        let best'     = relabelParams best
            expr      = paramsToConst (MA.toList theta) best'
            unprotect = convertProtectedOps expr 
            mse_train = mse x y best' theta
            mse_val   = mse x_val y_val best' theta
            mse_te    = mse x_te y_te best' theta
            r2_train  = r2 x y best' theta
            r2_val    = r2 x_val y_val best' theta
            r2_te     = r2 x_te y_te best' theta
            nll_train  = nll distribution mYErr x y best' theta
            nll_val    = nll distribution mYErr_val x_val y_val best' theta
            nll_te     = nll distribution mYErr_te x_te y_te best' theta
            mdl_train  = mdl distribution mYErr x y theta best' --unprotect
            mdl_val    = mdl distribution mYErr_val x_val y_val theta best' --unprotect
            mdl_te     = mdl distribution mYErr_te x_te y_te theta best' --unprotect
            vals       = intercalate "," $ Prelude.map show [mse_train, mse_val, mse_te, r2_train, r2_val, r2_te, nll_train, nll_val, nll_te, mdl_train, mdl_val, mdl_te]
            thetaStr   = intercalate ";" $ Prelude.map show (MA.toList theta)
        io . putStrLn $ show ix <> "," <> showExpr expr <> "," <> thetaStr <> "," <> show (countNodes $ convertProtectedOps expr) <> "," <> vals

    printBest = do
      bec <- gets (snd . getGreatest . _fitRangeDB . _eDB) >>= canonical
      printExpr 0 bec

    paretoFront = go 1 0 (-(1.0/0.0))
      where
        go n ix f
          | n > maxSize = pure ()
          | otherwise   = do
              ecList <- getBestExprWithSize n
              if not (null ecList)
                 then do let (((best, ec), mf), mtheta) = head ecList
                             improved = fromJust mf > f 
                         cm <- gets _canonicalMap
                         ec' <- traverse canonical ec
                         when improved $ printExpr ix (head ec')
                         go (n+1) (ix + if improved then 1 else 0) (max f (fromJust mf))
                 else go (n+1) ix f

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
    _nPop         :: Int,
    _nTournament  :: Int,
    _pc           :: Double,
    _pm           :: Double
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

chunksOf :: Int -> [e] -> [[e]]
chunksOf i ls = Prelude.map (Prelude.take i) (build (splitter ls))
 where
  splitter :: [e] -> ([e] -> a -> a) -> a -> a
  splitter [] _ n = n
  splitter l c n = l `c` splitter (Prelude.drop i l) c n
  build :: ((a -> [a] -> [a]) -> [a] -> [a]) -> [a]
  build g = g (:) []

splitData :: SRMatrix -> PVector -> Maybe PVector ->Int -> State StdGen (SRMatrix, SRMatrix, PVector, PVector, Maybe PVector, Maybe PVector)
splitData x y mYErr k = do
  if k == 1
    then pure (x, x, y, y, mYErr, mYErr)
    else do
      ixs' <- (state . shuffle) [0 .. sz-1]
      let ixs = chunksOf k ixs'

      let (x_tr, x_te) = getX ixs x
          (y_tr, y_te) = getY ixs y
          mY = fmap (getY ixs) mYErr
          (y_err_tr, y_err_te) = (fmap fst mY, fmap snd mY)
      pure (x_tr, x_te, y_tr, y_te, y_err_tr, y_err_te)
  where
    (MA.Sz sz) = MA.size y
    --qty_tr     = round (thr * fromIntegral sz)
    --qty_te     = sz - qty_tr
    comp_x     = MA.getComp x
    comp_y     = MA.getComp y

    getX :: [[Int]] -> SRMatrix -> (SRMatrix, SRMatrix)
    getX ixs xs' = let xs = MA.toLists xs' :: [MA.ListItem MA.Ix2 Double]
                    in ( MA.fromLists' comp_x [xs !! ix | ixs_i <- ixs, ix <- Prelude.tail ixs_i]
                       , MA.fromLists' comp_x [xs !! ix | ixs_i <- ixs, let ix = Prelude.head ixs_i]
                       )
    getY :: [[Int]] -> PVector -> (PVector, PVector)
    getY ixs ys  = ( MA.fromList comp_y [ys MA.! ix | ixs_i <- ixs, ix <- Prelude.tail ixs_i]
                   , MA.fromList comp_y [ys MA.! ix | ixs_i <- ixs, let ix = Prelude.head ixs_i]
                   )

getTrain ((a, b, _, _), (c, _), _, _) = (a,b,c)

main :: IO ()
main = do
  --args <- pure (Args "nikuradse_2.csv" 100) -- execParser opts
  args <- execParser opts
  g <- getStdGen
  ((x, y, _, _), (mYErr, _), _, _) <- loadDataset (_dataset args) True
  (x_te, y_te, mYErr_te) <- if null (_testData args)
                              then pure (x, y, mYErr)
                              else getTrain <$> loadDataset (_testData args) True
  let ((x_tr, x_val, y_tr, y_val, mYErr_tr, mYErr_val),g') = runState (splitData x y mYErr $ _split args) g
  let (Sz2 _ nFeats) = MA.size x
      terms          = if _distribution args == ROXY
                          then [var 0, param 0]
                          else [var ix | ix <- [0 .. nFeats-1]] <> [param 0] -- [param ix | ix <- [0 .. 5]]
      alg            = evalStateT (egraphGP (_distribution args) x_tr y_tr mYErr_tr x_val y_val mYErr_val x_te y_te mYErr_te terms (_nPop args) (_gens args) (_nTournament args) (_pc args) (_pm args) (_maxSize args) (_printPareto args) (_trace args) (_optIter args) (_optRepeat args)) emptyGraph
  evalStateT alg g'

  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )
