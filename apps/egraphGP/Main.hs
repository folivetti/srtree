{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}
{-# LANGUAGE  MultiWayIf #-}
{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE  BangPatterns #-}

module Main where 

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Simplify
import Algorithm.EqSat.Build
import Algorithm.EqSat.Queries
import Algorithm.EqSat.Info
import Algorithm.EqSat.DB
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.Opt
import Control.Lens (element, makeLenses, over, (&), (+~), (-~), (.~), (^.))
import Control.Monad (foldM, forM_, forM, when, unless, filterM, (>=>), replicateM, replicateM_)
import Control.Monad.State.Strict
import qualified Data.IntMap.Strict as IM
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
import Data.List ( sort, maximumBy, intercalate, sortOn )
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as FingerTree
import Data.Function ( on )
import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IntMap
import List.Shuffle ( shuffle )

import Debug.Trace
import Algorithm.EqSat (runEqSat)

-- Insert random expression 
-- Evaluate random subtree 
-- Insert new random parent eNode 

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

data Alg = OnlyRandom | BestFirst deriving (Show, Read, Eq)

-- experiment 1 80/30
fitnessFun :: SRMatrix -> PVector -> SRMatrix -> PVector -> Fix SRTree -> RndEGraph (Double, PVector)
fitnessFun x y x_val y_val _tree = do
    let tree         = relabelParams _tree
        nParams      = countParams tree
    thetaOrig <- rnd $ randomVec nParams --   = MA.replicate Seq nParams 1.0
    let (theta, fit) = minimizeNLL Gaussian Nothing 50 x y tree thetaOrig
        tr           = negate . mse x y tree $ if nParams == 0 then thetaOrig else theta
        val          = negate . mse x_val y_val tree $ if nParams == 0 then thetaOrig else theta
        -- val       = r2 x y tree $ if nParams == 0 then thetaOrig else theta
    pure $ if isNaN val || isNaN tr
            then (-1/0, theta) -- infinity
            else (min tr val, theta)
{-# INLINE fitnessFun #-}

fitnessFunRep :: SRMatrix -> PVector -> SRMatrix -> PVector -> Fix SRTree -> RndEGraph (Double, PVector)
fitnessFunRep x y x_val y_val _tree = do
    fits <- replicateM 1 (fitnessFun x y x_val y_val _tree)
    pure (maximumBy (compare `on` fst) fits)
{-# INLINE fitnessFunRep #-}

-- helper query functions
fitnessIs p = p . _fitness . _info
{-# INLINE fitnessIs #-}

getFitness :: EClassId -> RndEGraph (Maybe Double)
getFitness c = gets (_fitness . _info . (IM.! c) . _eClass)
{-# INLINE getFitness #-}
getSize :: EClassId -> RndEGraph Int
getSize c = gets (_size . _info . (IM.! c) . _eClass)
{-# INLINE getSize #-}
getSizeOf :: (Int -> Bool) -> [EClassId] -> RndEGraph [EClassId]
getSizeOf p = filterM (getSize >=> (pure . p))
{-# INLINE getSizeOf #-}

(&&&) p1 p2 x = p1 x && p2 x
{-# INLINE (&&&) #-}

isValidFitness = fitnessIs (isJust &&& (not . isNaN . fromJust) &&& (not . isInfinite . fromJust))
{-# INLINE isValidFitness #-}

evaluated = fitnessIs isJust
{-# INLINE evaluated #-}
unevaluated' = fitnessIs isNothing
{-# INLINE unevaluated' #-}

isSizeOf p = p . _size . _info
{-# INLINE isSizeOf #-}

funDoesNotExistWith node = Prelude.any (not . (`sameFunAs` node) . snd) . _parents
  where sameFunAs (Uni f _) (Uni g _) = f == g
        sameFunAs _ _ = False
{-# INLINE funDoesNotExistWith #-}

opDoesNotExistWith :: (SRTree ()) -> EClassId -> EClass -> Bool
opDoesNotExistWith node ecId = Prelude.any (not . (`sameOpAs` node) . snd) . _parents
  where sameOpAs (Bin op1 l _) (Bin op2 _ _) = op1 == op2 && ecId == l
        sameOpAs _ _ = False
{-# INLINE opDoesNotExistWith #-}

rewriteBasic2 :: [Rule]
rewriteBasic2 =
    [
      "x" * "y" :=> "y" * "x"
    , "x" + "y" :=> "y" + "x"
    , ("x" ** "y") * ("x" ** "z") :=> "x" ** ("y" + "z") -- :| isPositive "x"
    , ("x" + "y") + "z" :=> "x" + ("y" + "z")
    , ("x" * "y") * "z" :=> "x" * ("y" * "z")
    , ("x" * "y") + ("x" * "z") :=> "x" * ("y" + "z")
    , ("w" * "x") + ("z" * "x") :=> ("w" + "z") * "x" -- :| isConstPt "w" :| isConstPt "z"
    ]

egraphSearch alg x y x_val y_val x_te y_te terms nEvals maxSize = do
  ec <- insertRndExpr maxSize
  updateIfNothing ec
  insertTerms
  evaluateUnevaluated
  runEqSat myCost rewriteBasic2 1

  while ((<nEvals) . snd) (1,1) $
    \(radius, nEvs) ->
      do
       --nEvs  <- gets (FingerTree.size . _fitRangeDB . _eDB)
       nCls  <- gets (IM.size . _eClass)
       nUnev <- gets (IntSet.size . _unevaluated . _eDB)
       let nEvs = nCls - nUnev
       --io . print $ (nCls, nEvs)
       bestF <- getBestFitness

       (ecN, b) <- case alg of
                    OnlyRandom -> do let ratio = fromIntegral nEvs / fromIntegral nCls
                                     b <- rnd (tossBiased ratio)
                                     ec <- if b && ratio > 0.99 then insertRndExpr maxSize >>= canonical else evaluateRndUnevaluated >>= canonical
                                     pure (ec, False)
                    BestFirst  -> do
                      ecsPareto <- getParetoEcsUpTo radius
                      ecsBest   <- getBestEcs (isSizeOf (<=maxSize)) radius

                      ecPareto     <- combineFrom ecsPareto
                      curFitPareto <- getFitness ecPareto

                      if isNothing curFitPareto
                        then pure (ecPareto, False)
                        else do ecBest     <- combineFrom ecsBest
                                curFitBest <- getFitness ecBest
                                if isNothing curFitBest
                                  then pure (ecBest, False)
                                  else do ee <- evalRndSubTree
                                          case ee of
                                            Nothing -> do ec <- insertRndExpr maxSize >>= canonical
                                                          pure (ec, True)
                                            Just c  -> pure (c, False)

       upd <- updateIfNothing ecN
       when (upd)
         do runEqSat myCost rewriteBasic2 1
            cleanDB
            pure ()
       let radius' = if b then (max 1 $ min (200 `div` maxSize) (radius+1)) else (max 1 $ radius-1)
           nEvs'    = nEvs + if upd then 1 else 0
       pure (radius', nEvs')
  eclasses <- gets (IntMap.toList . _eClass)
  -- forM_ eclasses $ \(_, v) -> (io.print) (Set.size (_eNodes v), Set.size (_parents v))
  paretoFront
  --ft <- gets (_fitRangeDB . _eDB)
  --io . print $ Foldable.toList ft

  where
    numberOfEvalClasses :: Monad m => Int -> EGraphST m Bool
    numberOfEvalClasses nEvs =
      (subtract <$> gets (IntSet.size . _unevaluated . _eDB) <*> gets (IM.size . _eClass))
        >>= \n -> pure (n<nEvs)

    updateIfNothing ec = do
      mf <- getFitness ec
      case mf of
        Nothing -> do
          t <- getBest ec
          (f, p) <- fitnessFunRep x y x_val y_val t
          insertFitness ec f p
          pure True
        Just _ -> pure False

    getBestFitness = do
      bec <- (gets (snd . getGreatest . _fitRangeDB . _eDB) >>= canonical)
      gets (_fitness . _info . (IM.! bec) . _eClass)

    evalRndSubTree :: RndEGraph (Maybe EClassId)
    evalRndSubTree = do ecIds <- gets (IntSet.toList . _unevaluated . _eDB)
                        if not (null ecIds)
                          then do rndId <- rnd $ randomFrom ecIds
                                  Just <$> canonical rndId
                          else pure Nothing


    combineFrom ecs = do
        nt  <- rnd rndNonTerm
        p1  <- rnd (randomFrom ecs)
        p2  <- rnd (randomFrom ecs)
        l1  <- rnd (randomFrom [1..maxSize-2])
        l2  <- rnd (randomFrom [1..(maxSize - l1 - 1)])
        e1  <- randomChildFrom p1 l1
        ml  <- gets (_size . _info . (IM.! e1) . _eClass)
        e2  <- randomChildFrom p2 l2
        case nt of
          Uni Id ()    -> canonical e1
          Uni f ()     -> add myCost (Uni f e1) >>= canonical
          Bin op () () -> do b <- rnd toss
                             if b
                              then add myCost (Bin op e1 e2) >>= canonical
                              else add myCost (Bin op e2 e1) >>= canonical

    getParetoEcsUpTo n = concat <$> (forM [1..maxSize] $ \i -> getBestEcsOfSize  i n)

    getBestEcsOfSize i n = do
      ecs <- getTopECLassWithSize i n
      Prelude.mapM canonical (Prelude.take n ecs)

    getBestEcs p n = do
      ecs  <- getTopECLassThat n p
      --fits <- Prelude.mapM getFitness ecs
      --let sorted = sort $ Prelude.zip (Prelude.map (fmap negate) fits) ecs
      Prelude.mapM canonical (Prelude.take n ecs)

    randomChildFrom ec maxL = do
      p <- rnd toss -- whether to go deeper or return this level
      l <- gets (_size . _info . (IM.! ec) . _eClass )

      if p || l >= maxL
          then do enodes <- gets (_eNodes . (IM.! ec) . _eClass)
                  enode  <- gets (_best . _info . (IM.! ec) . _eClass) -- we should return the best otherwise we may build larger
                  case enode of
                      Uni _ eci     -> randomChildFrom eci maxL
                      Bin _ ecl ecr -> do coin <- rnd toss
                                          if coin
                                            then randomChildFrom ecl maxL
                                            else randomChildFrom ecr maxL
                      _ -> pure ec
          else pure ec

    nonTerms   = [ Bin Add () (), Bin Sub () (), Bin Mul () (), Bin Div () ()
                 , Bin PowerAbs () (),  Uni Recip (), Uni LogAbs (), Uni Exp (), Uni Sin (), Uni SqrtAbs ()]
    rndTerm    = Random.randomFrom terms
    rndNonTerm = Random.randomFrom $ (Uni Id ()) : nonTerms
    rndNonTerm2 = Random.randomFrom nonTerms

    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical

    insertRndExpr :: Int -> RndEGraph EClassId
    insertRndExpr maxSize =
      do grow <- rnd toss
         n <- rnd (randomFrom [3 .. maxSize])
         t <- rnd $ Random.randomTree 2 8 n rndTerm rndNonTerm2 grow
         fromTree myCost t >>= canonical

    insertBestExpr :: RndEGraph EClassId
    insertBestExpr = do --let t =  "t0" / (recip ("t1" - "x0") + powabs "t2" "x0")
                        let t = ((("t0" + (powabs "t0" "x0")) / "t0") * "x0")
                        ecId <- fromTree myCost t >>= canonical
                        (f, p) <- fitnessFunRep x y x_val y_val t
                        insertFitness ecId f p
                        io . putStrLn $ "Best fit global: " <> show f
                        pure ecId
        where powabs l r  = Fix (Bin PowerAbs l r)

    getBestEclassThat p  =
        do ecIds <- getTopECLassThat 1 p -- isValidFitness
           --bestFit <- foldM (\acc -> getFitness >=> (pure . max acc . fromJust)) ((-1.0)/0.0) ecIds
           --ecIds'  <- getEClassesThat (fitnessIs (== Just bestFit))
           Prelude.mapM canonical $ Prelude.take 1 ecIds

    getBestExprWithSize n =
        do ec <- getTopECLassWithSize n 1
           if (not (null ec))
            then do
              bestFit <- getFitness $ head ec
              bestP   <- gets (_theta . _info . (IM.! (head ec)) . _eClass)
              (:[]) . (,bestP) . (,bestFit) <$> getBest (head ec)
            else pure []

    getBestExprThat p  =
        do ec <- getBestEclassThat p
           if (not (null ec))
            then do
              bestFit <- getFitness $ head ec
              (:[]) . (,bestFit) <$> getBest (head ec)
            else pure []

    printAll = do
        ecs <- gets (IM.keys . _eClass)
        forM_ ecs $ \ec ->
            do t <- getBest ec
               f <- gets (_fitness . _info . (IM.! ec) . _eClass)
               io . putStrLn $ showExpr t <> " " <> show f

    paretoFront = go 1 (-1.0/0.0)
      where
        go n f
          | n > maxSize = pure ()
          | otherwise   = do
              ecList <- getBestExprWithSize n
              if (not (null ecList))
                 then do let ((best, mf), mtheta) = head ecList
                             best' = relabelParams best
                         x_tot <- MA.computeAs MA.S <$> (MA.concatOuterM $ Prelude.map MA.toLoadArray [x, x_val])
                         y_tot <- MA.computeAs MA.S <$> (MA.concatOuterM $ Prelude.map MA.toLoadArray [y, y_val])

                         --(fit_tr, theta) <- fitnessFunRep x_tot y_tot x_tot y_tot best'
                         let fit = fromJust mf
                             fit_tr = fit
                             theta = fromJust mtheta
                             fit_te = mse x_te y_te best' theta
                             str_th = intercalate ";" $ Prelude.map show $ MA.toList theta

                         when (fit > f) do
                           io . putStrLn $ showExpr best <> "," <> str_th <> "," <> show (negate fit) <> "," <> show (negate fit_tr) <> "," <> show fit_te
                         go (n+1) (max fit f)
                 else go (n+1) f

    evaluateUnevaluated = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          forM_ ec $ \c -> do
              t <- getBest c
              (f, p) <- fitnessFun x y x_val y_val t
              insertFitness c f p

    evaluateRndUnevaluated = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          c <- rnd . randomFrom $ ec 
          t <- getBest c
          (f, p) <- fitnessFun x y x_val y_val t
          insertFitness c f p
          pure c

while p arg prog = do when (p arg) do arg' <- prog arg
                                      while p arg' prog

                                {-
egraphGP :: SRMatrix -> PVector -> [Fix SRTree] -> Int -> RndEGraph (Fix SRTree, Double)
egraphGP x y terms nEvals = do
    replicateM_ 200 insertRndExpr
    getBestExpr
    runEqSat myCost rewrites 50
    evaluateUnevaluated
    paretoFront
    getBestExpr
  where
    paretoFront = do 
        forM_ [1..10] $ \i ->
            do (best, fit) <- getBestExprThat (evaluated &&& isSizeOf (==i))
               io . putStrLn $ showExpr best <> " " <> show fit 

    evaluateUnevaluated = do 
          ec <- getEClassesThat unevaluated
          forM_ ec $ \c -> do 
              t <- getBest c 
              f <- fitnessFun x y t
              updateFitness f c 
















------------------- GARBAGE CODE -------------------
    go i = do n <- getEClassesThat isValidFitness
              unless (length n >= nEvals)
                do gpStep
                   when (i `mod` 1000 == 0) (getBestExpr >>= (io . print . snd))
                   when (i `mod` 1000000 == 0) $ do
                     n <- gets (IM.size . _eClass)
                     --io $ putStrLn ("before: " <> show n)
                     applyMergeOnlyDftl myCost
                     n1 <- gets (IM.size . _eClass)
                     when (n1 < n) $ io $ print (n,n1)
                     --io $ putStrLn ("after: " <> show n1)
                   go (i+1)

    rndTerm    = Random.randomFrom terms
    rndNonTerm = Random.randomFrom [Bin Add () (), Bin Sub () (), Bin Mul () (), Bin Div () ()
                                   , Bin PowerAbs () (),  Uni Recip ()]

    getBestExpr :: RndEGraph (Fix SRTree, Double) 
    getBestExpr = do ecIds <- getEClassesThat evaluated -- isValidFitness
                     nc    <- gets (IM.size . _eClass)
                     io . putStrLn $ "Evaluated expressions: " <> show (length ecIds) <> " / " <> show nc
                     bestFit <- foldM (\acc -> getFitness >=> (pure . max acc . fromJust)) ((-1.0)/0.0) ecIds
                     ecIds'  <- getEClassesThat (fitnessIs (== Just bestFit))
                     (,bestFit) <$> getBest (head ecIds')

    getBestExprThat p  = 
        do ecIds <- getEClassesThat p -- isValidFitness
           nc    <- gets (IM.size . _eClass)
           bestFit <- foldM (\acc -> getFitness >=> (pure . max acc . fromJust)) ((-1.0)/0.0) ecIds
           ecIds'  <- getEClassesThat (fitnessIs (== Just bestFit))
           (,bestFit) <$> getBest (head ecIds')

    insertRndExpr :: RndEGraph () 
    insertRndExpr = do grow <- rnd toss
                       t <- rnd $ Random.randomTree 2 6 10 rndTerm rndNonTerm grow
                       f <- fitnessFun x y t
                       ecId <- fromTree myCost t >>= canonical
                       -- io $ print ('i', showExpr t, f)
                       updateFitness f ecId

    evalRndSubTree :: RndEGraph ()
    evalRndSubTree = do ecIds <- getEClassesThat unevaluated
                        unless (null ecIds) do
                            rndId <- rnd $ randomFrom ecIds
                            rndId' <- canonical rndId 
                            t     <- getBest rndId'
                            f <- fitnessFun x y t
                            -- io $ print ('e', showExpr t, f)
                            updateFitness f rndId'

    tournament :: Int -> [EClassId] -> RndEGraph EClassId
    tournament n ecIds = do 
        (c0:cs) <- replicateM n (rnd (randomFrom ecIds))
        f0 <- gets (_fitness . _info . (IM.! c0) . _eClass)
        snd <$> foldM (\(facc, acc) c -> gets (_fitness . _info . (IM.! c) . _eClass)
                                           >>= \f -> if f > facc
                                                        then pure (f, c)
                                                        else pure (facc, acc)) (f0, c0) cs

    insertRndParent :: RndEGraph ()
    insertRndParent = do nt    <- rnd rndNonTerm
                         meId <- case nt of
                                  Uni f  _   -> do ecIds <- getEClassesThat (isSizeOf (<10) &&& isValidFitness &&& funDoesNotExistWith nt)
                                                   if null ecIds
                                                      then pure Nothing 
                                                      else do rndId <- tournament 5 ecIds
                                                              sz <- getSize rndId
                                                              if sz < 10 
                                                                 then do node <- canonize (Uni f rndId)
                                                                         Just <$> add myCost node
                                                                 else pure Nothing
                                  Bin op _ _ -> do ecIds <- getEClassesThat (isSizeOf (<9) &&& isValidFitness)
                                                   if null ecIds
                                                      then pure Nothing
                                                      else do rndIdLeft <- rnd $ randomFrom ecIds
                                                              sz1 <- getSize rndIdLeft
                                                              ecIds' <- getEClassesThat (isSizeOf (< (10 - sz1)) &&& isValidFitness &&& opDoesNotExistWith nt rndIdLeft)
                                                              if null ecIds'
                                                                 then pure Nothing
                                                                 else do rndIdRight <- rnd $ randomFrom ecIds'
                                                                         rndIdRight <- tournament 5 ecIds'
                                                                         sz2 <- getSize rndIdRight
                                                                         if sz1 + sz2 < 10
                                                                           then Just <$> (canonize (Bin op rndIdLeft rndIdRight)
                                                                                  >>= add myCost)
                                                                           else pure Nothing
                         when (isJust meId) do
                           let eId = fromJust meId
                           eId' <- canonical eId
                           curFit <- gets (_fitness . _info . (IM.! eId') . _eClass)
                           when (isNothing curFit) do
                               t <- getBest eId'
                               f <- fitnessFun x y t
                               updateFitness f eId'
                               -- io $ print ('p', showExpr t, f)

    gpStep :: RndEGraph () 
    gpStep = do choice <- rnd $ randomFrom [2,2,3,3,3]
                if | choice == 1 -> insertRndExpr
                   | choice == 2 -> insertRndParent
                   | otherwise   -> evalRndSubTree
                rebuild myCost
                -}
data Args = Args
  { dataset  :: String,
    gens     :: Int,
    _alg     :: Alg,
    _maxSize :: Int,
    _split   :: Int
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
       <> help "k-split ratio training-test")

chunksOf :: Int -> [e] -> [[e]]
chunksOf i ls = Prelude.map (Prelude.take i) (build (splitter ls))
 where
  splitter :: [e] -> ([e] -> a -> a) -> a -> a
  splitter [] _ n = n
  splitter l c n = l `c` splitter (Prelude.drop i l) c n
  build :: ((a -> [a] -> [a]) -> [a] -> [a]) -> [a]
  build g = g (:) []

splitData :: SRMatrix -> PVector -> Int -> State StdGen (SRMatrix, SRMatrix, PVector, PVector)
splitData x y k = do if k == 1
                         then pure (x, x, y, y)
                         else do
                          ixs' <- (state . shuffle) [0 .. sz-1]
                          let ixs = chunksOf k ixs' -- $ sortOn (\ix -> y MA.! ix) [0 .. sz-1]
                          --ixs <- forM sortedIxs $ \is -> state (shuffle is)
                          let xl     = MA.toLists x :: [MA.ListItem MA.Ix2 Double]
                              x_tr   = MA.fromLists' comp_x [xl !! ix | ixs_i <- ixs, ix <- Prelude.tail ixs_i]
                              x_te   = MA.fromLists' comp_x [xl !! ix | ixs_i <- ixs, let ix = Prelude.head ixs_i]
                              y_tr   = MA.fromList comp_y [y MA.! ix | ixs_i <- ixs, ix <- Prelude.tail ixs_i]
                              y_te   = MA.fromList comp_y [y MA.! ix | ixs_i <- ixs, let ix = Prelude.head ixs_i]

                                                                                          {-
                          ixs <- state (shuffle [0 .. sz-1])
                          let ixs_tr = sort $ Prelude.take qty_tr ixs
                              ixs_te = sort $ Prelude.drop qty_tr ixs

                              x_tr   = MA.fromLists' comp_x [xl !! ix | ix <- ixs_tr]
                              x_te   = MA.fromLists' comp_x [xl !! ix | ix <- ixs_te]
                              y_tr   = MA.fromList comp_y [y MA.! ix | ix <- ixs_tr]
                              y_te   = MA.fromList comp_y [y MA.! ix | ix <- ixs_te]
                              -}
                          pure (x_tr, x_te, y_tr, y_te)
  where
    (MA.Sz sz) = MA.size y
    --qty_tr     = round (thr * fromIntegral sz)
    --qty_te     = sz - qty_tr
    comp_x     = MA.getComp x
    comp_y     = MA.getComp y

main :: IO ()
main = do
  --args <- pure (Args "nikuradse_2.csv" 100) -- execParser opts
  args <- execParser opts
  g <- getStdGen
  ((x, y, _, _), _, _) <- loadDataset (dataset args) True
  let ((x', x_te, y', y_te),g') = runState (splitData x y $ _split args) g
      ((x_tr, x_val, y_tr, y_val),g'') = runState (splitData x' y' 2) g'
  let (Sz2 _ nFeats) = MA.size x
      terms          = [var ix | ix <- [0 .. nFeats-1]] <> [param 0] -- [param ix | ix <- [0 .. 5]]
      alg            = evalStateT (egraphSearch (_alg args) x_tr y_tr x_val y_val x_te y_te terms (gens args) (_maxSize args)) emptyGraph
  --(bestExpr, fit) <- evalStateT alg g
  --printExpr bestExpr
  --print fit
  evalStateT alg g''

  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )
