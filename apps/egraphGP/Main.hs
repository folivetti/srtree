{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}
{-# LANGUAGE  MultiWayIf #-}
module Main where 

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Simplify
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.Opt
import Control.Lens (element, makeLenses, over, (&), (+~), (-~), (.~), (^.))
import Control.Monad (foldM, forM_, when, unless, filterM, (>=>), replicateM)
import Control.Monad.State
import qualified Data.IntMap as IM
import Data.Massiv.Array as MA hiding (forM_)
import Data.Maybe (fromJust, isNothing, isJust)
import Data.SRTree
import Data.SRTree.Datasets
import Data.SRTree.Eval
import Data.SRTree.Random (randomTree)
import Data.SRTree.Print
import Options.Applicative as Opt hiding (Const)
import Random
import System.Random

import Debug.Trace

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

fitnessFun :: SRMatrix -> PVector -> Fix SRTree -> RndEGraph Double
fitnessFun x y _tree = do
    let tree         = relabelParams _tree
        nParams      = countParams tree
    thetaOrig <- rnd $ randomVec nParams --   = MA.replicate Seq nParams 1.0
    let (theta, fit) = minimizeNLL Gaussian Nothing 5 x y tree thetaOrig
    pure . negate . mse x y tree $ if nParams == 0 then thetaOrig else theta
{-# INLINE fitnessFun #-}

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
unevaluated = fitnessIs isNothing
{-# INLINE unevaluated #-}

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

egraphGP :: SRMatrix -> PVector -> [Fix SRTree] -> Int -> RndEGraph (Fix SRTree, Double)
egraphGP x y terms nEvals = do
    insertRndExpr
    go 1
    getBestExpr
  where

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
    rndNonTerm = Random.randomFrom [Bin Add () (), Bin Sub () (), Bin Mul () (), Bin Div () (), Bin PowerAbs () (),  Uni Recip ()]

    getBestExpr :: RndEGraph (Fix SRTree, Double) 
    getBestExpr = do ecIds <- getEClassesThat isValidFitness
                     nc    <- gets (IM.size . _eClass)
                     io . putStrLn $ "Evaluated expressions: " <> show (length ecIds) <> " / " <> show nc
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
    gpStep = do choice <- rnd $ randomFrom [1,1,2,2,3,3,3]
                if | choice == 1 -> insertRndExpr
                   | choice == 2 -> insertRndParent
                   | otherwise   -> evalRndSubTree
                rebuild myCost

data Args = Args
  { dataset :: String,
    gens    :: Int
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

main :: IO ()
main = do
  --args <- pure (Args "nikuradse_2.csv" 100) -- execParser opts
  args <- execParser opts
  g <- getStdGen
  ((x, y, _, _), _, _) <- loadDataset (dataset args) True
  let (Sz2 _ nFeats) = MA.size x
      terms          = [var ix | ix <- [0 .. nFeats-1]] <> [param 0] -- [param ix | ix <- [0 .. 5]]
      alg            = evalStateT (egraphGP x y terms (gens args)) emptyGraph
  (bestExpr, fit) <- evalStateT alg g 
  printExpr bestExpr
  print fit
  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )
