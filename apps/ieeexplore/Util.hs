{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}

module Util where

import qualified Data.Map.Strict as Map
import Data.Massiv.Array as MA hiding (forM_, forM)
import Data.SRTree
import Data.SRTree.Eval
import Algorithm.SRTree.Opt
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Build
import Algorithm.EqSat.Info

import Algorithm.SRTree.NonlinearOpt
import System.Random
import Random
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.ModelSelection
import Data.SRTree.Print
--import Algorithm.SRTree.ModelSelection
--import Algorithm.SRTree.Opt
import qualified Data.IntMap.Strict as IM
import Control.Monad.State.Strict
import Control.Monad ( when, replicateM, forM, forM_ )
import Data.Maybe ( fromJust )
import Data.List ( maximumBy, intercalate )
import Data.Function ( on )
import List.Shuffle ( shuffle )
import Data.List.Split ( splitOn )
import Data.Char ( toLower )
import qualified Data.IntSet as IntSet
import Data.SRTree.Datasets
import Algorithm.EqSat.Queries
import Algorithm.EqSat.DB
import Data.List (nub)
import System.Console.Repline hiding (Repl)
import Text.Printf
import Text.Layout.Table hiding (top)
import Text.Layout.Table.Cell.Formatted
import Text.Layout.Table.Cell
import System.Console.ANSI.Codes


type RndEGraph = StateT EGraph IO
type DataSet = (SRMatrix, PVector, Maybe PVector)
data Info = Info {_training :: DataSet, _test :: DataSet, _dist :: Distribution}
type Repl = HaskelineT (StateT EGraph IO)

csvHeader :: String
csvHeader = "id,Expression,theta,size,MSE_train,MSE_val,MSE_test,R2_train,R2_val,R2_test,nll_train,nll_val,nll_test,mdl_train,mdl_val,mdl_test"

io :: IO a -> Repl a
io = lift . lift
{-# INLINE io #-}
egraph :: RndEGraph a -> Repl a
egraph = lift

myCost :: SRTree Int -> Int
myCost (Var _)     = 1
myCost (Const _)   = 1
myCost (Param _)   = 1
myCost (Bin _ l r) = 2 + l + r
myCost (Uni _ t)   = 3 + t

fitnessFun :: Int -> Distribution -> DataSet -> DataSet -> Fix SRTree -> PVector -> (Double, PVector)
fitnessFun nIter distribution (x, y, mYErr) (x_val, y_val, mYErr_val) _tree thetaOrig =
  if isNaN val || isNaN tr
    then (-(1/0), theta) -- infinity
    else (min tr val, theta)
  where
    tree          = relabelParams _tree
    nParams       = countParams tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    (theta, _, _) = minimizeNLL' VAR1 distribution mYErr nIter x y tree thetaOrig
    evalF a b c   = negate $ nll distribution c a b tree $ if nParams == 0 then thetaOrig else theta
    tr            = evalF x y mYErr
    val           = evalF x_val y_val mYErr_val

{-# INLINE fitnessFun #-}

fitnessFunRep :: Int -> Distribution -> DataSet -> DataSet -> Fix SRTree -> RndEGraph (Double, PVector)
fitnessFunRep nIter distribution dataTrain dataVal _tree = do
    let tree = relabelParams _tree
        nParams = countParams tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0

    thetaOrigs <- lift (randomVec nParams)
    lift $ print thetaOrigs
    pure (fitnessFun nIter distribution dataTrain dataVal _tree thetaOrigs)
{-# INLINE fitnessFunRep #-}


-- helper query functions
-- TODO: move to egraph lib
getFitness :: EClassId -> RndEGraph (Maybe Double)
getFitness c = gets (_fitness . _info . (IM.! c) . _eClass)
{-# INLINE getFitness #-}
getTheta :: EClassId -> RndEGraph (Maybe PVector)
getTheta c = gets (_theta . _info . (IM.! c) . _eClass)
{-# INLINE getTheta #-}
getSize :: EClassId -> RndEGraph Int
getSize c = gets (_size . _info . (IM.! c) . _eClass)
{-# INLINE getSize #-}
isSizeOf :: (Int -> Bool) -> EClass -> Bool
isSizeOf p = p . _size . _info
{-# INLINE isSizeOf #-}

getBestFitness :: RndEGraph (Maybe Double)
getBestFitness = do
    bec <- (gets (snd . getGreatest . _fitRangeDB . _eDB) >>= canonical)
    gets (_fitness . _info . (IM.! bec) . _eClass)

getTrain :: ((a, b1, c1, d1), (c2, b2), c3, d2) -> (a, b1, c2)
getTrain ((a, b, _, _), (c, _), _, _) = (a,b,c)

getX :: DataSet -> SRMatrix
getX (a, _, _) = a

getTarget :: DataSet -> PVector
getTarget (_, b, _) = b

getError :: DataSet -> Maybe PVector
getError (_, _, c) = c

loadTrainingOnly fname b = getTrain <$> loadDataset fname b

printExpr :: DataSet -> DataSet -> Distribution -> EClassId -> RndEGraph ()
printExpr dataTrain dataTest distribution ec = do
        theta <- fromJust <$> getTheta ec

        bestExpr <- getBestExpr ec
        let (x, y, mYErr) = dataTrain
            (x_te, y_te, mYErr_te) = dataTest
            best'     = relabelParams bestExpr
            expr      = paramsToConst (MA.toList theta) best'
            mse_train = mse x y best' theta
            mse_te    = mse x_te y_te best' theta
            r2_train  = r2 x y best' theta
            r2_te     = r2 x_te y_te best' theta
            nll_train  = nll distribution mYErr x y best' theta
            nll_te     = nll distribution mYErr_te x_te y_te best' theta
            mdl_train  = mdl distribution mYErr x y theta best'
            mdl_te     = mdl distribution mYErr_te x_te y_te theta best'
            thetaStr   = intercalate ", " $ Prelude.map show (MA.toList theta)
        lift . putStr $ "Evaluation metrics for expression (" <> (show ec) <> "): "
        lift . putStr $ setSGRCode [SetConsoleIntensity BoldIntensity]
        lift . putStrLn $ showExpr bestExpr
        lift . putStr $ setSGRCode [Reset]
        lift . putStrLn $ "# of nodes\t" <> show (countNodes $ convertProtectedOps expr)
        lift . putStrLn $ "params:\t[" <> thetaStr <> "]"

        let rows = [ rowG ["MSE", printf "%.4f" mse_train, printf "%.4f" mse_te]
                   , rowG ["R^2", printf "%.4f" r2_train, printf "%.4f" r2_te]
                   , rowG ["nll", printf "%.4f" nll_train, printf "%.4f" nll_te]
                   , rowG ["DL", printf "%.4f" mdl_train, printf "%.4f" mdl_te]
                   ]
            columnsReport = [def, numCol, numCol]
            headerReport = titlesH $ Prelude.map bold ["Metric", "Training", "Test"]
        lift . putStrLn $ tableString (columnHeaderTableS columnsReport unicodeS headerReport rows)

printsimpleExpr eid = do t   <- egraph $ getBestExpr eid
                         fit <- egraph $ getFitness eid
                         sz  <- egraph $ getSize eid
                         p   <- egraph $ getTheta eid
                         let fit' = case fit of
                                      Nothing -> "--"
                                      Just f  -> printf "%.4f" f
                             p' = case p of
                                    Nothing -> "--"
                                    Just ps -> "[" <> intercalate ", " (Prelude.map (printf "%.4f") (MA.toList ps)) <> "]"

                         pure $ colsAllG center [[show eid], justifyText 50 $ showExpr t, [fit'], justifyText 50 p', [show sz]]

printCounts (pat, cnt) = do
  let spat = showPat pat
  pure $ colsAllG center [justifyText 50 spat, [show cnt]]
  where
    showPat (Fixed (Var ix)) = 'x' : show ix
    showPat (Fixed (Param ix)) = 't' : show ix
    showPat (Fixed (Const x))  = show x
    showPat (Fixed (Bin op l r)) = concat ["(", showPat l, " ", showOp op, " ", showPat r, ")"]
    showPat (Fixed (Uni f t)) = concat [show f, "(", showPat t, ")"]
    showPat (VarPat ix) = 'v' : show (fromEnum ix-65)

printSimpleMultiExprs eids = do rows <- forM (nub eids) printsimpleExpr
                                io.putStrLn $ tableString (columnHeaderTableS columns unicodeS headerSimple rows)

printMultiCounts cnts = do rows <- forM cnts printCounts
                           io.putStrLn $ tableString (columnHeaderTableS [fixedLeftCol 50, numCol] unicodeS headerCount rows)

bold s = formatted (setSGRCode [SetConsoleIntensity BoldIntensity]) (plain s) (setSGRCode [Reset])

headerSimple :: HeaderSpec LineStyle (Formatted String)
headerSimple = titlesH $ Prelude.map (bold) ["Id", "Expression", "Fitness", "Parameters", "Size"]
columns = [numCol, fixedLeftCol 50, numCol, fixedLeftCol 50, numCol]
headerCount :: HeaderSpec LineStyle (Formatted String)
headerCount = titlesH $ Prelude.map bold ["Pattern", "Count"]

-- RndEGraph utils
-- fitFun fitnessFunRep rep iter distribution x y mYErr x_val y_val mYErr_val
insertExpr :: Fix SRTree -> (Fix SRTree -> RndEGraph (Double, PVector)) -> RndEGraph EClassId
insertExpr t fitFun = do
    ecId <- fromTree myCost t >>= canonical
    (f, p) <- fitFun t
    insertFitness ecId f p
    pure ecId
  where powabs l r  = Fix (Bin PowerAbs l r)

updateIfNothing fitFun ec = do
      mf <- getFitness ec
      case mf of
        Nothing -> do
          t <- getBestExpr ec
          (f, p) <- fitFun t
          insertFitness ec f p
          pure True
        Just _ -> pure False

getParetoEcsUpTo b n maxSize = concat <$> forM [1..maxSize] (\i -> getTopEClassWithSize b i n)

getBestExprWithSize n =
        do ec <- getTopFitEClassWithSize n 1 >>= traverse canonical
           if (not (null ec))
            then do
              bestFit <- getFitness $ head ec
              bestP   <- gets (_theta . _info . (IM.! (head ec)) . _eClass)
              (:[]) . (,bestP) . (,bestFit) . (,ec) <$> getBestExpr (head ec)
            else pure []

printBest :: (Int -> EClassId -> RndEGraph ()) -> RndEGraph ()
printBest printExprFun = do
      bec <- gets (snd . getGreatest . _fitRangeDB . _eDB) >>= canonical
      printExprFun 0 bec

paretoFront :: Int -> (Int -> EClassId -> RndEGraph ()) -> RndEGraph ()
paretoFront maxSize printExprFun = go 1 0 (-(1.0/0.0))
    where
    go :: Int -> Int -> Double -> RndEGraph ()
    go n ix f
        | n > maxSize = pure ()
        | otherwise   = do
            ecList <- getBestExprWithSize n
            if not (null ecList)
                then do let (((_, ec), mf), _) = head ecList
                            improved = fromJust mf > f
                        ec' <- traverse canonical ec
                        when improved $ printExprFun ix (head ec')
                        go (n+1) (ix + if improved then 1 else 0) (max f (fromJust mf))
                else go (n+1) ix f

evaluateUnevaluated fitFun = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          forM_ ec $ \c -> do
              t <- getBestExpr c
              (f, p) <- fitFun t
              insertFitness c f p

fillDL dist (x, y, mYErr) = do
  ecs <- getAllEvaluatedEClasses
  forM_ ecs $ \ec -> do
    theta <- fromJust <$> getTheta ec
    bestExpr <- relabelParams <$> getBestExpr ec
    let mdl_train  = mdl dist mYErr x y theta bestExpr
    insertDL ec mdl_train
