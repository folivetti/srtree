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
--import Algorithm.SRTree.ModelSelection
--import Algorithm.SRTree.Opt
import qualified Data.IntMap.Strict as IM
import Control.Monad.State.Strict
import Control.Monad ( when, replicateM, forM, forM_ )
import Data.Maybe ( fromJust )
import Data.List ( maximumBy )
import Data.Function ( on )
import List.Shuffle ( shuffle )
import Data.List.Split ( splitOn )
import Data.Char ( toLower )
import qualified Data.IntSet as IntSet
import Data.SRTree.Datasets
import Algorithm.EqSat.Queries

type RndEGraph a = EGraphST (StateT StdGen IO) a
type DataSet = (SRMatrix, PVector, Maybe PVector)

csvHeader :: String
csvHeader = "id,Expression,theta,size,MSE_train,MSE_val,MSE_test,R2_train,R2_val,R2_test,nll_train,nll_val,nll_test,mdl_train,mdl_val,mdl_test"

io :: IO a -> RndEGraph a
io = lift . lift
{-# INLINE io #-}
rnd :: StateT StdGen IO a -> RndEGraph a
rnd = lift
{-# INLINE rnd #-}

myCost :: SRTree Int -> Int
myCost (Var _)     = 1
myCost (Const _)   = 1
myCost (Param _)   = 1
myCost (Bin _ l r) = 2 + l + r
myCost (Uni _ t)   = 3 + t

while :: Monad f => (t -> Bool) -> t -> (t -> f t) -> f ()
while p arg prog = do when (p arg) do arg' <- prog arg
                                      while p arg' prog

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

fitnessFunRep :: Int -> Int -> Distribution -> DataSet -> DataSet -> Fix SRTree -> RndEGraph (Double, PVector)
fitnessFunRep nRep nIter distribution dataTrain dataVal _tree = do
    let tree = relabelParams _tree
        nParams = countParams tree + if distribution == ROXY then 3 else if distribution == Gaussian then 1 else 0
    thetaOrigs <- replicateM nRep (rnd $ randomVec nParams)
    let fits = Prelude.map (fitnessFun nIter distribution dataTrain dataVal _tree) thetaOrigs
    pure (maximumBy (compare `on` fst) fits)
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

-- TODO: move to dataset lib
chunksOf :: Int -> [e] -> [[e]]
chunksOf i ls = Prelude.map (Prelude.take i) (build (splitter ls))
 where
  splitter :: [e] -> ([e] -> a -> a) -> a -> a
  splitter [] _ n = n
  splitter l c n = l `c` splitter (Prelude.drop i l) c n
  build :: ((a -> [a] -> [a]) -> [a] -> [a]) -> [a]
  build g = g (:) []

splitData :: DataSet ->Int -> State StdGen (DataSet, DataSet)
splitData (x, y, mYErr) k = do
  if k == 1
    then pure ((x, y, mYErr), (x, y, mYErr))
    else do
      ixs' <- (state . shuffle) [0 .. sz-1]
      let ixs = chunksOf k ixs'

      let (x_tr, x_te) = getX ixs x
          (y_tr, y_te) = getY ixs y
          mY = fmap (getY ixs) mYErr
          (y_err_tr, y_err_te) = (fmap fst mY, fmap snd mY)
      pure ((x_tr, y_tr, y_err_tr), (x_te, y_te, y_err_te))
  where
    (MA.Sz sz) = MA.size y
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

getTrain :: ((a, b1, c1, d1), (c2, b2), c3, d2) -> (a, b1, c2)
getTrain ((a, b, _, _), (c, _), _, _) = (a,b,c)

getX :: DataSet -> SRMatrix
getX (a, _, _) = a

getTarget :: DataSet -> PVector
getTarget (_, b, _) = b

getError :: DataSet -> Maybe PVector
getError (_, _, c) = c

loadTrainingOnly fname b = getTrain <$> loadDataset fname b

parseNonTerms :: String -> [SRTree ()]
parseNonTerms = Prelude.map toNonTerm . splitOn ","
  where
    binTerms = Map.fromList [ (Prelude.map toLower (show op), op) | op <- [Add .. AQ]]
    uniTerms = Map.fromList [ (Prelude.map toLower (show f), f) | f <- [Abs .. Cube]]
    toNonTerm xs' = let xs = Prelude.map toLower xs'
                    in case binTerms Map.!? xs of
                          Just op -> Bin op () ()
                          Nothing -> case uniTerms Map.!? xs of
                                          Just f -> Uni f ()
                                          Nothing -> error $ "invalid non-terminal " <> show xs

-- RndEGraph utils
-- fitFun fitnessFunRep rep iter distribution x y mYErr x_val y_val mYErr_val
insertExpr :: Fix SRTree -> (Fix SRTree -> RndEGraph (Double, PVector)) -> RndEGraph EClassId
insertExpr t fitFun = do
    ecId <- fromTree myCost t >>= canonical
    (f, p) <- fitFun t
    insertFitness ecId f p
    io . putStrLn $ "Best fit global: " <> show f
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

pickRndSubTree :: RndEGraph (Maybe EClassId)
pickRndSubTree = do ecIds <- gets (IntSet.toList . _unevaluated . _eDB)
                    if not (null ecIds)
                          then do rndId' <- rnd $ randomFrom ecIds
                                  rndId  <- canonical rndId'
                                  constType <- gets (_consts . _info . (IM.! rndId) . _eClass)
                                  case constType of
                                    NotConst -> pure $ Just rndId
                                    _        -> pure Nothing
                          else pure Nothing

getParetoEcsUpTo n maxSize = concat <$> forM [1..maxSize] (\i -> getTopECLassWithSize i n)

getBestExprWithSize n =
        do ec <- getTopECLassWithSize n 1 >>= traverse canonical
           if (not (null ec))
            then do
              bestFit <- getFitness $ head ec
              bestP   <- gets (_theta . _info . (IM.! (head ec)) . _eClass)
              pure [(head ec, bestFit)]
            else pure []

insertRndExpr maxSize rndTerm rndNonTerm =
      do grow <- rnd toss
         n <- rnd (randomFrom [if maxSize > 4 then 4 else 1 .. maxSize])
         t <- rnd $ Random.randomTree 3 8 n rndTerm rndNonTerm grow
         fromTree myCost t >>= canonical

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
                then do let (ec, mf) = head ecList
                            improved = fromJust mf > f
                        ec' <- canonical ec
                        when improved $ printExprFun ix ec'
                        go (n+1) (ix + if improved then 1 else 0) (max f (fromJust mf))
                else go (n+1) ix f

evaluateUnevaluated fitFun = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          forM_ ec $ \c -> do
              t <- getBestExpr c
              (f, p) <- fitFun t
              insertFitness c f p

evaluateRndUnevaluated fitFun = do
          ec <- gets (IntSet.toList . _unevaluated . _eDB)
          c <- rnd . randomFrom $ ec
          t <- getBestExpr c
          (f, p) <- fitFun t
          insertFitness c f p
          pure c
