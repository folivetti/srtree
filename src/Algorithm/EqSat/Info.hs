-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.EqSat.Info
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Functions related to info/data calculation in Equality Graph data structure
-- Heavily based on hegg (https://github.com/alt-romes/hegg by alt-romes)
--
-----------------------------------------------------------------------------

module Algorithm.EqSat.Info where

import Control.Lens ( over )
import Control.Monad --(forM, forM_, when, foldM, void)
import Control.Monad.State
import Data.AEq (AEq ((~==)))
import Data.IntMap (IntMap) -- , delete, empty, insert, toList)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.SRTree
import Data.SRTree.Eval (evalFun, evalOp, PVector)
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.IntSet as IntSet
import Algorithm.EqSat.Egraph
import Data.AEq (AEq ((~==)))
import Algorithm.EqSat.Queries
import Data.Maybe
import qualified Data.Set as TrueSet

import Debug.Trace

-- * Data related functions 

-- | join data from two e-classes
-- TODO: instead of folding, just do not apply rules
-- list of values instead of single value
joinData :: EClassData -> EClassData -> EClassData
joinData (EData c1 b1 cn1 fit1 p1 sz1) (EData c2 b2 cn2 fit2 p2 sz2) =
  EData (min c1 c2) b (combineConsts cn1 cn2) (minMaybe fit1 fit2) (bestParam p1 p2 fit1 fit2) (min sz1 sz2)
  where
    minMaybe Nothing x = x
    minMaybe x Nothing = x
    minMaybe x y       = min x y

    bestParam Nothing x _ _ = x
    bestParam x Nothing _ _ = x
    bestParam x y (Just f1) (Just f2) = if f1 < f2 then x else y

    b = if c1 <= c2 then b1 else b2
    combineConsts (ConstVal x) (ConstVal y)
      | abs (x-y) < 1e-7   = ConstVal $ (x+y)/2
      | isNaN x || isInfinite x = ConstVal y 
      | isNaN y || isInfinite y = ConstVal x
      | isNaN x && isNaN y = ConstVal x
      | x ~== y = ConstVal $ (x+y)/2
      | abs (x / y) < 1 + 1e-6 || abs (y / x) < 1 + 1e-6 = ConstVal $ min x y
      | isInfinite x && isInfinite y = ConstVal x
      | isInfinite x && isNaN y = ConstVal y
      | isNaN x && isInfinite y = ConstVal x
      | otherwise          = error $ "Combining different values: " <> show x <> " " <> show y <> " " <> show (x/y)
    combineConsts (ParamIx ix) (ParamIx iy) = ParamIx (min ix iy)
    combineConsts NotConst x = x
    combineConsts x NotConst = x
    combineConsts x y = error (show x <> " " <> show y)

-- | Calculate e-node data (constant values and cost)
makeAnalysis :: Monad m => CostFun -> ENode -> EGraphST m EClassData
makeAnalysis costFun enode =
  do consts <- calculateConsts enode
     enode' <- canonize enode
     cost   <- calculateCost costFun enode'
     sz <- sum <$> mapM (\ecId -> gets (_size . _info . (IntMap.! ecId) . _eClass)) (childrenOf enode')
     pure $ EData cost enode' consts Nothing Nothing (sz+1)

getChildrenMinHeight :: Monad m => ENode -> EGraphST m Int
getChildrenMinHeight enode = do
  let children = childrenOf enode
      minimum' [] = 0
      minimum' xs = minimum xs
  minimum' <$> mapM (\ec -> gets (_height . (IntMap.! ec) . _eClass)) children

-- | update the heights of each e-class
-- won't work if there's no root
calculateHeights :: Monad m => EGraphST m ()
calculateHeights =
  do queue   <- findRootClasses
     classes <- gets (Prelude.map fst . IntMap.toList . _eClass)
     let nClasses = length classes
     forM_ classes (setHeight nClasses) -- set all heights to max possible height (number of e-classes)
     forM_ queue (setHeight 0)          -- set root e-classes height to zero
     go queue (TrueSet.fromList queue) 1    -- next height is 1
  where
    setHeight x eId' =
      do eId <- canonical eId'
         ec <- getEClass eId
         let ec' = over height (const x) ec
         modify' $ over eClass (IntMap.insert eId ec')

    setMinHeight x eId' = -- set height to the minimum between current and x
      do eId <- canonical eId'
         h <- _height <$> getEClass eId
         setHeight (min h x) eId

    getChildrenEC :: Monad m => EClassId -> EGraphST m [EClassId]
    getChildrenEC ec' = do ec <- canonical ec'
                           gets (concatMap childrenOf' . _eNodes . (IntMap.! ec) . _eClass)

    childrenOf' (_, -1, -1, _) = []
    childrenOf' (_, e1, -1, _) = [e1]
    childrenOf' (_, e1, e2, _) = [e1, e2]

    go [] _    _ = pure ()
    go qs tabu h =
      do childrenOf <- (TrueSet.\\ tabu) . TrueSet.fromList . concat <$> forM qs getChildrenEC -- rerieve all unvisited children
         let childrenL = TrueSet.toList childrenOf
         forM_ childrenL (setMinHeight h) -- set the height of the children as the minimum between current and h
         go childrenL (TrueSet.union tabu childrenOf) (h+1) -- move one breadth search style

-- | calculates the cost of a node
calculateCost :: Monad m => CostFun -> SRTree EClassId -> EGraphST m Cost
calculateCost f t =
  do let cs = childrenOf t
     costs <- traverse (fmap (_cost . _info) . getEClass) cs
     pure . f $ replaceChildren costs t

-- | check whether an e-node evaluates to a const
calculateConsts :: Monad m => SRTree EClassId -> EGraphST m Consts
calculateConsts t =
  do let cs = childrenOf t
     eg <- get
     consts <- traverse (fmap (_consts . _info) . getEClass) cs
     case combineConsts $ replaceChildren consts t of
          ConstVal x | isNaN x -> pure (ConstVal x)
          a -> pure a

combineConsts :: SRTree Consts -> Consts
combineConsts (Const x)    = ConstVal x
combineConsts (Param ix)   = ParamIx ix
combineConsts (Var _)      = NotConst
combineConsts (Uni f t)    = case t of
                              ConstVal x -> ConstVal $ evalFun f x
                              _          -> t
combineConsts (Bin op l r) = evalOp' l r
  where
    evalOp' (ParamIx ix) (ParamIx iy) = ParamIx (min ix iy)
    evalOp' (ConstVal x) (ConstVal y) = ConstVal $ evalOp op x y
    evalOp' _            _            = NotConst

insertFitness :: Monad m => EClassId -> Double -> PVector -> EGraphST m ()
insertFitness eId fit params = do
  ec <- gets ((IntMap.! eId) . _eClass)
  let oldFit  = _fitness . _info $ ec
      newInfo = (_info ec){_fitness = Just fit, _theta = Just params}
      newEc   = ec{_info = newInfo}
  modify' $ over eClass (IntMap.insert eId newEc)
  if (isNothing oldFit)
    then modify' $ over (eDB . unevaluated) (IntSet.delete eId)
                 . over (eDB . fitRangeDB) (insertRange eId fit)
    else modify' $ over (eDB . fitRangeDB) (insertRange eId fit . removeRange eId (fromJust oldFit))
