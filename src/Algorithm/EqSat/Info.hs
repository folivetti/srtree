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
import Control.Monad
import Control.Monad.State
import Data.AEq (AEq ((~==)))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.SRTree
import Data.SRTree.Eval (evalFun, evalOp, Target)
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.Set as RangeSet
import qualified Data.IntSet as IntSet
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Queries

import qualified Data.Set as TrueSet

-- * Data related functions 

-- | join data from two e-classes
-- TODO: instead of folding, just do not apply rules
-- list of values instead of single value
joinData :: EClassData -> EClassData -> EClassData
joinData (EData c1 b1 cn1 fit1 dl1 p1 sz1) (EData c2 b2 cn2 fit2 dl2 p2 sz2) =
  --EData (min c1 c2) b (combineConsts cn1 cn2) (minMaybe fit1 fit2) (bestParam p1 p2 fit1 fit2) (min sz1 sz2)
  EData (min c1 c2) (choose b1 b2) (choose cn1 cn2) (maxMaybe fit1 fit2) (choose dl1 dl2) (choose p1 p2) (choose sz1 sz2)
  where
    isFst = c1 <= c2
    choose x y = if isFst then x else y
    chooseF x y = if maxIsFst then x else y

    maxIsFst = case (fit1, fit2) of
                 (Nothing, Nothing) -> True
                 (Nothing,  Just f) -> False
                 (Just f , Nothing) -> True
                 (Just f1, Just f2) -> f1 >= f2

    maxMaybe Nothing x = x
    maxMaybe x Nothing = x
    maxMaybe x y       = max x y

    bestParam Nothing x _ _ = x
    bestParam x Nothing _ _ = x
    bestParam x y (Just f1) (Just f2) = if f1 >= f2 then x else y

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
    combineConsts (ParamIx ix) (ConstVal x) = ConstVal x
    combineConsts (ConstVal x) (ParamIx ix) = ConstVal x -- p - p = 0
    combineConsts x y = error (show x <> " " <> show y)

-- | Fetch consts, cost, and size for all children in a single state traversal
getChildrenData :: Monad m => [EClassId] -> EGraphST m [(Consts, Cost, Int)]
getChildrenData ids = do
  ids' <- mapM canonical ids
  gets $ \eg ->
    map (\cid -> let ec = _eClass eg IntMap.! cid
                     d  = _info ec
                 in (_consts d, _cost d, _size d)) ids'
{-# INLINE getChildrenData #-}

-- | Calculate e-node data (constant values and cost)
makeAnalysis :: Monad m => CostFun -> ENode -> EGraphST m EClassData
makeAnalysis costFun enode =
  do let cs = eChildren enode
     childData <- getChildrenData cs
     let (consts', costs', sizes) = unzip3 childData
         consts = combineNode enode consts'
         cost   = costNode enode costs'
         sz     = sum sizes
     enode' <- canonize enode
     pure $ EData cost enode' consts Nothing Nothing [] (sz + 1)
  where
    -- ENAry folds children pairwise (constant folding over a multiset); the
    -- binary skeleton cannot represent n children.
    combineNode (ENAry op _) cs = foldr1 (\a b -> combineConsts (Bin (toOp op) a b)) cs
    combineNode _             cs = combineConsts (replaceChildren cs (fromENode enode))
    -- ENAry is a single flattened op node: op cost + sum of child costs.
    costNode (ENAry op _) cs = costFun (Bin (toOp op) 0 0) + sum cs
    costNode _             cs = costFun (replaceChildren cs (fromENode enode))

getChildrenMinHeight :: Monad m => ENode -> EGraphST m Int
getChildrenMinHeight enode = do
  let children = eChildren enode
  if null children then pure 0 else do
    children' <- mapM canonical children
    gets (\eg -> minimum $ map (\ec -> _height $ _eClass eg IntMap.! ec) children')

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
    getChildrenEC ec' = do ec <- getEClass ec'
                           pure $ concatMap eChildren (_eNodes ec)

    go [] _    _ = pure ()
    go qs tabu h =
      do childrenOf <- (TrueSet.\\ tabu) . TrueSet.fromList . concat <$> forM qs getChildrenEC -- rerieve all unvisited children
         let childrenL = TrueSet.toList childrenOf
         forM_ childrenL (setMinHeight h) -- set the height of the children as the minimum between current and h
         go childrenL (TrueSet.union tabu childrenOf) (h+1) -- move one breadth search style

-- | calculates the cost of a node
calculateCost :: Monad m => CostFun -> ENode -> EGraphST m Cost
calculateCost f enode =
  do let cs = eChildren enode
     costs <- traverse (fmap (_cost . _info) . getEClass) cs
     pure $ case enode of
              ENAry op _ -> f (Bin (toOp op) 0 0) + sum costs
              _          -> f (replaceChildren costs (fromENode enode))

-- | check whether an e-node evaluates to a const
calculateConsts :: Monad m => ENode -> EGraphST m Consts
calculateConsts enode =
  do let cs = eChildren enode
     consts <- traverse (fmap (_consts . _info) . getEClass) cs
     let c = case enode of
               ENAry op _ -> foldr1 (\a b -> combineConsts (Bin (toOp op) a b)) consts
               _          -> combineConsts (replaceChildren consts (fromENode enode))
     case c of
          ConstVal x | isNaN x -> pure (ConstVal x)
          a -> pure a

combineConsts :: SRTree Consts -> Consts
combineConsts (Const x)    = ConstVal x
combineConsts (Param ix)   = ParamIx ix
combineConsts (Var _)      = NotConst
combineConsts (Uni f t)    = case t of
                              ConstVal x -> ConstVal $ evalFun f x
                              --ParamIx  x -> ParamIx x
                              _          -> t
combineConsts (Bin op l r) = evalOp' l r
  where
    evalOp' (ParamIx ix) (ParamIx iy) = ParamIx (min ix iy)
    evalOp' (ConstVal x) (ConstVal y) = ConstVal $ evalOp op x y
    evalOp' _            _            = NotConst

insertFitness :: Monad m => EClassId -> Double -> [Target] -> EGraphST m ()
insertFitness eId' fit params =
  do eId <- canonical eId'
     tree <- getBestExpr eId
     let p = fromIntegral (length params)
     let f_compl = countNodes tree * log (countUniqueTokens tree) + p * (log (2 * pi * exp(1 - log 3)) - log p) / 2.0
     ec <- getEClass eId
     let oldFit  = _fitness . _info $ ec
     let newInfo = (_info ec){_fitness = Just fit, _theta = params}
         newEc   = ec{_info = newInfo}
         sz = _size newInfo
     modify' $ over eClass (IntMap.insert eId newEc)
     case oldFit of
       Nothing -> modify' $ over (eDB . unevaluated) (IntSet.delete eId)
                    . over (eDB . fitRangeDB) (insertRange eId fit)
                    . over (eDB . sizeFitDB) (IntMap.adjust (insertRange eId fit) sz . IntMap.insertWith RangeSet.union sz RangeSet.empty)
                    . over (eDB . dlRangeDB) (insertRange eId f_compl)
       Just oldVal -> modify' $ over (eDB . fitRangeDB) (insertRange eId fit . removeRange eId oldVal)
                                 . over (eDB . sizeFitDB) (IntMap.adjust (insertRange eId fit . removeRange eId oldVal) sz)

insertDL :: Monad m => EClassId -> Double -> EGraphST m ()
insertDL eId fit' =
  do let fit = negate fit'
     ec <- getEClass eId
     let sz = _size . _info $ ec
         newInfo = (_info ec){_dl = Just fit'}
         newEc   = ec{_info=newInfo}
     modify' $ over eClass (IntMap.insert eId newEc)
     modify' $ over (eDB . dlRangeDB) (insertRange eId fit)
             . over (eDB . sizeDLDB) (IntMap.adjust (insertRange eId fit) sz . IntMap.insertWith RangeSet.union sz RangeSet.empty)


