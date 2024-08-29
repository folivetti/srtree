{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.EqSat1
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Equality Saturation for SRTree
--
-----------------------------------------------------------------------------

module Data.SRTree.Egraph where

import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Recursion ( cataM )
import Control.Monad
import Control.Monad.State
import Control.Lens ( (+~), (-~), makeLenses, (^.), (.~), (&), element, over )
import Data.IntMap ( IntMap, empty, toList, insert, delete )
import Data.Set ( Set )
import Data.Map ( Map )
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import System.Random
import Data.Ratio
import Debug.Trace
import Data.AEq ( AEq((~==)) )


type EClassId   = Int -- DO NOT CHANGE THIS without changing the next line! This will break the use of IntMap for speed
type ClassIdMap = IntMap
type ENode      = SRTree EClassId
type EData      = ()
type EGraphST a = State EGraph a
type Cost       = Int
type CostFun    = SRTree Cost -> Cost

data EGraph = EGraph { _canonicalMap  :: ClassIdMap EClassId -- maps an e-class id to its canonical form
                     , _eNodeToEClass :: Map ENode EClassId  -- maps an e-node to its e-class id
                     , _eClass        :: ClassIdMap EClass   -- maps an e-class id to its e-class data
                     , _worklist      :: [(EClassId, ENode)] -- e-nodes and e-class schedule for analysis
                     , _analysis      :: [(EClassId, ENode)] -- e-nodes and e-class that changed data
                     , _nextId        :: Int                 -- next available id
                     } deriving Show

data EClass = EClass { _eClassId :: Int                 -- e-class id (maybe we don't need that here)
                     , _eNodes   :: Set ENode           -- set of e-nodes inside this e-class
                     , _parents  :: [(EClassId, ENode)] -- parents (e-class, e-node)'s
                     , _height   :: Int                 -- height
                     , _info     :: EClassData          -- data
                     } deriving (Show, Eq)

data Consts   = NotConst | ParamIx Int | ConstVal Double deriving (Show, Eq)
data Property = Positive | Negative | NonZero | Real deriving (Show, Eq)

data EClassData = EData { _cost   :: Cost
                        , _best   :: ENode
                        , _consts :: Consts
                        -- , _properties :: Property
                        } deriving (Show, Eq)

makeLenses ''EGraph
makeLenses ''EClass
makeLenses ''EClassData

add :: CostFun -> ENode -> EGraphST EClassId
add costFun enode =
  do enode'  <- canonize enode                                             -- canonize e-node
     doExist <- gets ((Map.member enode') . _eNodeToEClass)                -- check if canonical e-node exists
     if doExist
        then gets ((Map.! enode') . _eNodeToEClass)                        -- returns existing e-node
        else do curId <- gets _nextId                                      -- get the next available e-class id
                modify' $ over nextId (+1)                                 -- update next id
                        . over canonicalMap (insert curId curId)           -- insert e-class id into canon map
                        . over eNodeToEClass (Map.insert enode' curId)     -- associate new e-node with id
                        . over worklist ((curId, enode'):)                 -- add e-node and id into worklist
                forM_ (children enode') (addParents curId enode')          -- update the children's parent list
                info <- makeAnalysis costFun enode'
                let newClass = EClass curId (Set.singleton enode') [] 0 info -- create e-class
                modify' $ over eClass (insert curId newClass)              -- insert new e-class into e-graph
                newId <- modifyEClass costFun curId                        -- simplify eclass if it evaluates to a number
                pure newId                                                 -- returns the e-class id
  where
    addParents :: EClassId -> ENode -> EClassId -> EGraphST ()
    addParents cId node c =
      do ec <- getEClass c
         let ec' = ec{ _parents = (cId, node):_parents ec }
         modify' $ over eClass (insert c ec')

-- | rebuilds the e-graph after inserting or merging
-- e-classes
rebuild :: CostFun -> EGraphST ()
rebuild costFun =
  do wl <- gets _worklist
     al <- gets _analysis
     modify' $ over worklist (const [])
             . over analysis (const [])
     forM_ wl (uncurry (repair costFun))
     forM_ al (uncurry (repairAnalysis costFun))

-- | repairs e-node by canonizing its children
-- if the canonized e-node already exists in
-- e-graph, merge the e-classes
repair :: CostFun -> EClassId -> ENode -> EGraphST ()
repair costFun ecId enode =
  do modify' $ over eNodeToEClass (Map.delete enode)
     enode'  <- canonize enode
     ecId'   <- canonical ecId
     doExist <- gets ((Map.member enode') . _eNodeToEClass)
     if doExist
       then do ecIdCanon <- gets ((Map.! enode') . _eNodeToEClass)
               _ <- merge costFun ecIdCanon ecId'
               pure ()
       else modify' $ over eNodeToEClass (Map.insert enode' ecId')

-- | repair the analysis of the e-class
-- considering the new added e-node
repairAnalysis :: CostFun -> EClassId -> ENode -> EGraphST ()
repairAnalysis costFun ecId enode =
  do ecId'  <- canonical ecId
     enode' <- canonize enode
     eclass <- getEClass ecId'
     info   <- makeAnalysis costFun enode'
     let newData = joinData (_info eclass) info
         eclass' = eclass { _info = newData }
     when ((_info eclass) /= newData) $
       do modify' $ over analysis (_parents eclass <>)
                  . over eClass (insert ecId' eclass')
          _ <- modifyEClass costFun ecId'
          pure ()

-- | merge to equivalnt e-classes
merge :: CostFun -> EClassId -> EClassId -> EGraphST EClassId
merge costFun c1 c2 =
  do c1' <- canonical c1
     c2' <- canonical c2
     if c1' == c2'                                     -- if they are already merge, return canonical
       then pure c1'
       else do (led, ledC, sub, subC) <- getLeaderSub c1' c2'  -- the leader will be the e-class with more parents
               mergeClasses led ledC sub subC          -- merge sub into leader
  where
    mergeClasses :: EClassId -> EClass -> EClassId -> EClass -> EGraphST EClassId
    mergeClasses led ledC sub subC =
      do modify' $ over canonicalMap (insert sub led) -- points sub e-class to leader to maintain consistency
         let -- create new e-class with same id as led
             newC = EClass led
                           (_eNodes ledC `Set.union` _eNodes subC)
                           (_parents ledC <> _parents subC)
                           (min (_height ledC) (_height subC))
                           (joinData (_info ledC) (_info subC))

         modify' $ over eClass (insert led newC . delete sub) -- delete sub e-class and replace leader
                 . over worklist ((_parents subC) <>)         -- insert parents of sub into worklist
         when (_info newC /= _info ledC)                      -- if there was change in data,
           $ modify' $ over analysis ((_parents ledC) <>)     --   insert parents into analysis
         when (_info newC /= _info subC)
           $ modify' $ over analysis ((_parents subC) <>)
         modifyEClass costFun led
         pure led

    getLeaderSub c1 c2 =
      do ec1 <- getEClass c1
         ec2 <- getEClass c2
         let n1 = length (_parents ec1)
             n2 = length (_parents ec2)
         pure $ if n1 >= n2
                  then (c1, ec1, c2, ec2)
                  else (c2, ec2, c1, ec1)

-- modify an e-class, e.g., add constant e-node and prune non-leaves
modifyEClass :: CostFun -> EClassId -> EGraphST EClassId
modifyEClass costFun ecId =
  do ec <- getEClass ecId
     if (((_consts . _info) ec) /= NotConst)
      then
       do let en = case ((_consts . _info) ec) of
                     ParamIx ix -> Param ix
                     ConstVal x -> Const x
          c <- calculateCost costFun en
          let infoEc = (_info ec){ _cost = c, _best = en }
          maybeEid <- gets ((Map.!? en) . _eNodeToEClass)
          modify' $ over eClass (insert ecId ec{_eNodes = Set.singleton en , _info = infoEc})
          case maybeEid of
            Nothing   -> pure ecId
            Just eid' -> merge costFun eid' ecId
              -- en'    = Set.insert en $ _eNodes ec
      else pure ecId


-- join data from two e-classes
joinData :: EClassData -> EClassData -> EClassData
joinData (EData c1 b1 cn1) (EData c2 b2 cn2) =
  EData (min c1 c2) b (combineConsts cn1 cn2)
  where
    b = if c1 <= c2 then b1 else b2
    combineConsts (ConstVal x) (ConstVal y)
      | abs (x-y) < 1e-7   = ConstVal $ (x+y)/2
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
makeAnalysis :: CostFun -> ENode -> EGraphST EClassData
makeAnalysis costFun enode =
  do consts <- calculateConsts enode
     enode' <- canonize enode
     cost   <- calculateCost costFun enode'
     pure $ EData cost enode' consts

-- | Creates an e-graph from an expression tree
fromTree :: CostFun -> Fix SRTree -> (EClassId, EGraph)
fromTree costFun tree = cataM sequence' (add costFun) tree `runState` emptyGraph

-- | Builds an e-graph from multiple independent trees
fromTrees :: CostFun -> [Fix SRTree] -> ([EClassId], EGraph)
fromTrees costFun = Prelude.foldr (\t (rs, eg) -> let (r, eg') = fromTreeWith costFun eg t in (r:rs, eg')) ([], emptyGraph)

-- | insert new tree into an existing e-graph
fromTreeWith :: CostFun -> EGraph -> Fix SRTree -> (EClassId, EGraph)
fromTreeWith costFun eg tree = cataM sequence' (add costFun) tree `runState` eg

-- | returns all the root e-classes (e-class without parents)
findRootClasses :: EGraph -> [EClassId]
findRootClasses = Prelude.map fst . Prelude.filter isParent . toList . _eClass
  where
    isParent (k, v) = Prelude.null (_parents v) || fst (head (_parents v)) == k

-- | returns one expression rooted at e-class `eId`
getExpressionFrom :: EGraph -> EClassId -> Fix SRTree
getExpressionFrom eg eId = case head (Set.toList nodes) of
                                Bin op l r -> Fix $ Bin op (getExpressionFrom eg l) (getExpressionFrom eg r)
                                Uni f t    -> Fix $ Uni f (getExpressionFrom eg t)
                                Var ix     -> Fix $ Var ix
                                Const x    -> Fix $ Const x
                                Param ix   -> Fix $ Param ix
  where
    nodes = _eNodes . (IntMap.! eId) . _eClass $ eg

-- | returns all expressions rooted at e-class `eId`
getAllExpressionsFrom :: EGraph -> EClassId -> [Fix SRTree]
getAllExpressionsFrom eg eId = concatMap f (Set.toList nodes)
  where
    f n = case n of
            Bin op l r -> Prelude.map Fix $ (Bin op) <$> (getAllExpressionsFrom eg l) <*> (getAllExpressionsFrom eg r)
            Uni f t    -> (Fix . Uni f) <$> (getAllExpressionsFrom eg t)
            Var ix     -> [Fix $ Var ix]
            Const x    -> [Fix $ Const x]
            Param ix   -> [Fix $ Param ix]
    nodes = _eNodes . (IntMap.! eId) . _eClass $ eg

-- | returns a random expression rooted at e-class `eId`
getRndExpressionFrom :: EGraph -> EClassId -> State StdGen (Fix SRTree)
getRndExpressionFrom eg eId = do n <- randomFrom nodes
                                 Fix <$> case n of
                                            Bin op l r -> Bin op <$> (getRndExpressionFrom eg l) <*> (getRndExpressionFrom eg r)
                                            Uni f t    -> Uni f <$> (getRndExpressionFrom eg t)
                                            Var ix     -> pure $ Var ix
                                            Const x    -> pure $ Const x
                                            Param ix   -> pure $ Param ix
  where
    nodes           = Set.toList . _eNodes . (IntMap.! eId) . _eClass $ eg
    randomRange rng = state (randomR rng)
    randomFrom xs   = do n <- randomRange (0, length xs - 1)
                         pure $ xs !! n

-- | update the heights of each e-class
-- won't work if there's no root
calculateHeights :: EGraphST ()
calculateHeights =
  do queue   <- gets findRootClasses
     classes <- gets (Prelude.map fst . toList . _eClass)
     let nClasses = length classes
     forM_ classes (setHeight nClasses) -- set all heights to max possible height (number of e-classes)
     forM_ queue (setHeight 0)          -- set root e-classes height to zero
     go queue (Set.fromList queue) 1    -- next height is 1
  where
    setHeight x eId' =
      do eId <- canonical eId'
         ec <- getEClass eId
         let ec' = over height (const x) ec
         modify' $ over eClass (insert eId ec')

    setMinHeight x eId' = -- set height to the minimum between current and x
      do eId <- canonical eId'
         h <- _height <$> getEClass eId
         setHeight (min h x) eId

    getChildren :: EClassId -> EGraphST [EClassId]
    getChildren ec' = do ec <- canonical ec'
                         gets (concatMap children . _eNodes . (IntMap.! ec) . _eClass)

    go [] _    _ = pure ()
    go qs tabu h =
      do children <- (Set.\\ tabu) . Set.fromList . concat <$> forM qs getChildren -- rerieve all unvisited children
         let childrenL = Set.toList children
         forM_ childrenL (setMinHeight h) -- set the height of the children as the minimum between current and h
         go childrenL (Set.union tabu children) (h+1) -- move one breadth search style

-- | gets the canonical id of an e-class
canonical :: EClassId -> EGraphST EClassId
canonical eclassId =
  do m <- gets _canonicalMap
     go m eclassId
    where
      go m ecId
        | m IntMap.! ecId == ecId = pure ecId        -- if the e-class id is mapped to itself, it's canonical
        | otherwise        = go m (m IntMap.! ecId)  -- otherwise, check the next id in the sequence
{-# INLINE canonical #-}

canonical' :: EClassId -> EGraph -> EClassId
canonical' ec eg = go ec
  where
    m = _canonicalMap eg
    go ec
      | m IntMap.! ec == ec = ec
      | otherwise           = go (m IntMap.! ec)
{-# INLINE canonical' #-}

-- | canonize the e-node children
canonize :: ENode -> EGraphST ENode
canonize = sequence' . fmap canonical  -- applies canonical to the children
{-# INLINE canonize #-}

sequence' :: Applicative f => SRTree (f a) -> f (SRTree a)
sequence' (Bin f ml mr) = Bin f <$> ml <*> mr
sequence' (Uni f mt)    = Uni f <$> mt
sequence' (Var ix)      = pure (Var ix)
sequence' (Param ix)    = pure (Param ix)
sequence' (Const x)     = pure (Const x)
{-# INLINE sequence' #-}

children :: SRTree a -> [a]
children (Bin _ l r) = [l, r]
children (Uni _ t)   = [t]
children _           = []
{-# INLINE children #-}

replaceChildren :: [a] -> SRTree b -> SRTree a
replaceChildren [l, r] (Bin op _ _) = Bin op l r
replaceChildren [t]    (Uni f _)    = Uni f t
replaceChildren _      (Var ix)     = Var ix
replaceChildren _      (Param ix)   = Param ix
replaceChildren _      (Const x)    = Const x
{-# INLINE replaceChildren #-}

getOperator :: SRTree a -> SRTree ()
getOperator (Bin op _ _) = Bin op () ()
getOperator (Uni f _) = Uni f () 
getOperator (Var ix) = Var ix 
getOperator (Param ix) = Param ix 
getOperator (Const x) = Const x 

-- | gets an e-class with id `c`
getEClass :: EClassId -> EGraphST EClass
getEClass c = gets ((IntMap.! c) . _eClass)
{-# INLINE getEClass #-}

-- | returns an empty e-graph
emptyGraph :: EGraph
emptyGraph = EGraph empty Map.empty empty [] [] 0

-- | calculates the cost of a node
calculateCost :: CostFun -> SRTree EClassId -> EGraphST Cost
calculateCost f t =
  do let cs = children t
     costs <- traverse (\c -> (_cost . _info) <$> getEClass c) cs
     pure . f $ replaceChildren costs t

-- | check whether an e-node evaluates to a const
calculateConsts :: SRTree EClassId -> EGraphST Consts
calculateConsts t =
  do let cs = children t
     eg <- get
     consts <- traverse (\c -> (_consts . _info) <$> getEClass c) cs
     case (combineConsts $ replaceChildren consts t) of
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
