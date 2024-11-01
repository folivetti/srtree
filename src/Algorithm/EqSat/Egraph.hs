{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.EqSat.Egraph
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Equality Graph data structure 
-- Heavily based on hegg (https://github.com/alt-romes/hegg by alt-romes)
--
-----------------------------------------------------------------------------

module Algorithm.EqSat.Egraph where

import Control.Lens (element, makeLenses, view, over, (&), (+~), (-~), (.~), (^.))
--import Control.Monad (forM, forM_, when, foldM, void)
import Data.List ( intercalate )
import Control.Monad.State.Strict
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.FingerTree ( FingerTree, Measured, ViewL(..), ViewR(..), (<|), (|>), measure )
import qualified Data.FingerTree as FingerTree
import Data.Foldable ( toList )
import Data.SRTree
import Data.SRTree.Eval
import Data.Hashable

import Debug.Trace

type EClassId     = Int -- NOTE: DO NOT CHANGE THIS, this will break the use of IntMap and IntSet
type ClassIdMap   = IntMap
type ENode        = SRTree EClassId
type ENodeEnc     = (Int, Int, Int, Double)
type EGraphST m a = StateT EGraph m a
type Cost         = Int
type CostFun      = SRTree Cost -> Cost

data Range a = EmptyRange | Range EClassId a a
data Singl a = Singl EClassId a deriving Show

eidOf (Singl eid _) = eid
valOf (Singl _ v)   = v
high (Range _ _ h) = h
low (Range _ l _) = l

instance Hashable ENode where
  hashWithSalt n enode = hashWithSalt n (encodeEnode enode)

instance Ord a => Semigroup (Range a) where
  EmptyRange <> rng = rng
  rng <> EmptyRange = rng
  (Range i a b) <> (Range j c d) = Range j (min a c) (max b d)
instance Ord a => Monoid (Range a) where
  mempty = EmptyRange

instance Ord a => Measured (Range a) (Singl a) where
  measure (Singl eid x) = Range eid x x

type RangeTree a = FingerTree (Range a) (Singl a)

-- | this assumes up to 999 variables and params
encodeEnode :: ENode -> ENodeEnc
--encodeEnode = id
{--}
encodeEnode (Var ix)         = (0, ix, -1, 0)
encodeEnode (Param ix)       = (1, ix, -1, 0)
encodeEnode (Const x)        = (2, -1, -1, x)
encodeEnode (Uni f ed)       = (300 + fromEnum f, ed, -1, 0)
encodeEnode (Bin op ed1 ed2) = (400 + fromEnum op, ed1, ed2, 0)
{--}
{-# INLINE encodeEnode #-}

decodeEnode :: ENodeEnc -> ENode
--decodeEnode = id
{--}
decodeEnode (0, ix, _, _) = Var ix
decodeEnode (1, ix, _, _) = Param ix
decodeEnode (2, _, _, x)  = Const x
decodeEnode (opCode, arg1, arg2, arg3)
  | opCode < 400 = Uni (toEnum $ opCode-300) arg1
  | otherwise    = Bin (toEnum $ opCode-400) arg1 arg2
  {--}
{-# INLINE decodeEnode #-}

insertRange :: (Ord a, Show a) => EClassId -> a -> RangeTree a -> RangeTree a
insertRange eid x rt = go rt
  where
    go root
      | theSame (measure root)    = root
      | toTheLeft (measure root)  = (Singl eid x) <| root
      | toTheRight (measure root) = root |> (Singl eid x)
      | otherwise = let (l, r) = FingerTree.split greater root
                    in l <> (go r)

    greater EmptyRange       = False
    greater (Range eid' a b) = x < b

    toTheLeft EmptyRange = True
    toTheLeft (Range eid' lo hi) = (x < lo) || (x == lo && eid < eid')

    toTheRight EmptyRange = True
    toTheRight (Range eid' lo hi) = (x > hi) || (x == hi && eid > eid')

    theSame EmptyRange = False
    theSame (Range eid' _ _) = eid' == eid

removeRange :: (Ord a, Show a) => EClassId -> a -> RangeTree a -> RangeTree a
removeRange eid x rt = go rt
  where
    go root
      | theSame (measure root)    = FingerTree.empty
      | toTheLeft (measure root)  = (Singl eid x) <| root
      | toTheRight (measure root) = root |> (Singl eid x)
      | otherwise = let (l, r) = FingerTree.split greater root
                    in l <> (go r)

    greater EmptyRange       = False
    greater (Range eid' a b) = x < b

    toTheLeft EmptyRange = True
    toTheLeft (Range eid' lo hi) = (x < lo) || (x == lo && eid < eid')

    toTheRight EmptyRange = True
    toTheRight (Range eid' lo hi) = (x > hi) || (x == hi && eid > eid')

    theSame EmptyRange = False
    theSame (Range eid' _ _) = eid' == eid

-- TODO: check this \/
getWithinRange :: Ord a => a -> a -> RangeTree a -> [EClassId]
getWithinRange lb ub rt = map eidOf $ toList eids
  where
    (l, r)    = FingerTree.split greater rt
    (eids, _) = FingerTree.split smaller r

    greater EmptyRange = False
    greater (Range _ a b) = lb > b

    smaller EmptyRange = False
    smaller (Range _ a b) = ub <= a

getSmallest :: Ord a => RangeTree a -> Singl a
getSmallest rt = case FingerTree.viewl rt of
                     EmptyL -> error "empty finger"
                     x :< t -> x
getGreatest :: Ord a => RangeTree a -> Singl a
getGreatest rt = case FingerTree.viewr rt of
                     EmptyR -> error "empty finger"
                     t :> x -> x


data EGraph = EGraph { _canonicalMap  :: ClassIdMap EClassId   -- maps an e-class id to its canonical form
                     , _eNodeToEClass :: Map ENode EClassId    -- maps an e-node to its e-class id
                     , _eClass        :: ClassIdMap EClass     -- maps an e-class id to its e-class data
                     , _eDB           :: EGraphDB
                     } deriving Show

data EGraphDB = EDB { _worklist      :: HashSet (EClassId, ENode)      -- e-nodes and e-class schedule for analysis
                    , _analysis      :: HashSet (EClassId, ENode)      -- e-nodes and e-class that changed data
                    , _patDB         :: DB                         -- database of patterns
                    , _fitRangeDB    :: RangeTree Double           -- database of valid fitness
                    , _sizeDB        :: IntMap IntSet              -- database of model sizes
                    , _unevaluated   :: IntSet                     -- set of not-evaluated e-classes
                    , _nextId        :: Int                        -- next available id
                    } deriving Show

data EClass = EClass { _eClassId :: Int                   -- e-class id (maybe we don't need that here)
                     , _eNodes   :: HashSet ENodeEnc          -- set of e-nodes inside this e-class
                     , _parents  :: HashSet (EClassId, ENode) -- parents (e-class, e-node)'s
                     , _height   :: Int                   -- height
                     , _info     :: EClassData            -- data
                     } deriving (Show, Eq)

data Consts   = NotConst | ParamIx Int | ConstVal Double deriving (Show, Eq)
data Property = Positive | Negative | NonZero | Real deriving (Show, Eq) -- TODO: incorporate properties

data EClassData = EData { _cost    :: Cost
                        , _best    :: ENode
                        , _consts  :: Consts
                        , _fitness :: Maybe Double    -- NOTE: this cannot be NaN
                        , _theta   :: Maybe PVector
                        , _size    :: Int
                        -- , _properties :: Property
                        -- TODO: include evaluation of expression from this e-class
                        } deriving (Show)

instance Eq EClassData where
  EData c1 b1 cs1 ft1 _ s1 == EData c2 b2 cs2 ft2 _ s2 = c1==c2 && b1==b2 && cs1==cs2 && ft1==ft2 && s1==s2

-- The database maps a symbol to an IntTrie
-- The IntTrie stores the possible paths from a certain e-class
-- that matches a pattern
type DB = Map (SRTree ()) IntTrie
-- The IntTrie is composed of the set of available keys (for convenience)
-- and an IntMap that maps one e-class id to the first child IntTrie,
-- the first child IntTrie will point to the next child and so on
data IntTrie = IntTrie { _keys :: HashSet EClassId, _trie :: IntMap IntTrie } -- deriving Show

-- Shows the IntTrie as {keys} -> {show IntTries}
instance Show IntTrie where
  show (IntTrie k t) = let keys  = intercalate "," (map show $ Set.toList k)
                           tries = intercalate "," (map (\(k,v) -> show k <> " -> " <> show v) $ IntMap.toList t)
                       in "{" <> keys <> "} - {" <> tries <> "}"

makeLenses ''EGraph
makeLenses ''EClass
makeLenses ''EClassData
makeLenses ''EGraphDB

-- * E-Graph basic supporting functions

-- | returns an empty e-graph
emptyGraph :: EGraph
emptyGraph = EGraph IntMap.empty Map.empty IntMap.empty emptyDB

-- | returns an empty e-graph DB
emptyDB :: EGraphDB
emptyDB = EDB Set.empty Set.empty Map.empty FingerTree.empty IntMap.empty IntSet.empty 0

-- | Creates a new e-class from an e-class id, a new e-node,
-- and the info of this e-class 
createEClass :: EClassId -> ENode -> EClassData -> Int -> EClass
createEClass cId enode' info h = EClass cId (Set.singleton $ encodeEnode enode') Set.empty h info
{-# INLINE createEClass #-}

-- | gets the canonical id of an e-class
canonical :: Monad m => EClassId -> EGraphST m EClassId
canonical eclassId =
  do m <- gets _canonicalMap
     let oneStep = m IntMap.! eclassId
     if oneStep == eclassId
        then pure eclassId
        else go m oneStep
    where
      go :: Monad m => IntMap EClassId -> EClassId -> EGraphST m EClassId
      go m ecId
        | m IntMap.! ecId == ecId = do modify' $ over canonicalMap (IntMap.insert eclassId ecId) -- creates a shortcut for next time
                                       pure ecId        -- if the e-class id is mapped to itself, it's canonical
        | otherwise        = go m (m IntMap.! ecId)  -- otherwise, check the next id in the sequence
{-# INLINE canonical #-}

-- | canonize the e-node children
canonize :: Monad m => ENode -> EGraphST m ENode
canonize = mapM canonical  -- applies canonical to the children
{-# INLINE canonize #-}

-- | gets an e-class with id `c`
getEClass :: Monad m => EClassId -> EGraphST m EClass
getEClass c = gets ((IntMap.! c) . _eClass)
{-# INLINE getEClass #-}

-- | Creates a singleton trie from an e-class id
trie :: EClassId -> IntMap IntTrie -> IntTrie
trie eid = IntTrie (Set.singleton eid)

-- | Check whether an e-class is a constant value
isConst :: Monad m => EClassId -> EGraphST m Bool
isConst eid = do ec <- gets ((IntMap.! eid) . _eClass)
                 case (_consts . _info) ec of
                   ConstVal _ -> pure True
                   _          -> pure False
{-# INLINE isConst #-}
