{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
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
import Control.Monad.State.Strict hiding ( get, put )
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Sequence ( Seq(..), (><) )
import qualified Data.Sequence as FingerTree
import Data.Foldable ( toList )
import Data.SRTree
import Data.SRTree.Eval
import Data.Hashable
import Data.Binary
import qualified Data.Binary as Bin
import qualified Data.Massiv.Array as MA

import GHC.Generics

import Debug.Trace

type EClassId     = Int -- NOTE: DO NOT CHANGE THIS, this will break the use of IntMap and IntSet
type ClassIdMap   = IntMap
type ENode        = SRTree EClassId
type ENodeEnc     = (Int, Int, Int, Double)
type EGraphST m a = StateT EGraph m a
type Cost         = Int
type CostFun      = SRTree Cost -> Cost

instance Hashable ENode where
  hashWithSalt n enode = hashWithSalt n (encodeEnode enode)

type RangeTree a = Seq (a, EClassId)

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
insertRange eid x Empty                      = FingerTree.singleton (x, eid)
insertRange eid x (y :<| _xs) | (x, eid) < y = (x, eid) :<| y :<| _xs
insertRange eid x (_xs :|> y) | (x, eid) > y = _xs :|> y :|> (x, eid)
insertRange eid x rt = go rt
  where
    entry   = (x, eid)
    go root = case FingerTree.splitAt (n `div` 2) root of
                (Empty, Empty)    -> FingerTree.singleton entry
                (Empty, z :<| zs) | entry < z -> entry :<| z :<| zs
                                  | otherwise -> z :<| (go zs)
                (ys :|> y, Empty) | entry > y -> ys :|> y :|> entry
                                  | otherwise -> (go ys) :|> y
                (ys :|> y, z :<| zs)
                     | entry > y && entry < z -> (ys :|> y :|> entry) >< (z :<| zs)
                     | entry > z              -> (ys :|> y) >< go (z :<| zs)
                     | entry < y              -> go (ys :|> y) >< (z :<| zs)
                     | otherwise              -> root
      where
        n = FingerTree.length root

removeRange :: (Ord a, Show a) => EClassId -> a -> RangeTree a -> RangeTree a
removeRange eid x Empty                  = Empty
removeRange eid x (y :<| _xs) | (x, eid) < y = (y :<| _xs)
removeRange eid x (_xs :|> y) | (x, eid) > y = (_xs :|> y)
removeRange eid x rt = go rt
  where
    entry   = (x, eid)
    go root = case FingerTree.splitAt (n `div` 2) root of
                (Empty, Empty)    -> root
                (Empty, z :<| zs)
                            | entry < z  -> z :<| zs
                            | entry == z -> zs
                            | otherwise  -> z :<| (go zs)
                (ys :|> y, Empty)
                            | entry > y  -> ys :|> y
                            | entry == y -> ys
                            | otherwise  -> (go ys) :|> y
                (ys :|> y, z :<| zs)
                     | entry > y && entry < z -> root
                     | entry > z              -> (ys :|> y) >< go (z :<| zs)
                     | entry < y              -> go (ys :|> y) >< (z :<| zs)
                     | otherwise              -> root

      where
        n = FingerTree.length root


-- TODO: check this \/
getWithinRange :: Ord a => a -> a -> RangeTree a -> [EClassId]
getWithinRange lb ub rt = map snd . toList $ go rt
  where
    go Empty = Empty
    go root = case FingerTree.splitAt (n `div` 2) root of
                (Empty, Empty)    -> Empty
                (ys :|> y, Empty)
                     | fst y < lb    -> Empty
                     | otherwise -> go (ys :|> y)
                (Empty, z :<| zs)
                            | fst z > ub    -> Empty
                            | otherwise -> go (z :<| zs)
                (ys :|> y, z :<| zs)
                     | fst y < lb -> go (z :<| zs)
                     | fst z > ub -> go (ys :|> y)
                     | otherwise -> go (ys :|> y) >< go (z :<| zs)
      where
        n = FingerTree.length root


getSmallest :: Ord a => RangeTree a -> (a, EClassId)
getSmallest rt = case rt of
                     Empty -> error "empty finger"
                     x :<| t -> x
{-# INLINE getSmallest #-}

getGreatest :: Ord a => RangeTree a -> (a, EClassId)
getGreatest rt = case rt of
                     Empty -> error "empty finger"
                     t :|> x -> x
{-# INLINE getGreatest #-}

data EGraph = EGraph { _canonicalMap  :: ClassIdMap EClassId   -- maps an e-class id to its canonical form
                     , _eNodeToEClass :: Map ENode EClassId    -- maps an e-node to its e-class id
                     , _eClass        :: ClassIdMap EClass     -- maps an e-class id to its e-class data
                     , _eDB           :: EGraphDB
                     } deriving (Show, Generic)

data EGraphDB = EDB { _worklist      :: HashSet (EClassId, ENode)      -- e-nodes and e-class schedule for analysis
                    , _analysis      :: HashSet (EClassId, ENode)      -- e-nodes and e-class that changed data
                    , _patDB         :: DB                         -- database of patterns
                    , _fitRangeDB    :: RangeTree Double           -- database of valid fitness
                    , _sizeDB        :: IntMap IntSet              -- database of model sizes
                    , _sizeFitDB     :: IntMap (RangeTree Double)  -- hacky! Size x Fitness DB
                    , _unevaluated   :: IntSet                     -- set of not-evaluated e-classes
                    , _nextId        :: Int                        -- next available id
                    } deriving (Show, Generic)

data EClass = EClass { _eClassId :: Int                   -- e-class id (maybe we don't need that here)
                     , _eNodes   :: HashSet ENodeEnc          -- set of e-nodes inside this e-class
                     , _parents  :: HashSet (EClassId, ENode) -- parents (e-class, e-node)'s
                     , _height   :: Int                   -- height
                     , _info     :: EClassData            -- data
                     } deriving (Show, Eq, Generic)

data Consts   = NotConst | ParamIx Int | ConstVal Double deriving (Show, Eq, Generic)
data Property = Positive | Negative | NonZero | Real deriving (Show, Eq, Generic) -- TODO: incorporate properties

data EClassData = EData { _cost    :: Cost
                        , _best    :: ENode
                        , _consts  :: Consts
                        , _fitness :: Maybe Double    -- NOTE: this cannot be NaN
                        , _theta   :: Maybe PVector
                        , _size    :: Int
                        -- , _properties :: Property
                        -- TODO: include evaluation of expression from this e-class
                        } deriving (Show, Generic)

-- * Serialization
instance Generic (EClassId, ENode)

instance Binary (SRTree EClassId) where
  put (Var ix)     = put (0 :: Word8) >> put ix
  put (Param ix)   = put (1 :: Word8) >> put ix
  put (Const x)    = put (2 :: Word8) >> put x
  put (Uni f t)    = put (3 :: Word8) >> put (fromEnum f) >> put t
  put (Bin op l r) = put (4 :: Word8) >> put (fromEnum op) >> put l >> put r

  get = do t <- get :: Get Word8
           case t of
                0 -> Var   <$> get
                1 -> Param <$> get
                2 -> Const <$> get
                3 -> Uni   <$> (toEnum <$> get) <*> get
                4 -> Bin   <$> (toEnum <$> get) <*> get <*> get

instance Binary (SRTree ()) where
  put (Var ix)     = put (0 :: Word8) >> put ix
  put (Param ix)   = put (1 :: Word8) >> put ix
  put (Const x)    = put (2 :: Word8) >> put x
  put (Uni f t)    = put (3 :: Word8) >> put (fromEnum f)
  put (Bin op l r) = put (4 :: Word8) >> put (fromEnum op)

  get = do t <- get :: Get Word8
           case t of
                0 -> Var   <$> get
                1 -> Param <$> get
                2 -> Const <$> get
                3 -> Uni   <$> (toEnum <$> get) <*> pure ()
                4 -> Bin   <$> (toEnum <$> get) <*> pure () <*> pure ()

instance (Binary a, Hashable a) => Binary (HashSet a) where
  put hs = put (Set.toList hs)
  get    = Set.fromList <$> get

instance Binary PVector where
  put xs = put (MA.toList xs)
  get    = MA.fromList compMode <$> get

instance Binary IntTrie
instance Binary EClass
instance Binary Consts
instance Binary Property
instance Binary EClassData
instance Binary EGraphDB
instance Binary EGraph

instance Eq EClassData where
  EData c1 b1 cs1 ft1 _ s1 == EData c2 b2 cs2 ft2 _ s2 = c1==c2 && b1==b2 && cs1==cs2 && ft1==ft2 && s1==s2

-- The database maps a symbol to an IntTrie
-- The IntTrie stores the possible paths from a certain e-class
-- that matches a pattern
type DB = Map (SRTree ()) IntTrie
-- The IntTrie is composed of the set of available keys (for convenience)
-- and an IntMap that maps one e-class id to the first child IntTrie,
-- the first child IntTrie will point to the next child and so on
data IntTrie = IntTrie { _keys :: HashSet EClassId, _trie :: IntMap IntTrie } deriving (Generic)

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
{-# INLINE emptyGraph #-}

-- | returns an empty e-graph DB
emptyDB :: EGraphDB
emptyDB = EDB Set.empty Set.empty Map.empty FingerTree.empty IntMap.empty IntMap.empty IntSet.empty 0
{-# INLINE emptyDB #-}

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
{-# INLINE trie #-}

-- | Check whether an e-class is a constant value
isConst :: Monad m => EClassId -> EGraphST m Bool
isConst eid = do ec <- gets ((IntMap.! eid) . _eClass)
                 case (_consts . _info) ec of
                   ConstVal _ -> pure True
                   _          -> pure False
{-# INLINE isConst #-}
