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
import Data.List ( intercalate, foldl' )
import Control.Monad.State.Strict hiding ( get, put )
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as RangeSet
import Data.SRTree
import Data.SRTree.Eval
import Data.Hashable
import Data.Binary
import qualified Data.Binary as Bin
import qualified Data.Vector.Unboxed as VU

import GHC.Generics

import Debug.Trace

type EClassId     = Int -- NOTE: DO NOT CHANGE THIS, this will break the use of IntMap and IntSet
type ClassIdMap   = IntMap
type ENode        = SRTree EClassId
type EGraphST m a = StateT EGraph m a
type Cost         = Int
type CostFun      = SRTree Cost -> Cost
type ECache = IntMap.IntMap Target

instance Hashable ENode where
  hashWithSalt n (Var ix)       = n `hashWithSalt` (0 :: Int) `hashWithSalt` ix
  hashWithSalt n (Param ix)     = n `hashWithSalt` (1 :: Int) `hashWithSalt` ix
  hashWithSalt n (Const x)      = n `hashWithSalt` (2 :: Int) `hashWithSalt` x
  hashWithSalt n (Uni f e)      = n `hashWithSalt` (3 :: Int) `hashWithSalt` (fromEnum f) `hashWithSalt` e
  hashWithSalt n (Bin op l r)   = n `hashWithSalt` (4 :: Int) `hashWithSalt` (fromEnum op) `hashWithSalt` l `hashWithSalt` r

type RangeTree a = RangeSet.Set (a, EClassId)



insertRange :: (Ord a, Show a) => EClassId -> a -> RangeTree a -> RangeTree a
insertRange eid x = RangeSet.insert (x, eid)
{-# INLINE insertRange #-}

removeRange :: (Ord a, Show a) => EClassId -> a -> RangeTree a -> RangeTree a
removeRange eid x = RangeSet.delete (x, eid)
{-# INLINE removeRange #-}





-- TODO: check this \/
getWithinRange :: Ord a => a -> a -> RangeTree a -> [EClassId]
getWithinRange lb ub rt =
  let (_, ge)  = RangeSet.split (lb, minBound) rt
      (inR, _) = RangeSet.split (ub, maxBound) ge
  in map snd (RangeSet.toList inR)

getSmallest :: Ord a => RangeTree a -> (a, EClassId)
getSmallest = maybe (error "empty range tree") id . RangeSet.lookupMin
{-# INLINE getSmallest #-}

getGreatest :: Ord a => RangeTree a -> (a, EClassId)
getGreatest = maybe (error "empty range tree") id . RangeSet.lookupMax
{-# INLINE getGreatest #-}

data EGraph = EGraph { _canonicalMap  :: ClassIdMap EClassId   -- maps an e-class id to its canonical form
                     , _eNodeToEClass :: Map ENode EClassId    -- maps an e-node to its e-class id
                     , _eClass        :: ClassIdMap EClass     -- maps an e-class id to its e-class data
                     , _eDB           :: EGraphDB
                     } deriving (Show, Generic)

data EGraphDB = EDB { _worklist      :: HashSet (EClassId, ENode)      -- e-nodes and e-class schedule for analysis
                    , _analysis      :: HashSet (EClassId, ENode)      -- e-nodes and e-class that changed data
                    , _refits        :: HashSet EClassId
                    , _patDB         :: DB                         -- database of patterns
                    , _fitRangeDB    :: RangeTree Double           -- database of valid fitness
                    , _dlRangeDB     :: RangeTree Double
                    , _sizeDB        :: IntMap IntSet              -- database of model sizes
                    , _sizeFitDB     :: IntMap (RangeTree Double)  -- hacky! Size x Fitness DB
                    , _sizeDLDB      :: IntMap (RangeTree Double)
                    , _unevaluated   :: IntSet                     -- set of not-evaluated e-classes
                     , _nextId        :: Int                        -- next available id
                     , _changed       :: !Bool                      -- dirty flag: true if modified since last check
                     } deriving (Show, Generic)

data EClass = EClass { _eClassId :: Int                   -- e-class id (maybe we don't need that here)
                     , _eNodes   :: HashSet ENode           -- set of e-nodes inside this e-class
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
                        , _dl      :: Maybe Double
                        , _theta   :: [Target]
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

instance Binary Target where
  put xs = put (VU.toList xs)
  get    = VU.fromList <$> get

instance Binary IntTrie
instance Binary EClass
instance Binary Consts
instance Binary Property
instance Binary EClassData
instance Binary EGraphDB
instance Binary EGraph

instance Eq EClassData where
  EData c1 b1 cs1 ft1 dl1 _ s1 == EData c2 b2 cs2 ft2 dl2 _ s2 = c1==c2 && b1==b2 && cs1==cs2 && ft1==ft2 && dl1==dl2 && s1==s2

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
emptyDB = EDB Set.empty Set.empty Set.empty Map.empty RangeSet.empty RangeSet.empty IntMap.empty IntMap.empty IntMap.empty IntSet.empty 0 False
{-# INLINE emptyDB #-}

-- | Creates a new e-class from an e-class id, a new e-node,
-- and the info of this e-class 
createEClass :: EClassId -> ENode -> EClassData -> Int -> EClass
createEClass cId enode' info h = EClass cId (Set.singleton enode') Set.empty h info
{-# INLINE createEClass #-}

-- | gets the canonical id of an e-class with full path compression
canonical :: Monad m => EClassId -> EGraphST m EClassId
canonical eclassId =
  do m <- gets _canonicalMap
     let oneStep = m IntMap.! eclassId
     if oneStep == eclassId
        then pure eclassId
        else do
          let loop path ecId
                | m IntMap.! ecId == ecId = (ecId, eclassId : path)
                | otherwise = loop (ecId : path) (m IntMap.! ecId)
              (root, path) = loop [] oneStep
          modify' $ \eg -> eg{ _canonicalMap =
                        foldl' (\m' k -> IntMap.insert k root m') (_canonicalMap eg) path }
          pure root
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

getFitness :: Monad m => EClassId -> EGraphST m (Maybe Double)
getFitness c = gets (_fitness . _info . (IntMap.! c) . _eClass)
{-# INLINE getFitness #-}
getTheta :: Monad m => EClassId -> EGraphST m ([Target])
getTheta c = gets (_theta . _info . (IntMap.! c) . _eClass)
{-# INLINE getTheta #-}
getSize :: Monad m => EClassId -> EGraphST m Int
getSize c = gets (_size . _info . (IntMap.! c) . _eClass)
{-# INLINE getSize #-}
isSizeOf :: (Int -> Bool) -> EClass -> Bool
isSizeOf p = p . _size . _info
{-# INLINE isSizeOf #-}
getBestFitness :: Monad m => EGraphST m (Maybe Double)
getBestFitness = do
    bec <- (gets (snd . getGreatest . _fitRangeDB . _eDB) >>= canonical)
    gets (_fitness . _info . (IntMap.! bec) . _eClass)
getDL :: Monad m => EClassId -> EGraphST m (Maybe Double)
getDL c = gets (_dl . _info . (IntMap.! c) . _eClass)
{-# INLINE getDL #-}
