{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
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
--import Control.Monad (forM_, when, foldM, void)
import Data.List ( intercalate, foldl' )
import Control.Monad (forM)
import Control.Monad.State.Strict hiding ( get, put )
import Control.Monad.IO.Class (MonadIO(..))
import Data.Functor.Identity (Identity)
import GHC.Stack (HasCallStack)
import System.Random (StdGen)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as RangeSet
import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Recursion (cata)
import Data.Hashable
import Data.Binary
import qualified Data.Binary as Bin
import qualified Data.Vector.Unboxed as VU
import Control.DeepSeq (NFData)

import GHC.Generics


type EClassId     = Int -- NOTE: DO NOT CHANGE THIS, this will break the use of IntMap and IntSet
type ClassIdMap   = IntMap

-- | N-ary operators represented as flattened multisets inside the e-graph.
-- Only Add and Mul are associative-commutative in this library; the remaining
-- ops (Sub, Div, Power, PowerAbs, AQ) stay binary and live in 'EBin'.
data NOp = EAdd | EMul deriving (Show, Eq, Ord, Enum, Generic, NFData)

-- | The e-graph's node language.
--
-- 'ENAry' stores Add/Mul as a canonical multiset of e-class ids: children are
-- path-compressed, keys sorted by canonical 'EClassId' (commutativity), and
-- nested same-op ENAry children are absorbed at insertion time
-- (associativity), so no commutativity/associativity rewrite rules are needed
-- for Add/Mul. The children are an 'IntMap' of e-class id to multiplicity.
data ENode
  = EVar   {-# UNPACK #-} !Int
  | EParam {-# UNPACK #-} !Int
  | EConst {-# UNPACK #-} !Double
  | EUni   Function EClassId
  | EBin   Op EClassId EClassId          -- Sub | Div | Power | PowerAbs | AQ
  | ENAry  NOp (IntMap Int)              -- canonical multiset: eclass -> multiplicity
  deriving (Show, Eq, Generic, NFData)

type EGraphST m a = StateT EGraph m a
type Cost         = Int
type CostFun      = SRTree Cost -> Cost
type ECache = IntMap.IntMap Target

instance Hashable NOp where
  hashWithSalt n EAdd = n `hashWithSalt` (0 :: Int)
  hashWithSalt n EMul = n `hashWithSalt` (1 :: Int)

instance Hashable ENode where
  hashWithSalt n (EVar ix)      = n `hashWithSalt` (0 :: Int) `hashWithSalt` ix
  hashWithSalt n (EParam ix)    = n `hashWithSalt` (1 :: Int) `hashWithSalt` ix
  hashWithSalt n (EConst x)     = n `hashWithSalt` (2 :: Int) `hashWithSalt` x
  hashWithSalt n (EUni f t)     = n `hashWithSalt` (3 :: Int) `hashWithSalt` (fromEnum f) `hashWithSalt` t
  hashWithSalt n (EBin op l r)  = n `hashWithSalt` (4 :: Int) `hashWithSalt` (fromEnum op) `hashWithSalt` l `hashWithSalt` r
  hashWithSalt n (ENAry op m)   = n `hashWithSalt` (5 :: Int) `hashWithSalt` op `hashWithSalt` m

type RangeTree a = RangeSet.Set (a, EClassId)

-- | Expand a canonical multiset back to the equivalent (multi-)set of child
-- e-class ids, one entry per occurrence.
expandedList :: IntMap Int -> [EClassId]
expandedList = concatMap (\(k, n) -> replicate n k) . IntMap.toAscList
{-# INLINE expandedList #-}

-- | Build a canonical multiset from a list of child ids (duplicates allowed).
imFromList :: [EClassId] -> IntMap Int
imFromList = IntMap.fromListWith (+) . map (, 1)
{-# INLINE imFromList #-}



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

getSmallest :: Ord a => RangeTree a -> Maybe (a, EClassId)
getSmallest = RangeSet.lookupMin
{-# INLINE getSmallest #-}

getGreatest :: Ord a => RangeTree a -> Maybe (a, EClassId)
getGreatest = RangeSet.lookupMax
{-# INLINE getGreatest #-}

-- | Handle to an external, lazily paged e-class store (provided by the
-- storage layer, e.g. srtree-db's 'PageStore'). An 'EGraph' carries one when
-- e-classes are backed by a database; the IO actions fetch / persist /
-- evict a single e-class page. 'Nothing' keeps the classic fully-resident
-- behaviour.
data EClassPageStore = EClassPageStore
  { cpsLookup :: EClassId -> IO (Maybe EClass)
  , cpsInsert :: EClass -> IO ()
  , cpsDelete :: EClassId -> IO ()
  , cpsFlush  :: IO ()                      -- ^ write back all pending dirty pages
  , cpsAll    :: IO [EClass]                -- ^ all e-classes currently in the store
  , cpsKeys   :: IO [EClassId]              -- ^ all e-class ids currently in the store
  , cpsStreamRoots :: SRTree () -> Int -> [EClassId] -> IO [EClassId]  -- ^ bounded candidate roots for an operator, skipping an attempted set
  , cpsRecordNode  :: ENode -> EClassId -> IO ()         -- ^ register a newly-created node for write-back
  , cpsNodeToClass :: ENode -> IO (Maybe EClassId)       -- ^ content-address node -> class lookup (live)
  , cpsCanonicalOf :: EClassId -> IO (Maybe EClassId)    -- ^ e-class -> canonical representative (live)
  , cpsRecordCanonical :: EClassId -> EClassId -> IO ()  -- ^ persist a canonical mapping (write-back)
  , cpsBeginFrontier :: IO ()                            -- ^ start a frontier re-saturation (restrict matcher to changed classes)
  , cpsEndFrontier    :: IO ()                           -- ^ end it: clear the frontier (a pass re-saturated everything)
  }

data EGraph = EGraph { _canonicalMap  :: ClassIdMap EClassId   -- maps an e-class id to its canonical form
                     , _eNodeToEClass :: HashMap ENode EClassId    -- maps an e-node to its e-class id
                     , _eClass        :: ClassIdMap EClass     -- maps an e-class id to its e-class data (resident cache)
                     , _eDB           :: EGraphDB
                     , _classStore    :: Maybe EClassPageStore -- optional lazily paged store for _eClass
                     }

data EGraphDB = EDB { _worklist      :: HashSet (EClassId, ENode)      -- e-nodes and e-class schedule for analysis
                    , _analysis      :: HashSet (EClassId, ENode)      -- e-nodes and e-class that changed data
                     , _refits        :: IntSet
                    , _patDB         :: DB                         -- database of patterns
                    , _fitRangeDB    :: RangeTree Double           -- database of valid fitness
                    , _dlRangeDB     :: RangeTree Double
                    , _sizeDB        :: IntMap IntSet              -- database of model sizes
                    , _sizeFitDB     :: IntMap (RangeTree Double)  -- hacky! Size x Fitness DB
                    , _sizeDLDB      :: IntMap (RangeTree Double)
                    , _unevaluated   :: IntSet                     -- set of not-evaluated e-classes
                      , _nextId        :: Int                        -- next available id
                      , _changed       :: !Bool                      -- dirty flag: true if modified since last check
                      , _trackDBs      :: !Bool                      -- maintain range DBs (False during pure simplify)
                      , _seenMatches   :: Map String (RangeSet.Set String) -- persistent (rule source -> attempted match keys)
                      } deriving (Show, Generic)

data EClass = EClass { _eClassId :: {-# UNPACK #-} !Int                   -- e-class id (maybe we don't need that here)
                     , _eNodes   :: HashSet ENode           -- set of e-nodes inside this e-class
                     , _parents  :: HashSet (EClassId, ENode) -- parents (e-class, e-node)'s
                     , _height   :: {-# UNPACK #-} !Int                   -- height
                     , _info     :: EClassData            -- data
                     } deriving (Show, Eq, Generic)

data Consts   = NotConst | ParamIx {-# UNPACK #-} !Int | ConstVal {-# UNPACK #-} !Double deriving (Show, Eq, Generic)
data Property = Positive | Negative | NonZero | Real deriving (Show, Eq, Generic) -- TODO: incorporate properties

data EClassData = EData { _cost    :: {-# UNPACK #-} !Cost
                        , _best    :: ENode
                        , _consts  :: Consts
                        , _fitness :: Maybe Double    -- NOTE: this cannot be NaN
                        , _dl      :: Maybe Double
                        , _theta   :: [Target]
                        , _size    :: {-# UNPACK #-} !Int
                        -- , _properties :: Property
                        -- TODO: include evaluation of expression from this e-class
                        } deriving (Show, Generic)

-- * Serialization
instance Generic (EClassId, ENode)

instance Binary NOp where
  put EAdd = put (0 :: Word8)
  put EMul = put (1 :: Word8)

  get = do t <- get :: Get Word8
           case t of
             0 -> pure EAdd
             1 -> pure EMul

instance Binary ENode where
  put (EVar ix)      = put (0 :: Word8) >> put ix
  put (EParam ix)    = put (1 :: Word8) >> put ix
  put (EConst x)     = put (2 :: Word8) >> put x
  put (EUni f t)     = put (3 :: Word8) >> put (fromEnum f) >> put t
  put (EBin op l r)  = put (4 :: Word8) >> put (fromEnum op) >> put l >> put r
  put (ENAry op m)   = put (5 :: Word8) >> put op >> put (expandedList m)

  get = do t <- get :: Get Word8
           case t of
                0 -> EVar   <$> get
                1 -> EParam <$> get
                2 -> EConst <$> get
                3 -> EUni   <$> (toEnum <$> get) <*> get
                4 -> EBin   <$> (toEnum <$> get) <*> get <*> get
                5 -> ENAry  <$> get <*> (imFromList <$> get)

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

instance (Binary k, Binary v, Hashable k, Eq k) => Binary (HashMap k v) where
  put hm = put (HashMap.toList hm)
  get    = HashMap.fromList <$> get

instance Binary Target where
  put xs = put (VU.toList xs)
  get    = VU.fromList <$> get

instance Binary IntTrie
instance Binary EClass
instance Binary Consts
instance Binary Property
instance Binary EClassData
-- Custom: keep `_trackDBs` out of the wire format so on-disk EGraphDB data
-- (written before the flag existed) decodes unchanged; it defaults to True.
instance Binary EGraphDB where
  put (EDB w a r p f d s sf sdl u n c _ _) =
    put w >> put a >> put r >> put p >> put f >> put d >> put s >> put sf >> put sdl >> put u >> put n >> put c
  get = EDB <$> get <*> get <*> get <*> get <*> get <*> get <*> get <*> get <*> get <*> get <*> get <*> get <*> pure True <*> pure Map.empty
-- Custom: the wire format omits `_classStore` (a runtime handle to the paged
-- store, never serialized); it decodes to Nothing.
instance Binary EGraph where
  put (EGraph c n e d _) = put c >> put n >> put e >> put d
  get = EGraph <$> get <*> get <*> get <*> get <*> pure Nothing

instance Eq EClassData where
  EData c1 b1 cs1 ft1 dl1 _ s1 == EData c2 b2 cs2 ft2 dl2 _ s2 = c1==c2 && b1==b2 && cs1==cs2 && ft1==ft2 && dl1==dl2 && s1==s2

-- The database maps a symbol to an IntTrie
-- The IntTrie stores the possible paths from a certain e-class
-- that matches a pattern
type DB = Map (SRTree ()) IntTrie
-- The IntTrie is composed of the set of available keys (for convenience)
-- and an IntMap that maps one e-class id to the first child IntTrie,
-- the first child IntTrie will point to the next child and so on
newtype IntTrie = IntTrie { _trie :: IntMap IntTrie } deriving (Generic)

instance Show IntTrie where
  show (IntTrie t) = "{" <> intercalate "," (map (\(k,v) -> show k <> " -> " <> show v) $ IntMap.toList t) <> "}"

makeLenses ''EGraph
makeLenses ''EClass
makeLenses ''EClassData
makeLenses ''EGraphDB

-- * Paged e-class access

-- | A monad that can serve e-class data.
--
-- The pure instances ('Identity', 'State StdGen') serve classes from the
-- resident @_eClass@ map; the 'MonadIO' instance consults the optional
-- 'EClassPageStore' when the graph carries one, falling back to the resident
-- map otherwise. All e-class read/write goes through these accessors, which
-- are the single choke point for a paged (out-of-core) e-graph.
class Monad m => ClassStore m where
  lookupClass :: EClassId -> EGraphST m (Maybe EClass)
  getClass    :: HasCallStack => EClassId -> EGraphST m EClass
  insertClass :: EClass -> EGraphST m ()
  deleteClass :: EClassId -> EGraphST m ()
  adjustClass :: EClassId -> (EClass -> EClass) -> EGraphST m ()
  -- | Enumerate every e-class (ids / values) in the graph. Paged graphs stream
  -- from the store; resident graphs read the full @_eClass@ map.
  allClasses  :: EGraphST m [EClass]
  allKeys     :: EGraphST m [EClassId]
  -- | Read/write a class directly from/to the backing store, bypassing the
  -- resident LRU cache (and its O(n) 'trimResidentCache'). Bulk single-pass
  -- traversals such as 'recalculateBestAllStream' must use these: routing every
  -- one of ~n classes through 'lookupClass'/'insertClass' inserts each into the
  -- resident map and calls 'trimResidentCache' (a full O(n) rebuild) after each
  -- write, degenerating to O(n^2) and never terminating at scale.
  readDirect  :: EClassId -> EGraphST m (Maybe EClass)
  writeDirect :: EClass -> EGraphST m ()
  allClasses  = gets (IntMap.elems . _eClass)
  allKeys     = gets (IntMap.keys . _eClass)
  readDirect  = lookupClass
  writeDirect = insertClass
  -- | Enumerate (bounded) candidate e-class ids that contain a node of the
  -- given operator, to drive the streaming matcher, skipping any ids in
  -- @exclude@ (the already-attempted seen-set, so the per-rule budget advances
  -- to new roots across scheduler cycles). The default reads the resident
  -- @_patDB@ trie (the fully-in-RAM path); a paged graph streams the candidates
  -- from its backing store instead, so the matcher never builds an O(nodes)
  -- structure.
  streamRoots :: SRTree () -> Int -> [EClassId] -> EGraphST m [EClassId]
  streamRoots = streamRootsFromDB
  -- | Record a newly-created e-node (and its e-class) so a streaming matcher's
  -- candidate source can see it. The default (fully resident graph) is a no-op:
  -- the resident @_patDB@ is already updated by 'addToDB'.
  recordNode :: ENode -> EClassId -> EGraphST m ()
  recordNode _ _ = pure ()
  -- | Content-address node -> class lookup. The default reads the resident
  -- @_eNodeToEClass@ map (complete for a resident graph); a paged graph bounds
  -- that map and falls back to the backing store on a miss.
  lookupNode :: ENode -> EGraphST m (Maybe EClassId)
  lookupNode en = gets (HashMap.lookup en . _eNodeToEClass)
  -- | Record a node -> class mapping. The default keeps the resident (full)
  -- map; a paged graph bounds it (evicting, since the store is authoritative).
  insertNode :: ENode -> EClassId -> EGraphST m ()
  insertNode en eid = modify' $ over eNodeToEClass (HashMap.insert en eid)
  -- | Record a canonical mapping (e-class -> representative), persisting it on a
  -- paged graph so the store-backed canonical lookup sees merges/new classes.
  insertCanonical :: EClassId -> EClassId -> EGraphST m ()
  insertCanonical eid canon = modify' $ over canonicalMap (IntMap.insert eid canon)
  -- | The canonical representative of an e-class, or @Nothing@ when unknown. The
  -- default reads the resident @_canonicalMap@; a paged graph bounds it and
  -- falls back to the store.
  canonicalOf :: EClassId -> EGraphST m (Maybe EClassId)
  canonicalOf eid = gets (IntMap.lookup eid . _canonicalMap)

-- | Default candidate-root enumeration from the resident @_patDB@ trie, capped
-- at @budget@ after skipping @exclude@ (used by the pure instances and as the
-- no-store fallback for a @MonadIO@ graph).
streamRootsFromDB :: Monad m => SRTree () -> Int -> [EClassId] -> EGraphST m [EClassId]
streamRootsFromDB op budget exclude = do
  db <- gets (_patDB . _eDB)
  let ex = IntSet.fromList exclude
  case Map.lookup op db of
    Nothing  -> pure []
    Just trie -> pure (take budget [ e | e <- IntMap.keys (_trie trie), not (IntSet.member e ex) ])
{-# INLINE streamRootsFromDB #-}

-- | Whether the graph is backed by a lazily paged e-class store. Streaming
-- matchers dispatch on this: a paged graph enumerates candidates from the
-- backing store (bounded memory), a resident graph from @_patDB@.
isPagedGraph :: Monad m => EGraphST m Bool
isPagedGraph = gets (maybe False (const True) . _classStore)
{-# INLINE isPagedGraph #-}

-- Resident-map implementations (used by every pure monad) ------------------

pureLookupClass :: Monad m => EClassId -> EGraphST m (Maybe EClass)
pureLookupClass cid = gets (IntMap.lookup cid . _eClass)
{-# INLINE pureLookupClass #-}

pureGetClass :: (Monad m, HasCallStack) => EClassId -> EGraphST m EClass
pureGetClass cid = do
  m <- pureLookupClass cid
  case m of
    Just ec -> pure ec
    Nothing -> error $ "GETECLASS_MISSING eid=" <> show cid
{-# INLINE pureGetClass #-}

pureInsertClass :: Monad m => EClass -> EGraphST m ()
pureInsertClass ec = modify' $ over eClass (IntMap.insert (_eClassId ec) ec)
{-# INLINE pureInsertClass #-}

pureDeleteClass :: Monad m => EClassId -> EGraphST m ()
pureDeleteClass cid = modify' $ over eClass (IntMap.delete cid)
{-# INLINE pureDeleteClass #-}

pureAdjustClass :: Monad m => EClassId -> (EClass -> EClass) -> EGraphST m ()
pureAdjustClass cid f = modify' $ over eClass (IntMap.adjust f cid)
{-# INLINE pureAdjustClass #-}

-- | Maximum number of e-classes kept in the resident @_eClass@ cache when the
-- graph is backed by a paged store. When exceeded, the largest-id classes are
-- retained and the rest evicted from the resident map. The store remains
-- authoritative (and Little-data reads fall back to it), so eviction only
-- bounds memory, never correctness.
residentClassCap :: Int
residentClassCap = 50000

-- | Trim the resident @_eClass@ cache to at most 'residentClassCap' entries
-- by keeping the largest ids. No-op for graphs without a paged store (their
-- resident map must stay complete for the pure instances). Halving on 2x keeps
-- steady churn from triggering an O(n) rebuild on every insert.
trimResidentCache :: Monad m => EGraphST m ()
trimResidentCache = modify' $ \eg ->
  case _classStore eg of
    Nothing -> eg
    Just _  ->
      let m = _eClass eg
          n = IntMap.size m
      in if n <= 2 * residentClassCap
            then eg
            else over eClass (const (IntMap.fromList (Prelude.drop (n - residentClassCap) (IntMap.toAscList m)))) eg

-- | Bound on the resident @_eNodeToEClass@ cache on a paged graph. Beyond the
-- cap (checked at 2x, halved back to cap) the map is pruned; the backing store
-- is authoritative, so eviction only trades a little dedup accuracy for bounded
-- memory, never correctness.
nodeCacheCap :: Int
nodeCacheCap = 100000

-- | Bound on the resident @_canonicalMap@ cache on a paged graph (same
-- halve-on-2x policy; evicted entries are re-read from the store).
canonicalCacheCap :: Int
canonicalCacheCap = 100000
{-# INLINE nodeCacheCap #-}
{-# INLINE canonicalCacheCap #-}

trimNodeCache :: Monad m => EGraphST m ()
trimNodeCache = modify' $ \eg ->
  case _classStore eg of
    Nothing -> eg
    Just _  ->
      let m = _eNodeToEClass eg
          n = HashMap.size m
      in if n <= 2 * nodeCacheCap
            then eg
            else over eNodeToEClass (const (HashMap.fromList (Prelude.take nodeCacheCap (HashMap.toList m)))) eg
{-# INLINE trimNodeCache #-}

trimCanonicalCache :: Monad m => EGraphST m ()
trimCanonicalCache = modify' $ \eg ->
  case _classStore eg of
    Nothing -> eg
    Just _  ->
      let m = _canonicalMap eg
          n = IntMap.size m
      in if n <= 2 * canonicalCacheCap
            then eg
            else over canonicalMap (const (IntMap.fromList (Prelude.take canonicalCacheCap (IntMap.toAscList m)))) eg
{-# INLINE trimCanonicalCache #-}

instance ClassStore Identity where
  lookupClass = pureLookupClass
  getClass    = pureGetClass
  insertClass = pureInsertClass
  deleteClass = pureDeleteClass
  adjustClass = pureAdjustClass

instance ClassStore (State StdGen) where
  lookupClass = pureLookupClass
  getClass    = pureGetClass
  insertClass = pureInsertClass
  deleteClass = pureDeleteClass
  adjustClass = pureAdjustClass

-- Any monad that can run IO is potentially paged: the graph's optional
-- store, when present, is authoritative; otherwise classes come from the
-- resident map.
instance {-# OVERLAPPABLE #-} (Monad m, MonadIO m) => ClassStore m where
  -- The resident map is kept in sync by 'insertClass'/'deleteClass', so it is
  -- consulted first: repeated reads never touch the store, and a class that
  -- was evicted from the store's LRU while still dirty is never served stale.
  lookupClass cid = do
    eg <- gets id
    case IntMap.lookup cid (_eClass eg) of
      Just ec -> pure (Just ec)
      Nothing -> case _classStore eg of
                   Nothing -> pure Nothing
                   Just h  -> liftIO (cpsLookup h cid)
  getClass cid = do
    eg <- gets id
    case IntMap.lookup cid (_eClass eg) of
      Just ec -> pure ec
      Nothing -> case _classStore eg of
                   Nothing -> pureGetClass cid
                   Just h  -> do
                     m <- liftIO (cpsLookup h cid)
                     case m of
                       Just ec -> do
                         modify' (over eClass (IntMap.insert cid ec))
                         trimResidentCache
                         pure ec
                       Nothing -> error $ "GETECLASS_MISSING eid=" <> show cid
  insertClass ec = do
    eg <- gets id
    case _classStore eg of
      Nothing -> pureInsertClass ec
      Just h  -> do liftIO (cpsInsert h ec)
                    pureInsertClass ec
                    trimResidentCache
  deleteClass cid = do
    eg <- gets id
    case _classStore eg of
      Nothing -> pureDeleteClass cid
      Just h  -> do liftIO (cpsDelete h cid)
                    pureDeleteClass cid
  adjustClass cid f = do
    eg <- gets id
    case _classStore eg of
      Nothing -> pureAdjustClass cid f
      Just _  -> do
        m <- lookupClass cid
        case m of
          Nothing -> pure ()
          Just ec -> insertClass (f ec)
  allClasses = do
    eg <- gets id
    case _classStore eg of
      Nothing -> pure (IntMap.elems (_eClass eg))
      Just h  -> liftIO (cpsAll h)
  allKeys = do
    eg <- gets id
    case _classStore eg of
      Nothing -> pure (IntMap.keys (_eClass eg))
      Just h  -> liftIO (cpsKeys h)
  -- Bypass the resident cache entirely: read the page straight from the store
  -- and never insert into the (bounded) resident map, so a bulk traversal over
  -- every class stays O(n) instead of O(n^2).
  readDirect cid = do
    eg <- gets id
    case _classStore eg of
      Nothing -> pureLookupClass cid
      Just h  -> liftIO (cpsLookup h cid)
  writeDirect ec = do
    eg <- gets id
    case _classStore eg of
      Nothing -> pureInsertClass ec
      Just h  -> liftIO (cpsInsert h ec)
  streamRoots op budget exclude = do
    eg <- gets id
    case _classStore eg of
      Nothing -> streamRootsFromDB op budget exclude
      Just h  -> liftIO (cpsStreamRoots h op budget exclude)
  recordNode en eid = do
    eg <- gets id
    case _classStore eg of
      Nothing -> pure ()
      Just h  -> liftIO (cpsRecordNode h en eid)
  lookupNode en = do
    eg <- gets id
    case _classStore eg of
      Nothing -> gets (HashMap.lookup en . _eNodeToEClass)
      Just h  -> do
        m <- gets (HashMap.lookup en . _eNodeToEClass)
        case m of
          Just eid -> pure (Just eid)
          Nothing -> do
            r <- liftIO (cpsNodeToClass h en)
            case r of
              Just eid -> do insertNode en eid
                             pure (Just eid)
              Nothing  -> pure Nothing
  insertNode en eid = do
    eg <- gets id
    case _classStore eg of
      Nothing -> modify' $ over eNodeToEClass (HashMap.insert en eid)
      Just _  -> do modify' $ over eNodeToEClass (HashMap.insert en eid)
                    trimNodeCache
  insertCanonical eid canon = do
    eg <- gets id
    case _classStore eg of
      Nothing -> modify' $ over canonicalMap (IntMap.insert eid canon)
      Just h  -> do modify' $ over canonicalMap (IntMap.insert eid canon)
                    trimCanonicalCache
                    liftIO (cpsRecordCanonical h eid canon)
  canonicalOf eid = do
    eg <- gets id
    case _classStore eg of
      Nothing -> gets (IntMap.lookup eid . _canonicalMap)
      Just h  -> do
        m <- gets (IntMap.lookup eid . _canonicalMap)
        case m of
          Just c  -> pure (Just c)
          Nothing -> do
            r <- liftIO (cpsCanonicalOf h eid)
            case r of
              Just c  -> do modify' $ over canonicalMap (IntMap.insert eid c)
                            trimCanonicalCache
                            pure (Just c)
              Nothing -> pure Nothing

-- * E-Graph basic supporting functions

-- | returns an empty e-graph
emptyGraph :: EGraph
emptyGraph = EGraph IntMap.empty HashMap.empty IntMap.empty emptyDB Nothing
{-# INLINE emptyGraph #-}

-- | returns an empty e-graph DB
emptyDB :: EGraphDB
emptyDB = EDB
  Set.empty
  Set.empty
  IntSet.empty
  Map.empty
  RangeSet.empty
  RangeSet.empty
  IntMap.empty
  IntMap.empty
  IntMap.empty
  IntSet.empty
  0
  False
  True
  Map.empty
{-# INLINE emptyDB #-}

-- | like 'emptyDB' but skips range-DB maintenance (pure simplify mode)
emptyDBNoTrack :: EGraphDB
emptyDBNoTrack = emptyDB{ _trackDBs = False }
{-# INLINE emptyDBNoTrack #-}

-- | an empty e-graph that skips range-DB maintenance (pure simplify mode)
emptyGraphNoTrack :: EGraph
emptyGraphNoTrack = EGraph IntMap.empty HashMap.empty IntMap.empty emptyDBNoTrack Nothing
{-# INLINE emptyGraphNoTrack #-}

-- | Creates a new e-class from an e-class id, a new e-node,
-- and the info of this e-class 
createEClass :: EClassId -> ENode -> EClassData -> Int -> EClass
createEClass cId enode' info h = EClass cId (Set.singleton enode') Set.empty h info
{-# INLINE createEClass #-}

-- | gets the canonical id of an e-class with full path compression
canonical :: ClassStore m => EClassId -> EGraphST m EClassId
canonical eclassId = do
  mStep <- canonicalOf eclassId
  case mStep of
    Nothing -> canonError eclassId
    Just oneStep
      | oneStep == eclassId -> pure eclassId
      | otherwise -> do
          (root, chain) <- walk [eclassId] oneStep
          -- compress the chain in the resident cache (cache-only: the store
          -- keeps the authoritative semantic mappings recorded at insert
          -- time, so eviction just loses the shortcut, never correctness).
          modify' $ \eg -> eg{ _canonicalMap =
                        foldl' (\m' k -> IntMap.insert k root m') (_canonicalMap eg) chain }
          pure root
  where
    walk :: ClassStore m => [EClassId] -> EClassId -> EGraphST m (EClassId, [EClassId])
    walk chain ecId = do
      mNext <- canonicalOf ecId
      case mNext of
        Nothing -> canonError ecId
        Just n
          | n == ecId -> pure (ecId, chain)
          | otherwise -> walk (ecId : chain) n

    canonError :: ClassStore m => EClassId -> EGraphST m a
    canonError eid = do
      m <- gets _canonicalMap
      error $ "CANON_MISSING eid=" <> show eid <> " mapSize=" <> show (IntMap.size m)
{-# INLINE canonical #-}

-- | canonize the e-node children
canonize :: (ClassStore m, HasCallStack) => ENode -> EGraphST m ENode
canonize (EVar ix)     = pure (EVar ix)
canonize (EParam ix)   = pure (EParam ix)
canonize (EConst x)    = pure (EConst x)
canonize (EUni f t)    = EUni f <$> canonical t
canonize (EBin op l r) = EBin op <$> canonical l <*> canonical r
-- re-map children to their canonical ids; IntMap keeps keys sorted, so
-- commutativity is structural, no rewrite rule required.
canonize (ENAry op m) = do
  m' <- IntMap.fromListWith (+) <$> forM (IntMap.toList m) (\(c, n) -> do
            c' <- canonical c
            pure (c', n))
  pure (ENAry op m')
{-# INLINE canonize #-}

-- | The children e-class ids of an e-node.
eChildren :: ENode -> [EClassId]
eChildren (EVar _)     = []
eChildren (EParam _)   = []
eChildren (EConst _)   = []
eChildren (EUni _ t)   = [t]
eChildren (EBin _ l r) = [l, r]
eChildren (ENAry _ m)  = expandedList m
{-# INLINE eChildren #-}

toOp :: NOp -> Op
toOp EAdd = Add
toOp EMul = Mul
{-# INLINE toOp #-}

-- | Operator shape key used to index the pattern database. ENAry maps back to
-- the corresponding binary operator shape so existing (binary) Add/Mul
-- patterns address the same trie.
eOpKey :: ENode -> SRTree ()
eOpKey (EVar ix)     = Var ix
eOpKey (EParam ix)   = Param ix
eOpKey (EConst x)    = Const x
eOpKey (EUni f _)    = Uni f ()
eOpKey (EBin op _ _) = Bin op () ()
eOpKey (ENAry EAdd _) = Bin Add () ()
eOpKey (ENAry EMul _) = Bin Mul () ()
{-# INLINE eOpKey #-}

-- | Convert an e-node (children still as e-class ids) into the equivalent
-- binary SRTree shape. NOTE: only called on non-ENary nodes; flattened
-- ENAry nodes have no binary skeleton (see 'naryTree' / the explicit ENAry
-- cases in the analyses).
fromENode :: ENode -> SRTree EClassId
fromENode (EVar ix)     = Var ix
fromENode (EParam ix)   = Param ix
fromENode (EConst x)    = Const x
fromENode (EUni f t)    = Uni f t
fromENode (EBin op l r) = Bin op l r
fromENode (ENAry _ _)   = error "fromENode: ENAry has no binary skeleton"
{-# INLINE fromENode #-}

-- | Right-fold a list of e-class child expressions into a binary Fix SRTree
-- for a flattened ENAry multiset (extraction).
naryTree :: NOp -> [Fix SRTree] -> Fix SRTree
naryTree op ts = normalizeSubDiv (foldr1 (\a b -> Fix (Bin (toOp op) a b)) ts)
{-# INLINE naryTree #-}

-- | Re-render the internal negate/recip canonical forms back as Sub/Div so
-- extraction output keeps the familiar shape: `x + (-1)*y` -> `x - y`,
-- `x + (-3)` -> `x - 3` and `x * recip y` -> `x / y`. Sub and Div never
-- appear as e-nodes; they only reappear here during reconstruction.
normalizeSubDiv :: Fix SRTree -> Fix SRTree
normalizeSubDiv = cata alg
  where
    alg :: SRTree (Fix SRTree) -> Fix SRTree
    alg (Bin Add l r) = case pick l r of
        Just (pos, neg) -> Fix (Bin Sub pos neg)
        Nothing         -> Fix (Bin Add l r)
      where
        pick a b = case negated a of
                     Just t -> Just (b, t)
                     Nothing -> case negated b of
                                  Just t -> Just (a, t)
                                  Nothing -> Nothing
        negated (Fix (Bin Mul (Fix (Const c)) t)) | c == -1 = Just t
        negated (Fix (Bin Mul t (Fix (Const c)))) | c == -1 = Just t
        negated (Fix (Const c)) | c < 0 = Just (Fix (Const (-c)))
        negated _ = Nothing
    alg (Bin Mul l r) = case pick l r of
        Just (num, den) -> Fix (Bin Div num den)
        Nothing         -> Fix (Bin Mul l r)
      where
        pick a b = case a of
                     Fix (Uni Recip t) -> Just (b, t)
                     _ -> case b of
                            Fix (Uni Recip t) -> Just (a, t)
                            _ -> Nothing
    alg t = Fix t

-- | Convert a binary SRTree (children as e-class ids) into an e-node,
-- flattening Add/Mul into canonical ENAry multisets.
toENode :: (ClassStore m, HasCallStack) => SRTree EClassId -> EGraphST m ENode
toENode (Var ix)     = pure (EVar ix)
toENode (Param ix)   = pure (EParam ix)
toENode (Const x)    = pure (EConst x)
toENode (Uni f t)    = EUni f <$> canonical t
toENode (Bin Add l r) = mkENary EAdd [l, r]
toENode (Bin Mul l r) = mkENary EMul [l, r]
toENode (Bin op l r)  = EBin op <$> canonical l <*> canonical r
toENode n             = error $ "toENode: unsupported node " <> show n
{-# INLINE toENode #-}

-- | Build a canonical ENAry from child ids: canonicalize children, absorb
-- nested same-op ENAry children (associativity), sort by key (commutativity).
mkENary :: (ClassStore m, HasCallStack) => NOp -> [EClassId] -> EGraphST m ENode
mkENary op cids = mkENaryM op (imFromList cids)

-- | Build a canonical ENAry from a canonical multiset of child ids.
mkENaryM :: (ClassStore m, HasCallStack) => NOp -> IntMap Int -> EGraphST m ENode
mkENaryM op m = do
  flat <- IntMap.unionsWith (+) <$> mapM (expandM op) (IntMap.toList m)
  pure (ENAry op flat)

-- | If the e-class of `cid` holds exactly one e-node and that node is an ENAry
-- of the same op, return its children scaled by `n` (flattening `n`
-- occurrences); otherwise return `n` copies of `cid`. Flattening is only sound
-- through a class with a single node: if the class were merged with other
-- nodes (e.g. `{Add[a,b], Mul[x,c]}`) flattening would silently pick one
-- representative and change the meaning of the term.
expandM :: (ClassStore m, HasCallStack) => NOp -> (EClassId, Int) -> EGraphST m (IntMap Int)
expandM op (cid, n) = do
  ec <- getEClass cid
  case Set.toList (_eNodes ec) of
    [ENAry op' m'] | op' == op -> pure (IntMap.map (* n) m')
    _                          -> pure (IntMap.singleton cid n)

-- | Reconstruct a binary Fix SRTree from an e-node, right-folding ENAry
-- into nested Bin Add/Mul.
enodeToTree :: (ClassStore m, HasCallStack) => ENode -> EGraphST m (Fix SRTree)
enodeToTree (EVar ix)   = pure (Fix (Var ix))
enodeToTree (EParam ix) = pure (Fix (Param ix))
enodeToTree (EConst x)  = pure (Fix (Const x))
enodeToTree (EUni f t)  = Fix . Uni f <$> getBestExpr t
enodeToTree (EBin op l r) = do
  tl <- getBestExpr l
  tr <- getBestExpr r
  pure (Fix (Bin op tl tr))
enodeToTree (ENAry op m) = do
  ts <- mapM getBestExpr (expandedList m)
  pure (naryTree op ts)
{-# INLINE enodeToTree #-}

-- | gets an e-class with id `c` (auto-canonizes)
getEClass :: (ClassStore m, HasCallStack) => EClassId -> EGraphST m EClass
getEClass c = do c' <- canonical c; getClass c'
{-# INLINE getEClass #-}

-- | gets the best expression given the default cost function. Cycle-safe and
-- budgeted: see 'getBestExprBounded'.
getBestExpr :: (ClassStore m, HasCallStack) => EClassId -> EGraphST m (Fix SRTree)
getBestExpr eid = getBestExprBounded eid

-- | Like 'getBestExpr' but terminates on pathological graphs: a visited set
-- stops the expansion from re-entering an already-expanded class (a @_best@
-- cycle arising from supersaturation/merges), and a node budget caps the total
-- expanded size (so an exponentially-shared DAG is truncated rather than
-- exploded). Both guards substitute a @Var 0@ placeholder for the part that
-- would otherwise blow up. On well-formed acyclic graphs with small bests
-- neither guard triggers, so the result is identical to the unbounded version.
-- This keeps out-of-core extraction (e.g. 'dbTop') bounded in memory.
getBestExprBounded :: (ClassStore m, HasCallStack) => EClassId -> EGraphST m (Fix SRTree)
getBestExprBounded eid = fst <$> expand Set.empty 0 eid
  where
    budget :: Int
    budget = 200
    -- expand returns the tree and the running count of expanded nodes, so the
    -- budget bounds the TOTAL size (not just the depth): an exponentially-shared
    -- DAG is truncated instead of exploded. A revisited (cyclic) class or a
    -- full budget yields a @Var 0@ placeholder.
    expand :: ClassStore m => HashSet EClassId -> Int -> EClassId -> EGraphST m (Fix SRTree, Int)
    expand _ n _ | n >= budget = pure (Fix (Var 0), n)
    expand seen n eid
      | Set.member eid seen = pure (Fix (Var 0), n)
      | otherwise = do
          best <- (_best . _info) <$> getEClass eid
          let seen' = Set.insert eid seen
              n0    = n + 1
          case best of
            EVar ix   -> pure (Fix (Var ix), n0)
            EParam ix -> pure (Fix (Param ix), n0)
            EConst x  -> pure (Fix (Const x), n0)
            EUni f t  -> do (tt, n1) <- expand seen' n0 t
                            pure (Fix (Uni f tt), n1)
            EBin op l r -> do
              (tl, n1) <- expand seen' n0 l
              (tr, n2) <- expand seen' n1 r
              pure (Fix (Bin op tl tr), n2)
            ENAry op m -> do
              (xs, nEnd) <- goNary seen' n0 (IntMap.toAscList m) []
              pure (if null xs then (Fix (Var 0), nEnd) else (naryTree op xs, nEnd))
    -- build the ENAry children from the multiset WITHOUT materialising the
    -- expanded multiplicity list: an enormous count (a pathological supersaturated
    -- class) is capped per-child and by the total budget, so each copy counts
    -- toward the budget and no giant list is ever allocated.
    goNary seen n es acc
      | n >= budget = pure (reverse acc, n)
      | otherwise = case es of
          [] -> pure (reverse acc, n)
          ((c, cnt) : rest) -> do
            (t, n1) <- expand seen n c
            let take = min cnt (budget - n1 + 1)
                n2   = n1 + (take - 1)
                acc' = Prelude.replicate take t ++ acc
            goNary seen n2 rest acc'

-- | Creates a singleton trie from an e-class id
trie :: EClassId -> IntMap IntTrie -> IntTrie
trie eid = IntTrie
{-# INLINE trie #-}

-- | Check whether an e-class is a constant value
isConst :: ClassStore m => EClassId -> EGraphST m Bool
isConst eid = do ec <- getEClass eid
                 case (_consts . _info) ec of
                   ConstVal _ -> pure True
                   _          -> pure False
{-# INLINE isConst #-}

getFitness :: ClassStore m => EClassId -> EGraphST m (Maybe Double)
getFitness c = (_fitness . _info) <$> getEClass c
{-# INLINE getFitness #-}
getTheta :: ClassStore m => EClassId -> EGraphST m ([Target])
getTheta c = (_theta . _info) <$> getEClass c
{-# INLINE getTheta #-}
getSize :: ClassStore m => EClassId -> EGraphST m Int
getSize c = (_size . _info) <$> getEClass c
{-# INLINE getSize #-}
isSizeOf :: (Int -> Bool) -> EClass -> Bool
isSizeOf p = p . _size . _info
{-# INLINE isSizeOf #-}
getBestFitness :: ClassStore m => EGraphST m (Maybe Double)
getBestFitness = do
    mbec <- gets (fmap snd . getGreatest . _fitRangeDB . _eDB)
    case mbec of
      Just bec -> (_fitness . _info) <$> getEClass bec
      Nothing  -> pure Nothing
getDL :: ClassStore m => EClassId -> EGraphST m (Maybe Double)
getDL c = (_dl . _info) <$> getEClass c
{-# INLINE getDL #-}
