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
                      , _seenMatches   :: Map String IntSet          -- persistent (rule source -> attempted root classes)
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
-- resident map must stay complete for the pure instances).
trimResidentCache :: Monad m => EGraphST m ()
trimResidentCache = modify' $ \eg ->
  case _classStore eg of
    Nothing -> eg
    Just _  ->
      let m = _eClass eg
          n = IntMap.size m
      in if n <= residentClassCap
            then eg
            else over eClass (const (IntMap.fromList (Prelude.drop (n - residentClassCap) (IntMap.toAscList m)))) eg

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
canonical :: (Monad m, HasCallStack) => EClassId -> EGraphST m EClassId
canonical eclassId =
  do m <- gets _canonicalMap
     let oneStep = case IntMap.lookup eclassId m of
           Just x -> x
           Nothing -> error $ "CANON_MISSING eid=" <> show eclassId <> " mapSize=" <> show (IntMap.size m)
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
canonize :: (Monad m, HasCallStack) => ENode -> EGraphST m ENode
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

-- | gets the best expression given the default cost function
getBestExpr :: (ClassStore m, HasCallStack) => EClassId -> EGraphST m (Fix SRTree)
getBestExpr eid = do
  best <- (_best . _info) <$> getEClass eid
  enodeToTree best

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
