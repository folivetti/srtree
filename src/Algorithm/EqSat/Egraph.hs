{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
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
import Data.List ( intercalate, foldl', sort )
import Control.Monad.State.Strict hiding ( get, put )
import GHC.Stack (HasCallStack)
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
-- path-compressed, sorted by canonical 'EClassId' (commutativity), and nested
-- same-op ENAry children are absorbed at insertion time (associativity), so
-- no commutativity/associativity rewrite rules are needed for Add/Mul.
data ENode
  = EVar   {-# UNPACK #-} !Int
  | EParam {-# UNPACK #-} !Int
  | EConst {-# UNPACK #-} !Double
  | EUni   Function EClassId
  | EBin   Op EClassId EClassId          -- Sub | Div | Power | PowerAbs | AQ
  | ENAry  NOp [EClassId]                -- canonical sorted multiset
  deriving (Show, Eq, Ord, Generic, NFData)

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
  hashWithSalt n (ENAry op xs)  = n `hashWithSalt` (5 :: Int) `hashWithSalt` op `hashWithSalt` xs

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

getSmallest :: Ord a => RangeTree a -> Maybe (a, EClassId)
getSmallest = RangeSet.lookupMin
{-# INLINE getSmallest #-}

getGreatest :: Ord a => RangeTree a -> Maybe (a, EClassId)
getGreatest = RangeSet.lookupMax
{-# INLINE getGreatest #-}

data EGraph = EGraph { _canonicalMap  :: ClassIdMap EClassId   -- maps an e-class id to its canonical form
                     , _eNodeToEClass :: HashMap ENode EClassId    -- maps an e-node to its e-class id
                     , _eClass        :: ClassIdMap EClass     -- maps an e-class id to its e-class data
                     , _eDB           :: EGraphDB
                     } deriving (Show, Generic)

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
  put (ENAry op xs)  = put (5 :: Word8) >> put op >> put xs

  get = do t <- get :: Get Word8
           case t of
                0 -> EVar   <$> get
                1 -> EParam <$> get
                2 -> EConst <$> get
                3 -> EUni   <$> (toEnum <$> get) <*> get
                4 -> EBin   <$> (toEnum <$> get) <*> get <*> get
                5 -> ENAry  <$> get <*> get

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
newtype IntTrie = IntTrie { _trie :: IntMap IntTrie } deriving (Generic)

instance Show IntTrie where
  show (IntTrie t) = "{" <> intercalate "," (map (\(k,v) -> show k <> " -> " <> show v) $ IntMap.toList t) <> "}"

makeLenses ''EGraph
makeLenses ''EClass
makeLenses ''EClassData
makeLenses ''EGraphDB

-- * E-Graph basic supporting functions

-- | returns an empty e-graph
emptyGraph :: EGraph
emptyGraph = EGraph IntMap.empty HashMap.empty IntMap.empty emptyDB
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
{-# INLINE emptyDB #-}

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
-- re-sort: commutativity is structural, no rewrite rule required.
-- Fast path: skip the sort when the canonicalized children are already
-- ascending (the common case when re-canonizing a stored ENAry).
canonize (ENAry op xs) = do
  xs' <- mapM canonical xs
  pure $ if sortedAsc xs' then ENAry op xs' else ENAry op (sort xs')
{-# INLINE canonize #-}

sortedAsc :: Ord a => [a] -> Bool
sortedAsc (x : y : rest) = x <= y && sortedAsc (y : rest)
sortedAsc _              = True
{-# INLINE sortedAsc #-}

-- | The children e-class ids of an e-node.
eChildren :: ENode -> [EClassId]
eChildren (EVar _)     = []
eChildren (EParam _)   = []
eChildren (EConst _)   = []
eChildren (EUni _ t)   = [t]
eChildren (EBin _ l r) = [l, r]
eChildren (ENAry _ xs) = xs
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
toENode :: (Monad m, HasCallStack) => SRTree EClassId -> EGraphST m ENode
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
-- nested same-op ENAry children (associativity), sort (commutativity).
mkENary :: (Monad m, HasCallStack) => NOp -> [EClassId] -> EGraphST m ENode
mkENary op cids = do
  flat <- concat <$> mapM (expand op) cids
  pure (ENAry op flat)

-- | If the e-class of `cid` holds exactly one e-node and that node is an ENAry
-- of the same op, return its children directly (flattening); otherwise return
-- `[cid]`. Flattening is only sound through a class with a single node: if the
-- class were merged with other nodes (e.g. `{Add[a,b], Mul[x,c]}`) flattening
-- would silently pick one representative and change the meaning of the term.
expand :: (Monad m, HasCallStack) => NOp -> EClassId -> EGraphST m [EClassId]
expand op cid = do
  ec <- getEClass cid
  case Set.toList (_eNodes ec) of
    [ENAry op' xs] | op' == op -> pure xs
    _                          -> pure [cid]

-- | Reconstruct a binary Fix SRTree from an e-node, right-folding ENAry
-- into nested Bin Add/Mul.
enodeToTree :: (Monad m, HasCallStack) => ENode -> EGraphST m (Fix SRTree)
enodeToTree (EVar ix)   = pure (Fix (Var ix))
enodeToTree (EParam ix) = pure (Fix (Param ix))
enodeToTree (EConst x)  = pure (Fix (Const x))
enodeToTree (EUni f t)  = Fix . Uni f <$> getBestExpr t
enodeToTree (EBin op l r) = do
  tl <- getBestExpr l
  tr <- getBestExpr r
  pure (Fix (Bin op tl tr))
enodeToTree (ENAry op xs) = do
  ts <- mapM getBestExpr xs
  pure (naryTree op ts)
{-# INLINE enodeToTree #-}

-- | gets an e-class with id `c` (auto-canonizes)
getEClass :: (Monad m, HasCallStack) => EClassId -> EGraphST m EClass
getEClass c = do c' <- canonical c; gets $ \eg -> case IntMap.lookup c' (_eClass eg) of
                                   Just ec -> ec
                                   Nothing -> error $ "GETECLASS_MISSING eid=" <> show c'
                                             <> " nClasses=" <> show (IntMap.size (_eClass eg))
{-# INLINE getEClass #-}

-- | gets the best expression given the default cost function
getBestExpr :: (Monad m, HasCallStack) => EClassId -> EGraphST m (Fix SRTree)
getBestExpr eid = do
  best <- (_best . _info) <$> getEClass eid
  enodeToTree best

-- | Creates a singleton trie from an e-class id
trie :: EClassId -> IntMap IntTrie -> IntTrie
trie eid = IntTrie
{-# INLINE trie #-}

-- | Check whether an e-class is a constant value
isConst :: Monad m => EClassId -> EGraphST m Bool
isConst eid = do ec <- getEClass eid
                 case (_consts . _info) ec of
                   ConstVal _ -> pure True
                   _          -> pure False
{-# INLINE isConst #-}

getFitness :: Monad m => EClassId -> EGraphST m (Maybe Double)
getFitness c = (_fitness . _info) <$> getEClass c
{-# INLINE getFitness #-}
getTheta :: Monad m => EClassId -> EGraphST m ([Target])
getTheta c = (_theta . _info) <$> getEClass c
{-# INLINE getTheta #-}
getSize :: Monad m => EClassId -> EGraphST m Int
getSize c = (_size . _info) <$> getEClass c
{-# INLINE getSize #-}
isSizeOf :: (Int -> Bool) -> EClass -> Bool
isSizeOf p = p . _size . _info
{-# INLINE isSizeOf #-}
getBestFitness :: Monad m => EGraphST m (Maybe Double)
getBestFitness = do
    mbec <- gets (fmap snd . getGreatest . _fitRangeDB . _eDB)
    case mbec of
      Just bec -> (_fitness . _info) <$> getEClass bec
      Nothing  -> pure Nothing
getDL :: Monad m => EClassId -> EGraphST m (Maybe Double)
getDL c = (_dl . _info) <$> getEClass c
{-# INLINE getDL #-}
