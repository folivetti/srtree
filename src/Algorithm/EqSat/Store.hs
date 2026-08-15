{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Algorithm.EqSat.Store
  ( GraphRows(..)
  , EClassRow(..)
  , exportEGraph
  , importEGraph
  , mergeEGraph
  , rebuildDBs
  ) where

import Control.Lens ( over )
import Control.Monad ( forM, forM_, foldM )
import Control.Monad.Identity ( Identity, runIdentity )
import Control.Monad.State.Strict ( StateT, execStateT, modify', gets )
import GHC.Generics ( Generic )
import GHC.Stack ( HasCallStack )

import qualified Data.HashMap.Strict as HashMap
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashSet as Set
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict ( IntMap )
import qualified Data.IntSet as IntSet
import qualified Data.Set as RangeSet
import Data.List ( sortOn )

import Data.SRTree
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Build

-- | Row representation of the core (structural) state of an e-graph,
-- normalized for external storage (e.g. a relational DB).
data GraphRows = GraphRows
  { _grCanonical     :: IntMap EClassId                    -- ^ eid -> canonical representative (self-loop for roots)
  , _grENodeToEClass :: HashMap ENode EClassId             -- ^ canonical e-node -> its e-class
  , _grEClasses      :: IntMap EClassRow                   -- ^ canonical e-class id -> data row
  , _grNextId        :: Int                                -- ^ next free e-class id
  , _grTrackDBs      :: Bool                               -- ^ whether range DBs are maintained
  } deriving (Show, Eq, Generic)

-- | Per-e-class data row.
data EClassRow = EClassRow
  { _rcNodes   :: Set.HashSet ENode
  , _rcParents :: Set.HashSet (EClassId, ENode)
  , _rcHeight  :: Int
  , _rcInfo    :: EClassData
  } deriving (Show, Eq, Generic)

-- | Export the core structural state of an e-graph into a normalised row format.
exportEGraph :: EGraph -> GraphRows
exportEGraph eg = GraphRows
  { _grCanonical     = _canonicalMap eg
  , _grENodeToEClass = _eNodeToEClass eg
  , _grEClasses      = IntMap.map toRow (_eClass eg)
  , _grNextId        = _nextId (_eDB eg)
  , _grTrackDBs      = _trackDBs (_eDB eg)
  }
  where
    toRow ec = EClassRow (_eNodes ec) (_parents ec) (_height ec) (_info ec)

-- | Reconstruct an e-graph from normalised rows, rebuilding all derived indexes.
--
-- Real e-graphs may carry stale @_eNodeToEClass@ entries left behind by
-- merges (a node pointing at a class whose canonical representative is
-- another class). Such entries are canonicalized at import: node -> class
-- values are routed through the canonical map and any non-root class rows
-- are dropped. Parent pointers are recomputed from the canonicalized node
-- map so they never reference dead classes.
importEGraph :: GraphRows -> Either String EGraph
importEGraph rows
  | not (validate rows) = Left (validationMsg rows)
  | otherwise           = Right (runIdentity $ execStateT rebuildDBs (buildCore (canonicalize rows)))

-- | Normalize stale rows: route node->class values through the canonical map
-- and drop non-root class rows.
--
-- Parent pointers come from the stored @_rcParents@ when a class has any
-- (e.g. after a storage-layer round-trip through the @parent@ table); parent
-- class ids are routed through the canonical map so they never reference dead
-- classes. Classes without stored parents (legacy rows, hand-built rows) fall
-- back to recomputing parents from the canonicalized node map.
canonicalize :: GraphRows -> GraphRows
canonicalize rows =
  let canon    = _grCanonical rows
      rep eid  = IntMap.findWithDefault eid eid canon
      nodeMap' = HashMap.map rep (_grENodeToEClass rows)
      classes' = IntMap.filterWithKey
                   (\eid _ -> IntMap.lookup eid canon == Just eid)
                   (_grEClasses rows)
      parents' = IntMap.fromListWith Set.union
        [ (c, Set.singleton (eid, en))
        | (en, eid) <- HashMap.toList nodeMap'
        , c <- eChildren en ]
      stored'  = IntMap.mapWithKey
                   (\_ r -> Set.map (\(pEid, pEn) -> (rep pEid, pEn)) (_rcParents r))
                   classes'
      fixRow eid r =
        let stored = IntMap.findWithDefault Set.empty eid stored'
        in r { _rcParents = if Set.null stored
                              then IntMap.findWithDefault Set.empty eid parents'
                              else stored }
  in rows { _grENodeToEClass = nodeMap'
          , _grEClasses      = IntMap.mapWithKey fixRow classes' }

buildCore :: GraphRows -> EGraph
buildCore rows = EGraph
  { _canonicalMap     = _grCanonical rows
  , _eNodeToEClass    = _grENodeToEClass rows
  , _eClass           = IntMap.mapWithKey mkEClass (_grEClasses rows)
  , _eDB              = (emptyDB){ _nextId = _grNextId rows, _trackDBs = _grTrackDBs rows }
  , _classStore       = Nothing
  }
  where
    mkEClass eid r = EClass eid (_rcNodes r) (_rcParents r) (_rcHeight r) (_rcInfo r)

rebuildDBs :: EGraphST Identity ()
rebuildDBs = do
  -- Rebuild the pattern database from the canonical e-node -> class mapping
  nodes <- gets _eNodeToEClass
  forM_ (HashMap.toList nodes) $ \(en, eid) -> addToDB en eid

  -- Rebuild range/size indexes from class info
  classes <- gets _eClass
  forM_ (IntMap.toList classes) $ \(eid, ec) -> do
    let info = _info ec
        sz   = _size info
        fit  = _fitness info
        dl   = _dl info
    modify' $ over (eDB . sizeDB) (IntMap.insertWith IntSet.union sz (IntSet.singleton eid))
    case fit of
      Nothing -> modify' $ over (eDB . unevaluated) (IntSet.insert eid)
      Just fn -> modify' $ over (eDB . fitRangeDB) (insertRange eid fn)
                        . over (eDB . sizeFitDB) (IntMap.insertWith RangeSet.union sz (RangeSet.singleton (fn, eid)))
    case dl of
      Nothing -> pure ()
      Just dn -> modify' $ over (eDB . dlRangeDB) (insertRange eid dn)
                        . over (eDB . sizeDLDB) (IntMap.insertWith RangeSet.union sz (RangeSet.singleton (dn, eid)))

-- | Validate that the exported rows form a consistent graph.
--
-- All referenced ids must be present in the canonical map. Node -> class
-- values and class rows may reference classes that are not their own
-- canonical representative (stale entries left behind by merges); those are
-- repaired by 'canonicalize' during import.
validate :: GraphRows -> Bool
validate rows =
  let canon      = _grCanonical rows
      classes    = _grEClasses rows
      nodeIds    = HashMap.keys (_grENodeToEClass rows)
      extraIds   = IntMap.keys classes
                   ++ HashMap.elems (_grENodeToEClass rows)
                   ++ concatMap eChildren nodeIds
      inCanon    = all (`IntMap.member` canon) extraIds
      nextOk     = _grNextId rows >= 0
  in inCanon && nextOk

validationMsg :: GraphRows -> String
validationMsg rows
  | not inCanon = "some e-node/e-class id is not present in the canonical map"
  | not nextOk  = "next id is negative"
  | otherwise   = "invalid GraphRows"
  where
    canon      = _grCanonical rows
    classes    = _grEClasses rows
    nodeIds    = HashMap.keys (_grENodeToEClass rows)
    extraIds   = IntMap.keys classes
                 ++ HashMap.elems (_grENodeToEClass rows)
                 ++ concatMap eChildren nodeIds
    inCanon    = all (`IntMap.member` canon) extraIds
    nextOk     = _grNextId rows >= 0

-- | Return canonical e-class ids ordered children-before-parents (ascending height).
classOrder :: GraphRows -> Either String [EClassId]
classOrder rows =
  Right $ map fst $ sortOn (_rcHeight . snd) $ IntMap.toAscList (_grEClasses rows)

-- | Remap a B-e-graph's e-node into A's id-space using the correspondence map.
remapNode
  :: GraphRows               -- ^ rows of graph B (source)
  -> IntMap EClassId         -- ^ corr: B canonical id -> A id
  -> ENode
  -> Either String ENode
remapNode rowsB corr = go
  where
    canonB :: EClassId -> EClassId
    canonB cid = IntMap.findWithDefault cid cid (_grCanonical rowsB)

    toA :: EClassId -> Either String EClassId
    toA cid =
      case IntMap.lookup (canonB cid) corr of
        Just eidA -> Right eidA
        Nothing   -> Left ("child " <> show cid <> " of graph B not yet merged")

    go (EVar ix)     = Right (EVar ix)
    go (EParam ix)   = Right (EParam ix)
    go (EConst x)    = Right (EConst x)
    go (EUni f t)    = EUni f <$> toA t
    go (EBin op l r) = EBin op <$> toA l <*> toA r
    go (ENAry op m)  = do
      m' <- foldM step IntMap.empty (IntMap.toList m)
      Right (ENAry op m')
      where
        step acc (cid, n) = do
          cidA <- toA cid
          pure (IntMap.insertWith (+) cidA n acc)

-- | Merge class ids by unioning their e-classes under the given cost function.
mergeClass :: HasCallStack => CostFun -> EClassId -> EClassId -> EGraphST Identity EClassId
mergeClass costFun x y =
  if x == y then pure x else merge costFun x y

-- | Structurally merge graph @b@ into a copy of graph @a@.
--
-- The e-nodes of @b@ are canonicalized under @a@'s id space, deduplicated
-- against @a@'s existing content, and equivalent classes are unioned. Cost and
-- best of newly introduced content are computed with @costFun@ (i.e. merging
-- adopts @a@'s cost function). Dataset-specific values (fitness/DL/theta) are
-- NOT transferred: they are per-dataset data managed by the storage layer.
mergeEGraph :: HasCallStack => CostFun -> EGraph -> EGraph -> Either String EGraph
mergeEGraph costFun a b =
  let rowsB = exportEGraph b
  in case classOrder rowsB of
       Left err -> Left err
       Right order -> Right (runIdentity $ execStateT (step IntMap.empty order) a)
  where
    step :: IntMap EClassId -> [EClassId] -> EGraphST Identity ()
    step _ [] = rebuild costFun
    step corr (bCanon : rest) = do
      let ec = _grEClasses rowsB IntMap.! bCanon
      resolved <- forM (Set.toList (_rcNodes ec)) $ \en ->
        case remapNode rowsB corr en of
          Left err  -> pure (Left err)
          Right enA -> Right <$> add costFun enA
      case sequence resolved of
        Left err  -> error ("mergeEGraph: " <> err)  -- pre-validated
        Right []  -> step corr rest
        Right (x : xs) -> do
          rep <- foldM (mergeClass costFun) x xs
          step (IntMap.insert bCanon rep corr) rest
    rowsB = exportEGraph b
