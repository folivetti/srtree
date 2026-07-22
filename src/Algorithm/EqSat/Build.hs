{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.EqSat.Build
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Functions related to building and maintaining e-graphs
-- Heavily based on hegg (https://github.com/alt-romes/hegg by alt-romes)
--
-----------------------------------------------------------------------------

module Algorithm.EqSat.Build where

import System.Random (Random (randomR), StdGen)
import Control.Lens ( over )
import Control.Monad ( forM_, when, foldM, forM )
import Data.Maybe ( fromMaybe, catMaybes )
import Data.SRTree
import Algorithm.EqSat.Egraph
--import Algorithm.EqSat.Info
import Algorithm.EqSat.DB
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.HashSet as Set
import Control.Monad.State.Strict
import Control.Monad.Identity
import Data.SRTree.Recursion (cataM)
import Algorithm.EqSat.Info
import qualified Data.IntSet as IntSet
import Data.Maybe

import Data.List ( nub )
import qualified Data.Set as RangeSet
import Debug.Trace (trace, traceShow)

-- | adds a new or existing e-node (merging if necessary)
add :: Monad m => CostFun -> ENode -> EGraphST m EClassId
add costFun enode = do
  enode''   <- canonize enode
  constEnode <- calculateConsts enode''
  enode' <- case constEnode of
              ConstVal x -> pure $ Const x
              ParamIx  x -> pure $ Param x
              _          -> case enode'' of
                               Bin Sub c1 c2 ->
                                 do constType <- (_consts . _info) <$> getEClass c2
                                    pure $ case constType of
                                      ParamIx x -> Bin Add c1 c2
                                      _         -> enode''
                               Bin Div c1 c2 ->
                                 do constType <- (_consts . _info) <$> getEClass c2
                                    pure $ case constType of
                                      ParamIx x -> Bin Mul c1 c2
                                      _         -> enode''
                               _             -> pure $ enode''

  maybeEid <- gets (Map.lookup enode' . _eNodeToEClass)
  case maybeEid of
       Just eid -> pure eid
       Nothing  -> do
         curId <- gets (_nextId . _eDB)                             -- get the next available e-class id
         modify' $ over canonicalMap (IntMap.insert curId curId)           -- insert e-class id into canon map
                 . over eNodeToEClass (Map.insert enode' curId)     -- associate new e-node with id
                 . over (eDB . nextId) (+1)                                -- update next id
                 . over (eDB . worklist) (Set.insert (curId, enode'))      -- add e-node and id into worklist
         forM_ (childrenOf enode') (addParents curId enode')        -- update the children's parent list
         info <- makeAnalysis costFun enode'
         h    <- getChildrenMinHeight enode'
         let newClass = createEClass curId enode' info h              -- create e-class
         modify' $ over eClass (IntMap.insert curId newClass)              -- insert new e-class into e-graph
         --modifyEClass costFun curId                                 -- simplify eclass if it evaluates to a number

         -- update database
         addToDB enode' curId                                       -- add new node to db
         modify' $ over (eDB . sizeDB)
                 $ IntMap.insertWith (IntSet.union) (_size info) (IntSet.singleton curId)
         modify' $ over (eDB . unevaluated) (IntSet.insert curId)
                 . over (eDB . changed) (const True)
         pure curId
  where
    addParents :: Monad m => EClassId -> ENode -> EClassId -> EGraphST m ()
    addParents cId node c =
      do ec <- getEClass c
         let ec' = ec{ _parents = Set.insert (cId, node) (_parents ec) }
         modify' $ over eClass (IntMap.insert c ec')

-- | rebuilds the e-graph after inserting or merging
-- e-classes
rebuild :: Monad m => CostFun -> EGraphST m ()
rebuild costFun =
  do wl <- gets (_worklist . _eDB)
     al <- gets (_analysis . _eDB)
     modify' $ over (eDB . worklist) (const Set.empty)
             . over (eDB . analysis) (const Set.empty)
     forM_ wl (uncurry (repair costFun))
     forM_ al (uncurry (repairAnalysis costFun))
{-# INLINE rebuild #-}

-- | repairs e-node by canonizing its children
-- if the canonized e-node already exists in
-- e-graph, merge the e-classes
repair :: Monad m => CostFun -> EClassId -> ENode -> EGraphST m ()
repair costFun ecId enode =
  do modify' $ over eNodeToEClass (Map.delete enode)
     enode'  <- canonize enode
     ecId'   <- canonical ecId
     doExist <- gets (Map.lookup enode' . _eNodeToEClass)
     case doExist of
        Just ecIdCanon -> do mergedId <- merge costFun ecIdCanon ecId'
                             modify' $ over eNodeToEClass (Map.insert enode' mergedId)
        Nothing        -> modify' $ over eNodeToEClass (Map.insert enode' ecId')
{-# INLINE repair #-}

-- | repair the analysis of the e-class
-- considering the new added e-node
repairAnalysis :: Monad m => CostFun -> EClassId -> ENode -> EGraphST m ()
repairAnalysis costFun ecId enode =
  do ecId'  <- canonical ecId
     enode' <- canonize enode
     eclass <- getEClass ecId'
     info   <- makeAnalysis costFun enode'
     let newData = joinData (_info eclass) info
         eclass' = eclass { _info = newData }
     when (_info eclass /= newData) $
       do modify' $ over (eDB . analysis) (_parents eclass <>)
                  . over eClass (IntMap.insert ecId' eclass')
                   . over (eDB . refits) (IntSet.insert ecId')
          _ <- modifyEClass costFun ecId'
          pure ()
{-# INLINE repairAnalysis #-}

-- | merge to equivalent e-classes
merge :: Monad m => CostFun -> EClassId -> EClassId -> EGraphST m EClassId
merge costFun c1 c2 =
  do c1' <- canonical c1
     c2' <- canonical c2
     if c1' == c2'                                     -- if they are already merged, return canonical
       then pure c1'
       else do (led, ledC, ledOrig, sub, subC, subOrig) <- getLeaderSub c1' c1 c2' c2  -- the leader will be the e-class with more parents
               mergeClasses led ledC ledOrig sub subC subOrig         -- merge sub into leader
  where
    mergeClasses :: Monad m => EClassId -> EClass -> EClassId -> EClassId -> EClass -> EClassId -> EGraphST m EClassId
    mergeClasses led ledC ledO sub subC subO =
      do modify' $ over canonicalMap (IntMap.insert sub led . IntMap.insert subO led) -- points sub e-class to leader to maintain consistency
         let -- create new e-class with same id as led
             newC = EClass led
                           (_eNodes ledC `Set.union` _eNodes subC)
                           (_parents ledC <> _parents subC)
                           (min (_height ledC) (_height subC))
                           (joinData (_info ledC) (_info subC))

         modify' $ over eClass (IntMap.insert led newC . IntMap.delete sub) -- delete sub e-class and replace leader
                 . over (eDB . worklist) (_parents subC <>)         -- insert parents of sub into worklist
         when (_info newC /= _info ledC)                            -- if there was change in data,
           $ modify' $ over (eDB . analysis) (_parents ledC <>)     --   insert parents into analysis
                      . over (eDB . refits) (IntSet.insert led)
         when (_info newC /= _info subC)
           $ modify' $ over (eDB . analysis) (_parents subC <>)
         updateDBs newC led ledC ledO sub subC subO
         modifyEClass costFun led
         modify' $ over (eDB . changed) (const True)
         pure led

    getLeaderSub c1 c1O c2 c2O =
      do ec1 <- getEClass c1
         ec2 <- getEClass c2
         let n1 = Set.size (_parents ec1)
             n2 = Set.size (_parents ec2)
         pure $ if n1 >= n2
                  then (c1, ec1, c1O, c2, ec2, c2O)
                  else (c2, ec2, c2O, c1, ec1, c1O)

    updateDBs :: Monad m => EClass -> EClassId -> EClass -> EClassId -> EClassId -> EClass -> EClassId -> EGraphST m ()
    updateDBs newC led ledC ledO sub subC subO = do
      updateFitnessDB newC led ledC ledO sub subC subO
      updateSizeDB newC led ledC ledO sub subC subO

    updateSizeDB :: Monad m => EClass -> EClassId -> EClass -> EClassId -> EClassId -> EClass -> EClassId -> EGraphST m ()
    updateSizeDB newC led ledC ledO sub subC subO = do
      let sz  = (_size . _info) newC
          szL = (_size . _info) ledC
          szS = (_size . _info) subC
          fun = IntMap.adjust (IntSet.insert led) sz . IntMap.adjust (IntSet.delete led . IntSet.delete ledO) szL . IntMap.adjust (IntSet.delete sub . IntSet.delete subO) szS
      modify' $ over (eDB . sizeDB) fun

    updateFitnessDB :: Monad m => EClass -> EClassId -> EClass -> EClassId -> EClassId -> EClass -> EClassId -> EGraphST m ()
    updateFitnessDB newC led ledC ledO sub subC subO =
      case fitNew of
        Nothing -> modify' $ over (eDB . unevaluated) (IntSet.insert led . IntSet.delete ledO . IntSet.delete sub . IntSet.delete subO)
        Just fn -> do
          when (fitNew /= fitLed) $ do
            modify' $ case fitLed of
              Nothing -> over (eDB . unevaluated) (IntSet.delete led . IntSet.delete ledO)
              Just fl -> over (eDB . fitRangeDB) (removeRange led fl . removeRange ledO fl)
                       . over (eDB . sizeFitDB) (IntMap.adjust (removeRange ledO fl . removeRange led fl) szLed)
            modify' $ over (eDB . fitRangeDB) (insertRange led fn)
                    . over (eDB . sizeFitDB) (IntMap.adjust (insertRange led fn) szNew . IntMap.insertWith RangeSet.union szNew RangeSet.empty)
          modify' $ case fitSub of
            Nothing -> over (eDB . unevaluated) (IntSet.delete sub . IntSet.delete subO)
            Just fs -> over (eDB . fitRangeDB) (removeRange sub fs . removeRange subO fs)
                     . over (eDB . sizeFitDB) (IntMap.adjust (removeRange subO fs . removeRange sub fs) szSub)
      where
        fitNew = (_fitness . _info) newC
        fitLed = (_fitness . _info) ledC
        fitSub = (_fitness . _info) subC
        szNew  = (_size . _info) newC
        szLed  = (_size . _info) ledC
        szSub  = (_size . _info) subC

-- | modify an e-class, e.g., add constant e-node and prune non-leaves
modifyEClass :: Monad m => CostFun -> EClassId -> EGraphST m EClassId
modifyEClass costFun ecId =
  do ec <- getEClass ecId
     case (_consts . _info) ec of
       ConstVal x ->
         do let en = Const x
            c <- calculateCost costFun en
            let infoEc = (_info ec){ _cost = c, _best = en, _consts = toConst en }
            maybeEid <- gets (Map.lookup en . _eNodeToEClass)
            modify' $ over eClass (IntMap.insert ecId ec{_eNodes = Set.singleton en , _info = infoEc})
            when (isJust $ _fitness $ _info ec) $ modify' $ over (eDB . refits) (IntSet.insert ecId)
            case maybeEid of
              Nothing   -> pure ecId
              Just eid' -> merge costFun eid' ecId

       ParamIx x ->
         do let en = Param x
            c <- calculateCost costFun en
            let infoEc = (_info ec){ _cost = c, _best = en, _consts = toConst en }
            maybeEid <- gets (Map.lookup en . _eNodeToEClass)
            modify' $ over eClass (IntMap.insert ecId ec{_eNodes = Set.insert en (_eNodes ec), _info = infoEc})
            when (isJust $ _fitness $ _info ec) $ modify' $ over (eDB . refits) (IntSet.insert ecId)
            case maybeEid of
              Nothing   -> pure ecId
              Just eid' -> merge costFun eid' ecId

       _ -> pure ecId

  where
    isTerm (Var _)   = True
    isTerm (Const _) = True
    isTerm (Param _) = True
    isTerm _         = False

    toConst (Param ix) = ParamIx ix
    toConst (Const x)  = ConstVal x
    toConst _          = NotConst

-- * DB

-- | `createDB` creates a database of patterns from an e-graph
-- it simply calls addToDB for every pair (e-node, e-class id) from
-- the e-graph.
createDB :: Monad m => EGraphST m DB
createDB = do modify' $ over (eDB . patDB) (const Map.empty)
              ecls <- gets (Map.toList . _eNodeToEClass)
              mapM_ (uncurry addToDB) ecls
              gets (_patDB . _eDB)
{-# INLINE createDB #-}

createDBBest :: Monad m => EGraphST m DB
createDBBest = do modify' $ over (eDB . patDB) (const Map.empty)
                  ecls <- gets (Prelude.map (\(eId, ec) -> (_best (_info ec), eId)) . IntMap.toList . _eClass)
                  mapM_ (uncurry addToDB) ecls
                  gets (_patDB . _eDB)

-- | `addToDB` adds an e-node and e-class id to the database
addToDB :: Monad m => ENode -> EClassId -> EGraphST m () -- State DB ()
addToDB enode' eid = do
  eid' <- canonical eid
  isConst <- (_consts . _info) <$> getEClass eid'
  let enode = case isConst of
                ConstVal x -> Const x
                ParamIx  x -> Param x
                _          -> enode'
  let ids = eid : childrenOf enode -- we will add the e-class id and the children ids
      op  = getOperator enode    -- changes Bin op l r to Bin op () () so `op` as a single entry in the DB
  trie <- gets (Map.lookup op . _patDB . _eDB)
  case populate trie ids of      -- populates the trie
    Nothing -> pure ()
    Just t  -> modify' $ over (eDB . patDB) (Map.insert op t) -- if something was created, insert back into the DB
{-# INLINE addToDB #-}

-- | Populates an IntTrie with a sequence of e-class ids
populate :: Maybe IntTrie -> [EClassId] -> Maybe IntTrie
populate _ []         = Nothing
populate Nothing eids = foldr f Nothing eids
  where
    f :: EClassId -> Maybe IntTrie -> Maybe IntTrie
    f eid (Just t) = Just $ IntTrie (IntMap.singleton eid t)
    f eid Nothing  = Just $ IntTrie (IntMap.singleton eid (IntTrie IntMap.empty))
populate (Just tId) (eid:eids) = let nextTrie = IntMap.lookup eid (_trie tId)
                                     val      = fromMaybe (IntTrie IntMap.empty) $ populate nextTrie eids
                                  in Just $ IntTrie (IntMap.insert eid val (_trie tId))
{-# INLINE populate #-}

canonizeMap :: Monad m => (Map ClassOrVar ClassOrVar, ClassOrVar) -> EGraphST m (Map ClassOrVar ClassOrVar, ClassOrVar)
canonizeMap (subst, cv) = (,cv) <$> traverse g subst -- Map.fromList <$> traverse f (Map.toList subst)
  where
    g :: Monad m => ClassOrVar -> EGraphST m ClassOrVar
    g (Left e2) = Left <$> canonical e2
    g e2        = pure e2

    f :: Monad m => (ClassOrVar, ClassOrVar) -> EGraphST m (ClassOrVar, ClassOrVar)
    f (e1, Left e2) = do e2' <- canonical e2
                         pure (e1, Left e2')
    f (e1, e2)      = pure (e1, e2)
{-# INLINE canonizeMap #-}

applyMatch :: Monad m => CostFun -> Rule -> (Map ClassOrVar ClassOrVar, ClassOrVar) -> EGraphST m ()
applyMatch costFun rule match' =
  do let conds = getConditions rule
     match       <- canonizeMap match'
     validHeight <- isValidHeight match
     validConds  <- mapM (`isValidConditions` match) conds
     when (validHeight && and validConds) $
       do new_eclass <- reprPrat costFun (fst match) (target rule)
          merge costFun (getInt (snd match)) new_eclass
          pure ()
{-# INLINE applyMatch #-}

applyMergeOnlyMatch :: Monad m => CostFun -> Rule -> (Map ClassOrVar ClassOrVar, ClassOrVar) -> EGraphST m ()
applyMergeOnlyMatch costFun rule match' =
  do let conds = getConditions rule
     match       <- canonizeMap match'
     validHeight <- isValidHeight match
     validConds  <- mapM (`isValidConditions` match) conds
     when (validHeight && and validConds) $
       do maybe_eid <- classOfENode costFun (fst match) (target rule)
          case maybe_eid of
            Nothing  -> pure ()
            Just eid -> do merge costFun (getInt (snd match)) eid
                           pure ()
{-# INLINE applyMergeOnlyMatch #-}

-- | gets the e-node of the target of the rule
-- TODO: add consts and modify
classOfENode :: Monad m => CostFun -> Map ClassOrVar ClassOrVar -> Pattern -> EGraphST m (Maybe EClassId)
classOfENode costFun subst (VarPat c)     = do let maybeEid = getInt <$> Map.lookup (Right (fromEnum c)) subst
                                               case maybeEid of
                                                 Nothing  -> pure Nothing
                                                 Just eid -> Just <$> canonical eid
classOfENode costFun subst (Fixed (Const x)) = Just <$> add costFun (Const x)
classOfENode costFun subst (Fixed target) = do newChildren <- mapM (classOfENode costFun subst) (getElems target)
                                               case sequence newChildren of
                                                 Nothing -> pure Nothing
                                                 Just cs -> do let new_enode = replaceChildren cs target
                                                               cs' <- mapM canonical cs
                                                               areConsts <- mapM isConst cs'
                                                               if and areConsts
                                                                 then do eid <- add costFun new_enode
                                                                         rebuild costFun -- eid new_enode
                                                                         pure (Just eid)
                                                                 else gets (Map.lookup new_enode . _eNodeToEClass)
{-# INLINE classOfENode #-}

-- | adds the target of the rule into the e-graph
reprPrat :: Monad m => CostFun -> Map ClassOrVar ClassOrVar -> Pattern -> EGraphST m EClassId
reprPrat costFun subst (VarPat c)     = canonical $ getInt $ subst Map.! Right (fromEnum c)
reprPrat costFun subst (Fixed target) = do newChildren <- mapM (reprPrat costFun subst) (getElems target)
                                           add costFun (replaceChildren newChildren target)
{-# INLINE reprPrat #-}

isValidHeight :: Monad m => (Map ClassOrVar ClassOrVar, ClassOrVar) -> EGraphST m Bool
isValidHeight match = do
      h <- case snd match of
             Left ec -> _height <$> getEClass ec
             Right _ -> pure 0
      pure $ h < 15
{-# INLINE isValidHeight #-}

-- | returns `True` if the condition of a rule is valid for that match
isValidConditions :: Monad m => Condition -> (Map ClassOrVar ClassOrVar, ClassOrVar) -> EGraphST m Bool
isValidConditions cond match = gets $ cond (fst match)
{-# INLINE isValidConditions #-}

-- * Tree to e-graph conversion and utility functions

-- | Creates an e-graph from an expression tree
fromTree :: Monad m => CostFun -> Fix SRTree -> EGraphST m EClassId
fromTree costFun = cataM sequence (add costFun)
{-# INLINE fromTree #-}

-- | Builds an e-graph from multiple independent trees
fromTrees :: Monad m => CostFun -> [Fix SRTree] -> EGraphST m [EClassId]
fromTrees costFun = foldM (\rs t -> do eid <- fromTree costFun t; pure (eid:rs)) []
{-# INLINE fromTrees #-}

countParamsEg :: EGraph -> EClassId -> Int
countParamsEg eg rt = countParams . runIdentity $ getBestExpr rt `evalStateT` eg
countParamsUniqEg :: EGraph -> EClassId -> Int
countParamsUniqEg eg rt = countParamsUniq . runIdentity $ getBestExpr rt `evalStateT` eg


-- | gets the best expression given the default cost function
getBestExpr :: Monad m => EClassId -> EGraphST m (Fix SRTree)
getBestExpr eid = do best <- (_best . _info) <$> getEClass eid
                     childs <- mapM getBestExpr $ childrenOf best
                     pure . Fix $ replaceChildren childs best

getBestENode eid = (_best . _info) <$> getEClass eid
{-# INLINE getBestENode #-}

-- | returns one expression rooted at e-class `eId`
-- TODO: avoid loopings
getExpressionFrom :: Monad m => EClassId -> EGraphST m (Fix SRTree)
getExpressionFrom eId' = do
    nodes <- _eNodes <$> getEClass eId'
    case Set.toList nodes of
      (n:_) -> Fix <$> case n of
        Bin op l r -> Bin op <$> getExpressionFrom l <*> getExpressionFrom r
        Uni f t    -> Uni f <$> getExpressionFrom t
        Var ix     -> pure $ Var ix
        Const x    -> pure $ Const x
        Param ix   -> pure $ Param ix
      [] -> error "getExpressionFrom: empty eclass"
{-# INLINE getExpressionFrom #-}

-- | returns all expressions rooted at e-class `eId`
-- TODO: check for infinite list
getAllExpressionsFrom :: Monad m => EClassId -> EGraphST m [Fix SRTree]
getAllExpressionsFrom eId' = do
  nodes <- Set.toList . _eNodes <$> getEClass eId'
  go nodes
  where
    go []     = pure []
    go (n:ns) = do
        t <- Prelude.map Fix <$> case n of
                Bin op l r -> do l' <- getAllExpressionsFrom l
                                 r' <- getAllExpressionsFrom r
                                 pure $ [Bin op li ri | li <- l', ri <- r']
                Uni f t    -> Prelude.map (Uni f) <$> getAllExpressionsFrom t
                Var ix     -> pure [Var ix]
                Const x    -> pure [Const x]
                Param ix   -> pure [Param ix]
        ts <- go ns
        pure (t ++ ts)
{-# INLINE getAllExpressionsFrom #-}

getNExpressionsFrom :: Monad m => Int -> EClassId -> EGraphST m [Fix SRTree]
getNExpressionsFrom n eId' = getNExpressionsFrom' n 15 eId' 

getNExpressionsFrom' :: Monad m => Int -> Int -> EClassId -> EGraphST m [Fix SRTree]
getNExpressionsFrom' _ 0 _ = pure []
getNExpressionsFrom' n d eId' = do
  nodes <- Set.toList . _eNodes <$> getEClass eId'
  (concat <$> go n d nodes)
  where
    isTerm (Var _) = True
    isTerm (Const _) = True
    isTerm (Param _) = True
    isTerm _ = False
    toTree (Var ix) = Fix $ Var ix
    toTree (Const x) = Fix $ Const x
    toTree (Param ix) = Fix $ Param ix
    toTree _ = undefined

    go n' _ []     = pure []
    go n' 0 ts     = pure []
    go n' d (node:ns) = do
        tt <- Prelude.map Fix <$> case node of
                Bin op l r -> do l' <- getNExpressionsFrom' n' (d-1) l
                                 r' <- getNExpressionsFrom' n' (d-1) r
                                 pure $ Prelude.take n [Bin op li ri | li <- l', ri <- r']
                Uni f t    -> Prelude.map (Uni f) <$> getNExpressionsFrom' n' (d-1) t
                Var ix     -> pure [Var ix]
                Const x    -> pure [Const x]
                Param ix   -> pure [Param ix]
        let n'' = n' - length tt
        if n'' <= 0
          then pure [tt]
          else do ts <- go n'' (d-1) ns
                  pure (tt:ts)

getNEclassFrom :: Monad m => Int -> EClassId -> EGraphST m [[EClassId]]
getNEclassFrom n eid = getNEclassFrom' n 15 eid

getNEclassFrom' :: Monad m => Int -> Int -> EClassId -> EGraphST m [[EClassId]]
getNEclassFrom' _ 0 _ = pure []
getNEclassFrom' n d eId' = do
  eId <- canonical eId'
  nodes <- Set.toList . _eNodes <$> getEClass eId'
  (Prelude.map (eId:) <$> go n d nodes)
  where
    --go :: Int -> Int -> [ENode] -> EGraphST m [[EClassId]]
    go n' _ []     = pure []
    go n' 0 ts     = pure []
    go n' d (node:ns) = do
        tt <- case node of
                Bin op l r -> do l' <- getNEclassFrom' n' (d-1) l
                                 r' <- getNEclassFrom' n' (d-1) r
                                 pure $ Prelude.take n [li <> ri | li <- l', ri <- r']
                Uni f t    -> getNEclassFrom' n' (d-1) t -- [[eid2:eid1]]
                Var ix     -> pure [[]]
                Const x    -> pure [[]]
                Param ix   -> pure [[]]
        pure tt
        --let n'' = n' - length tt
        --if n'' <= 0
        --  then pure [tt]
        --  else do ts <- go n'' (d-1) ns
        --          pure (tt:ts)

getAllChildEClasses :: Monad m => EClassId -> EGraphST m [EClassId]
getAllChildEClasses eId' = do
  eId <- canonical eId'
  IntSet.toList <$> go [eId] IntSet.empty

  where
    hasNoTerminal :: [ENode] -> Bool
    hasNoTerminal = all (not . null . childrenOf) 
    getNodes :: Monad m => EClassId -> EGraphST m [ENode]
    getNodes n = Set.toList . _eNodes <$> getEClass n

    go :: Monad m => [Int] -> IntSet.IntSet -> EGraphST m IntSet.IntSet
    go [] visited = pure visited
    go queue visited = do 
        nodes <- concatMap childrenOf . concat . filter hasNoTerminal <$> mapM getNodes queue
        eids <- filter (\e -> e `IntSet.notMember` visited) <$> (mapM canonical nodes)
        go eids (visited `IntSet.union` IntSet.fromList queue)
            {-
    go n = do nodes <- gets (map decodeEnode . Set.toList . _eNodes . (IntMap.! n) . _eClass)
              let hasTerminal = any (null . childrenOf) nodes
              eids <- mapM canonical $ concatMap childrenOf nodes
              if hasTerminal
                then pure [n]
                else do eids' <- mapM go eids
                        pure ((n : eids) <> concat eids')
                        -}
{-# INLINE getAllChildEClasses #-}

getAllChildBestEClasses :: Monad m => EClassId -> EGraphST m [EClassId]
getAllChildBestEClasses eId' = do
  nub <$> go eId'
  where
    go :: Monad m => EClassId -> EGraphST m [EClassId]
    go n = do node <- (_best . _info) <$> getEClass n
              let hasTerminal = (null . childrenOf) node
              eids <- mapM canonical $ childrenOf node
              if hasTerminal
                then pure [n]
                else do eids' <- mapM go eids
                        pure ((n : eids) <> concat eids')

getAllChildBestEClassesRep :: Monad m => EClassId -> EGraphST m [EClassId]
getAllChildBestEClassesRep eId' = do
  go eId'
  where
    go :: Monad m => EClassId -> EGraphST m [EClassId]
    go n = do node <- (_best . _info) <$> getEClass n
              let hasTerminal = (null . childrenOf) node
              eids <- mapM canonical $ childrenOf node
              if hasTerminal
                then pure [n]
                else do eids' <- mapM go eids
                        pure (n : concat eids')

-- | returns a random expression rooted at e-class `eId`
getRndExpressionFrom :: EClassId -> EGraphST (State StdGen) (Fix SRTree)
getRndExpressionFrom eId' = do
    nodes <- Set.toList . _eNodes <$> getEClass eId'
    n <- lift $ randomFrom nodes
    Fix <$> case n of
              Bin op l r -> Bin op <$> getRndExpressionFrom l <*> getRndExpressionFrom r
              Uni f t    -> Uni f <$> getRndExpressionFrom t
              Var ix     -> pure $ Var ix
              Const x    -> pure $ Const x
              Param ix   -> pure $ Param ix
  where
    randomRange rng = state (randomR rng)
    randomFrom xs   = do n <- randomRange (0, length xs - 1)
                         pure $ xs !! n
{-# INLINE getRndExpressionFrom #-}

cleanMaps :: Monad m => EGraphST m ()
cleanMaps = do
  enode2eclass <- gets _eNodeToEClass
  entries <- forM (Map.toList enode2eclass) $ \(k,v) -> do
    k' <- canonize k
    v' <- canonical v
    pure (k',v')
  let enode2eclass' = Map.fromList entries
  eclassMap <- gets _eClass
  entries' <- forM (IntMap.toList eclassMap) $ \(k,v) -> do
    k' <- canonical k
    pure $ if k==k' then (Just (k,v)) else Nothing
  let eclassMap' = IntMap.fromList (catMaybes entries')
  canon' <- gets (IntMap.filterWithKey (\k v -> k == v) . _canonicalMap)
  eDB' <- gets _eDB
  put $ EGraph canon' enode2eclass' eclassMap' eDB'
{-# INLINE cleanMaps #-}
