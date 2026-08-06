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
import Data.Maybe
import Data.SRTree
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.DB
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as Set
import Control.Monad.State.Strict
import Control.Monad.Identity
import GHC.Stack (HasCallStack)
import Data.SRTree.Recursion (cataM)
import Data.List (sort)
import Algorithm.EqSat.Info
import qualified Data.IntSet as IntSet

import qualified Data.Set as RangeSet

 -- TEMP instrumentation (EGGP_STATS=1), removed after measurement
 -- (refit-cause counter)
 -- end TEMP instrumentation


-- | adds a new or existing e-node (merging if necessary)
add :: (Monad m, HasCallStack) => CostFun -> ENode -> EGraphST m EClassId
add costFun enode = do
  enode''   <- canonize enode
  constEnode <- calculateConsts enode''
  enode' <- case constEnode of
              ConstVal x -> pure $ EConst x
              ParamIx  x -> pure $ EParam x
              _          -> pure enode''
  enode''' <- foldConstants costFun enode'

  maybeEid <- gets (HashMap.lookup enode''' . _eNodeToEClass)
  case maybeEid of
       Just eid -> pure eid
       Nothing  -> do
         curId <- gets (_nextId . _eDB)                             -- get the next available e-class id
         modify' $ over canonicalMap (IntMap.insert curId curId)           -- insert e-class id into canon map
                 . over eNodeToEClass (HashMap.insert enode''' curId)     -- associate new e-node with id
                 . over (eDB . nextId) (+1)                                -- update next id
                 . over (eDB . worklist) (Set.insert (curId, enode'''))      -- add e-node and id into worklist
         forM_ (eChildren enode''') (addParents curId enode''')        -- update the children's parent list
         info <- makeAnalysis costFun enode'''
         h    <- getChildrenMinHeight enode'''
         let newClass = createEClass curId enode''' info h              -- create e-class
         modify' $ over eClass (IntMap.insert curId newClass)              -- insert new e-class into e-graph
         --modifyEClass costFun curId                                 -- simplify eclass if it evaluates to a number

         -- update database
         addToDB enode''' curId                                       -- add new node to db
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

-- | Add a binary (SRTree-based) node, converting it to a flattened ENode.
-- Sub and Div are canonicalized away at insertion: `x - y` becomes
-- `x + (-1)*y` and `x / y` becomes `x * recip y`, so no Sub/Div e-node ever
-- enters the e-graph and the Sub/Div-aware rules become redundant.
addTree :: (Monad m, HasCallStack) => CostFun -> SRTree EClassId -> EGraphST m EClassId
addTree costFun (Bin Sub l r) = do
  neg <- addNegate costFun r
  add costFun =<< mkENary EAdd [l, neg]
addTree costFun (Bin Div l r) = do
  l' <- canonical l
  r' <- canonical r
  rec <- add costFun (EUni Recip r')
  add costFun =<< mkENary EMul [l', rec]
addTree costFun t = toENode t >>= add costFun
{-# INLINE addTree #-}

-- | builds the e-class for the negation of the e-class `t`, represented as
-- `(-1) * t` (matching the pattern-level `negate` encoding in Algorithm.EqSat.DB).
addNegate :: (Monad m, HasCallStack) => CostFun -> EClassId -> EGraphST m EClassId
addNegate costFun t = do
  negOne <- add costFun (EConst (-1))
  t' <- canonical t
  add costFun =<< mkENary EMul [negOne, t']

-- | Fold together all-but-one constant children of an ENAry at insertion
-- time (e.g. 2+3+x becomes 5+x). Constants that are already folded
-- single subtrees are handled by 'calculateConsts' above; this handles the
-- flattened case where several constant terms land in one multiset.
foldConstants :: (Monad m, HasCallStack) => CostFun -> ENode -> EGraphST m ENode
foldConstants costFun en@(ENAry op xs) = do
  infos <- mapM (fmap (_consts . _info) . getEClass) xs
  let (consts, rest) = foldr step ([], []) (zip xs infos)
      step (_, ConstVal v) (cs, rs) | not (isNaN v) && not (isInfinite v) = (v:cs, rs)
      step (x, _)          (cs, rs)              = (cs, x:rs)
  if length consts >= 2
    then do
      let folded = case op of
                     EAdd -> sum consts
                     EMul -> product consts
      if isNaN folded || isInfinite folded
        then pure en
        else do
          cid <- add costFun (EConst folded)
          pure (ENAry op (sort (cid : rest)))
    else pure en
foldConstants _ en = pure en

-- | rebuilds the e-graph after inserting or merging
-- e-classes
rebuild :: (Monad m, HasCallStack) => CostFun -> EGraphST m ()
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
repair :: (Monad m, HasCallStack) => CostFun -> EClassId -> ENode -> EGraphST m ()
repair costFun ecId enode =
  do modify' $ over eNodeToEClass (HashMap.delete enode)
     enode'  <- canonize enode
     ecId'   <- canonical ecId
     doExist <- gets (HashMap.lookup enode' . _eNodeToEClass)
     case doExist of
        Just ecIdCanon -> do mergedId <- merge costFun ecIdCanon ecId'
                             modify' $ over eNodeToEClass (HashMap.insert enode' mergedId)
                             addToDB enode' mergedId
        Nothing        -> do modify' $ over eNodeToEClass (HashMap.insert enode' ecId')
                             addToDB enode' ecId'
{-# INLINE repair #-}

-- | repair the analysis of the e-class
-- considering the new added e-node
repairAnalysis :: (Monad m, HasCallStack) => CostFun -> EClassId -> ENode -> EGraphST m ()
repairAnalysis costFun ecId enode =
  do ecId'  <- canonical ecId
     enode' <- canonize enode
     eclass <- getEClass ecId'
     info   <- makeAnalysis costFun enode'
     let newData = joinData (_info eclass) info
         eclass' = eclass { _info = newData }
     when (_info eclass /= newData) $
       do let bestChanged = _best (_info eclass) /= _best newData
          modify' $ over (eDB . analysis) (_parents eclass <>)
                  . over eClass (IntMap.insert ecId' eclass')
                   . (if bestChanged && isJust (_fitness (_info eclass)) then over (eDB . refits) (IntSet.insert ecId') else id)
          _ <- modifyEClass costFun ecId'
          pure ()
{-# INLINE repairAnalysis #-}

-- | merge to equivalent e-classes
merge :: (Monad m, HasCallStack) => CostFun -> EClassId -> EClassId -> EGraphST m EClassId
merge costFun c1 c2 =
  do c1' <- canonical c1
     c2' <- canonical c2
     if c1' == c2'                                     -- if they are already merged, return canonical
       then pure c1'
       else do (led, ledC, ledOrig, sub, subC, subOrig) <- getLeaderSub c1' c1 c2' c2  -- the leader will be the e-class with more parents
               mergeClasses led ledC ledOrig sub subC subOrig         -- merge sub into leader
  where
    mergeClasses :: (Monad m, HasCallStack) => EClassId -> EClass -> EClassId -> EClassId -> EClass -> EClassId -> EGraphST m EClassId
    mergeClasses led ledC ledO sub subC subO =
      do modify' $ over canonicalMap (IntMap.insert sub led . IntMap.insert subO led)
         let newC = EClass led
                         (_eNodes ledC `Set.union` _eNodes subC)
                         (_parents ledC <> _parents subC)
                         (min (_height ledC) (_height subC))
                         (joinData (_info ledC) (_info subC))
         modify' $ \eg -> eg { _eNodeToEClass = Set.foldl' (\acc en -> HashMap.insert en led acc) (_eNodeToEClass eg) (_eNodes subC) }
         modify' $ over eClass (IntMap.insert led newC . IntMap.delete sub)
                 . over (eDB . worklist) (_parents subC <>)
         when (_info newC /= _info ledC)
           $ do let bestChanged = _best (_info newC) /= _best (_info ledC)
                modify' $ over (eDB . analysis) (_parents ledC <>)
                           . (if bestChanged && isJust (_fitness (_info ledC)) then over (eDB . refits) (IntSet.insert led) else id)
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

    updateDBs :: (Monad m, HasCallStack) => EClass -> EClassId -> EClass -> EClassId -> EClassId -> EClass -> EClassId -> EGraphST m ()
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
modifyEClass :: (Monad m, HasCallStack) => CostFun -> EClassId -> EGraphST m EClassId
modifyEClass costFun ecId =
  do ec <- getEClass ecId
     case (_consts . _info) ec of
       ConstVal x ->
         do let en = EConst x
            c <- calculateCost costFun en
            let infoEc = (_info ec){ _cost = c, _best = en, _consts = toConst en }
            maybeEid <- gets (HashMap.lookup en . _eNodeToEClass)
            modify' $ over eClass (IntMap.insert ecId ec{_eNodes = Set.singleton en , _info = infoEc})
            when (isJust $ _fitness $ _info ec) $ modify' $ over (eDB . refits) (IntSet.insert ecId)
            case maybeEid of
              Nothing   -> pure ecId
              Just eid' -> merge costFun eid' ecId

       ParamIx x ->
         do let en = EParam x
            c <- calculateCost costFun en
            let infoEc = (_info ec){ _cost = c, _best = en, _consts = toConst en }
            maybeEid <- gets (HashMap.lookup en . _eNodeToEClass)
            modify' $ over eClass (IntMap.insert ecId ec{_eNodes = Set.insert en (_eNodes ec), _info = infoEc})
            when (isJust $ _fitness $ _info ec) $ modify' $ over (eDB . refits) (IntSet.insert ecId)
            case maybeEid of
              Nothing   -> pure ecId
              Just eid' -> merge costFun eid' ecId

       _ -> pure ecId

  where
    isTerm (EVar _)   = True
    isTerm (EConst _) = True
    isTerm (EParam _) = True
    isTerm _          = False

    toConst (EParam ix) = ParamIx ix
    toConst (EConst x)  = ConstVal x
    toConst _           = NotConst

-- * DB

-- | `addToDB` adds an e-node and e-class id to the database
addToDB :: (Monad m, HasCallStack) => ENode -> EClassId -> EGraphST m () -- State DB ()
addToDB enode' eid = do
  eid' <- canonical eid
  ec <- gets ((IntMap.! eid') . _eClass)
  let isConst = _consts . _info $ ec
  let enode = case isConst of
                ConstVal x -> EConst x
                ParamIx  x -> EParam x
                _          -> enode'
  let ids = eid : eChildren enode -- we will add the e-class id and the children ids
      op  = eOpKey enode    -- changes Bin op l r to Bin op () () so `op` as a single entry in the DB
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

canonizeMap :: (Monad m, HasCallStack) => (Subst, ClassOrVar) -> EGraphST m (Subst, ClassOrVar)
canonizeMap (subst, cv) = (,cv) <$> traverse g subst
  where
    g :: Monad m => SubVal -> EGraphST m SubVal
    g (SVOne e2)  = SVOne <$> canonOne e2
    g (SVList es) = SVList <$> mapM canonOne es
    canonOne :: Monad m => ClassOrVar -> EGraphST m ClassOrVar
    canonOne (Left e2) = Left <$> canonical e2
    canonOne e2        = pure e2
{-# INLINE canonizeMap #-}

applyMatch :: (Monad m, HasCallStack) => CostFun -> Rule -> (Subst, ClassOrVar) -> EGraphST m ()
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

-- | gets the e-node of the target of the rule
-- TODO: add consts and modify
classOfENode :: (Monad m, HasCallStack) => CostFun -> Subst -> Pattern -> EGraphST m (Maybe EClassId)
classOfENode costFun subst (VarPat c)     = do let maybeEid = case Map.lookup (Right (fromEnum c)) subst of
                                                                  Just (SVOne v) -> Just v
                                                                  _              -> Nothing
                                               case maybeEid of
                                                 Nothing  -> pure Nothing
                                                 Just eid -> Just <$> canonical (getInt eid)
classOfENode costFun subst (Fixed (Const x)) = Just <$> add costFun (EConst x)
classOfENode costFun subst (Fixed target) = do newChildren <- mapM (classOfENode costFun subst) (getElems target)
                                               case sequence newChildren of
                                                 Nothing -> pure Nothing
                                                 Just cs -> do let new_enode = replaceChildren cs target
                                                               cs' <- mapM canonical cs
                                                               areConsts <- mapM isConst cs'
                                                               if and areConsts
                                                                 then do eid <- addTree costFun new_enode
                                                                         rebuild costFun -- eid new_enode
                                                                         pure (Just eid)
                                                                 else do en <- toENode new_enode
                                                                         en' <- canonize en
                                                                         gets (HashMap.lookup en' . _eNodeToEClass)
classOfENode _ _ (NAry _ _) = error "classOfENode: n-ary pattern unsupported"
classOfENode _ _ Hole       = error "classOfENode: Hole is only valid in MapP targets"
{-# INLINE classOfENode #-}

-- | adds the target of the rule into the e-graph
reprPrat :: (Monad m, HasCallStack) => CostFun -> Subst -> Pattern -> EGraphST m EClassId
reprPrat costFun subst (VarPat c)     = do
    let k = Right (fromEnum c)
    v <- case Map.lookup k subst of
           Nothing -> error $ "REPRPRAT_MISSING var=" <> show (fromEnum c) <> " substSize=" <> show (Map.size subst)
           Just (SVOne x) -> pure x
           Just (SVList _) -> error $ "REPRPRAT_REST_AS_SINGLE var=" <> show (fromEnum c)
    canonical $ getInt v
reprPrat costFun subst (Fixed target) = do newChildren <- mapM (reprPrat costFun subst) (getElems target)
                                           addTree costFun (replaceChildren newChildren target)
reprPrat costFun subst Hole = error "REPRPRAT_HOLE: Hole must be filled by MapP"
reprPrat costFun subst (NAry op ncs) = do
    cs <- concat <$> mapM (childEid costFun subst) ncs
    case cs of
      []     -> reprPrat costFun subst (Fixed (Const (if op == EAdd then 0 else 1)))
      [c]    -> canonical c
      _      -> do en <- mkENary op cs
                   add costFun en
{-# INLINE reprPrat #-}

-- | Adds a single child of an n-ary target pattern to the e-graph.
childEid :: (Monad m, HasCallStack) => CostFun -> Subst -> NChild -> EGraphST m [EClassId]
childEid costFun subst (Ch p)     = (:[]) <$> reprPrat costFun subst p
childEid costFun subst (Rest c)   = restEids costFun subst c
childEid costFun subst (MapP p c) = do
  es <- restEids costFun subst c
  forM es $ \e -> reprMapP costFun subst e p
{-# INLINE childEid #-}

-- | The e-class ids bound to a rest variable.
restEids :: (Monad m, HasCallStack) => CostFun -> Subst -> Char -> EGraphST m [EClassId]
restEids _ subst c = do
  let k = Right (fromEnum c)
  case Map.lookup k subst of
    Just (SVList es) -> pure (map getInt es)
    Just (SVOne _)   -> error $ "REPRPRAT_SINGLE_AS_REST var=" <> show (fromEnum c)
    Nothing          -> error $ "REPRPRAT_MISSING_REST var=" <> show (fromEnum c)
{-# INLINE restEids #-}

-- | Build the target of a pattern where every `Hole` is filled with the
-- e-class `e` (used by 'MapP').
reprMapP :: (Monad m, HasCallStack) => CostFun -> Subst -> EClassId -> Pattern -> EGraphST m EClassId
reprMapP costFun subst e Hole = canonical e
reprMapP costFun subst e (VarPat c) = reprPrat costFun subst (VarPat c)
reprMapP costFun subst e (Fixed target) = do
  newChildren <- mapM (reprMapP costFun subst e) (getElems target)
  addTree costFun (replaceChildren newChildren target)
reprMapP costFun subst e (NAry op ncs) = do
  cs <- concat <$> mapM (childMapP costFun subst e) ncs
  case cs of
    []   -> reprPrat costFun subst (Fixed (Const (if op == EAdd then 0 else 1)))
    [c]  -> canonical c
    _    -> do en <- mkENary op cs
               add costFun en
{-# INLINE reprMapP #-}

-- | A single child of an n-ary pattern inside a 'MapP' function.
childMapP :: (Monad m, HasCallStack) => CostFun -> Subst -> EClassId -> NChild -> EGraphST m [EClassId]
childMapP costFun subst e (Ch p)     = (:[]) <$> reprMapP costFun subst e p
childMapP costFun subst e (Rest c)   = restEids costFun subst c
childMapP costFun subst e (MapP _ _) = error "nested MapP unsupported"
{-# INLINE childMapP #-}

isValidHeight :: (Monad m, HasCallStack) => (Subst, ClassOrVar) -> EGraphST m Bool
isValidHeight match = do
      h <- case snd match of
             Left ec -> _height <$> getEClass ec
             Right _ -> pure 0
      pure $ h < 15
{-# INLINE isValidHeight #-}

-- | returns `True` if the condition of a rule is valid for that match
isValidConditions :: Monad m => Condition -> (Subst, ClassOrVar) -> EGraphST m Bool
isValidConditions cond match = gets $ cond (fst match)
{-# INLINE isValidConditions #-}

-- * Tree to e-graph conversion and utility functions

-- | Creates an e-graph from an expression tree
fromTree :: (Monad m, HasCallStack) => CostFun -> Fix SRTree -> EGraphST m EClassId
fromTree costFun = cataM sequence (addTree costFun)
{-# INLINE fromTree #-}

-- | Builds an e-graph from multiple independent trees
fromTrees :: Monad m => CostFun -> [Fix SRTree] -> EGraphST m [EClassId]
fromTrees costFun = foldM (\rs t -> do eid <- fromTree costFun t; pure (eid:rs)) []
{-# INLINE fromTrees #-}

countParamsEg :: EGraph -> EClassId -> Int
countParamsEg eg rt = countParams . runIdentity $ getBestExpr rt `evalStateT` eg
countParamsUniqEg :: EGraph -> EClassId -> Int
countParamsUniqEg eg rt = countParamsUniq . runIdentity $ getBestExpr rt `evalStateT` eg


getBestENode eid = (_best . _info) <$> getEClass eid
{-# INLINE getBestENode #-}

-- | returns one expression rooted at e-class `eId`
-- TODO: avoid loopings
getExpressionFrom :: Monad m => EClassId -> EGraphST m (Fix SRTree)
getExpressionFrom eId' = do
    nodes <- _eNodes <$> getEClass eId'
    case Set.toList nodes of
      (n:_) -> case n of
        EVar ix     -> pure $ Fix $ Var ix
        EParam ix   -> pure $ Fix $ Param ix
        EConst x    -> pure $ Fix $ Const x
        EUni f t    -> Fix . Uni f <$> getExpressionFrom t
        EBin op l r -> Fix <$> (Bin op <$> getExpressionFrom l <*> getExpressionFrom r)
        ENAry op xs -> naryTree op <$> mapM getExpressionFrom xs
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
        t <- case n of
                EVar ix     -> pure [Fix $ Var ix]
                EParam ix   -> pure [Fix $ Param ix]
                EConst x    -> pure [Fix $ Const x]
                EUni f t    -> Prelude.map (Fix . Uni f) <$> getAllExpressionsFrom t
                EBin op l r -> do l' <- getAllExpressionsFrom l
                                  r' <- getAllExpressionsFrom r
                                  pure $ [Fix $ Bin op li ri | li <- l', ri <- r']
                ENAry op xs -> do ts <- mapM getAllExpressionsFrom xs
                                  pure [ naryTree op comb | comb <- sequence ts ]
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
    isTerm (EVar _) = True
    isTerm (EConst _) = True
    isTerm (EParam _) = True
    isTerm _ = False
    toTree (EVar ix) = Fix $ Var ix
    toTree (EConst x) = Fix $ Const x
    toTree (EParam ix) = Fix $ Param ix
    toTree _ = undefined

    go n' _ []     = pure []
    go n' 0 ts     = pure []
    go n' d (node:ns) = do
        tt <- case node of
                EVar ix     -> pure [Fix $ Var ix]
                EParam ix   -> pure [Fix $ Param ix]
                EConst x    -> pure [Fix $ Const x]
                EUni f t    -> Prelude.map (Fix . Uni f) <$> getNExpressionsFrom' n' (d-1) t
                EBin op l r -> do l' <- getNExpressionsFrom' n' (d-1) l
                                  r' <- getNExpressionsFrom' n' (d-1) r
                                  pure $ Prelude.take n [Fix $ Bin op li ri | li <- l', ri <- r']
                ENAry op xs -> do ts <- mapM (getNExpressionsFrom' n' (d-1)) xs
                                  pure $ Prelude.take n [ naryTree op comb | comb <- sequence ts ]
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
                EBin op l r -> do l' <- getNEclassFrom' n' (d-1) l
                                  r' <- getNEclassFrom' n' (d-1) r
                                  pure $ Prelude.take n [li <> ri | li <- l', ri <- r']
                ENAry op xs -> do ts <- mapM (getNEclassFrom' n' (d-1)) xs
                                  pure $ Prelude.take n [ concat comb | comb <- sequence ts ]
                EUni f t    -> getNEclassFrom' n' (d-1) t -- [[eid2:eid1]]
                EVar ix     -> pure [[]]
                EConst x    -> pure [[]]
                EParam ix   -> pure [[]]
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
    hasNoTerminal = all (not . null . eChildren) 
    getNodes :: Monad m => EClassId -> EGraphST m [ENode]
    getNodes n = Set.toList . _eNodes <$> getEClass n

    go :: Monad m => [Int] -> IntSet.IntSet -> EGraphST m IntSet.IntSet
    go [] visited = pure visited
    go queue visited = do 
        nodes <- concatMap eChildren . concat . filter hasNoTerminal <$> mapM getNodes queue
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
  IntSet.toList <$> go IntSet.empty eId'
  where
    go :: Monad m => IntSet.IntSet -> EClassId -> EGraphST m IntSet.IntSet
    go acc n
      | IntSet.member n acc = pure acc
      | otherwise = do
          let acc' = IntSet.insert n acc
          node <- (_best . _info) <$> getEClass n
          eids <- mapM canonical $ eChildren node
          foldM go acc' eids

getAllChildBestEClassesRep :: Monad m => EClassId -> EGraphST m [EClassId]
getAllChildBestEClassesRep eId' = do
  go eId'
  where
    go :: Monad m => EClassId -> EGraphST m [EClassId]
    go n = do node <- (_best . _info) <$> getEClass n
              let hasTerminal = (null . eChildren) node
              eids <- mapM canonical $ eChildren node
              if hasTerminal
                then pure [n]
                else do eids' <- mapM go eids
                        pure (n : concat eids')

-- | returns a random expression rooted at e-class `eId`
getRndExpressionFrom :: EClassId -> EGraphST (State StdGen) (Fix SRTree)
getRndExpressionFrom eId' = do
    nodes <- Set.toList . _eNodes <$> getEClass eId'
    n <- lift $ randomFrom nodes
    case n of
      EUni f t    -> Fix . Uni f <$> getRndExpressionFrom t
      EBin op l r -> Fix <$> (Bin op <$> getRndExpressionFrom l <*> getRndExpressionFrom r)
      ENAry op xs -> naryTree op <$> mapM getRndExpressionFrom xs
      EVar ix     -> pure $ Fix $ Var ix
      EConst x    -> pure $ Fix $ Const x
      EParam ix   -> pure $ Fix $ Param ix
  where
    randomRange rng = state (randomR rng)
    randomFrom xs   = do n <- randomRange (0, length xs - 1)
                         pure $ xs !! n
{-# INLINE getRndExpressionFrom #-}

cleanMaps :: Monad m => EGraphST m ()
cleanMaps = do
  enode2eclass <- gets _eNodeToEClass
  entries <- forM (HashMap.toList enode2eclass) $ \(k,v) -> do
    k' <- canonize k
    v' <- canonical v
    pure (k',v')
  let enode2eclass' = HashMap.fromList entries
  eclassMap <- gets _eClass
  entries' <- forM (IntMap.toList eclassMap) $ \(k,v) -> do
    k' <- canonical k
    pure $ if k==k' then (Just (k,v)) else Nothing
  let eclassMap' = IntMap.fromList (catMaybes entries')
  -- keep the canonical map COMPLETE (not just identity entries): _nextId keeps
  -- counting and stale ids can still be referenced (patDB trie, worklist,
  -- analysis, _unevaluated/_refits), so `canonical` must resolve them to a live
  -- representative that remains in the pruned _eClass.
  canon' <- gets _canonicalMap
  eDB' <- gets _eDB
  put $ EGraph canon' enode2eclass' eclassMap' eDB'
{-# INLINE cleanMaps #-}
