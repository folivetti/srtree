{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.EqSat.EqSatDB
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Pattern matching and rule application functions
-- Heavily based on hegg (https://github.com/alt-romes/hegg by alt-romes)
--
-----------------------------------------------------------------------------
module Algorithm.EqSat.DB where

import Algorithm.EqSat.Egraph
import Control.Lens ( over )
import Control.Monad (when, foldM, forM)
import Control.Monad.State
import GHC.Stack (HasCallStack)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List (delete, intercalate, sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.SRTree
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.Set as RangeSet
import Data.String (IsString (..))
import Data.SRTree.Recursion (cata)


-- A Pattern is either a fixed-point of a tree, an index to a pattern variable
-- (which matches anything), a hole (only used inside a 'MapP' target function),
-- or an n-ary Add/Mul pattern whose children are matched as a multiset.
data Pattern = Fixed (SRTree Pattern) | VarPat Char | Hole | NAry NOp [NChild]
  deriving (Show, Eq, Ord)

-- | A child of an n-ary pattern: a single child pattern ('Ch'), a rest
-- variable binding every remaining child of the node ('Rest'), or a
-- target-side map that splices one instantiation of a pattern (with its 'Hole'
-- filled) per child bound to a rest variable ('MapP').
data NChild = Ch Pattern | Rest Char | MapP Pattern Char
  deriving (Show, Eq, Ord)

-- The instance for `IsString` for a `Pattern` is 
-- valid only for a single letter char from a-zA-Z. 
-- The patterns can be written as "x" + "y", for example,
-- and it will translate to `Fixed (Bin Add (VarPat 120) (VarPat 121)`.
instance IsString Pattern where
  fromString []     = error "empty string in VarPat"
  fromString [c] | n >= 65 && n <= 122 = VarPat c where n = fromEnum c
  fromString s      = error $ "invalid string in VarPat: " <> s

tree2pat :: Fix SRTree -> Pattern
tree2pat = cata alg
  where
    alg (Param ix) = if ix >= 100 then VarPat (toEnum $ ix - 100 + 65) else Fixed $ Param ix
    alg (Var ix) = Fixed $ Var ix
    alg (Const x) = Fixed $ Const x
    alg (Bin Add l r) = NAry EAdd [Ch l, Ch r]
    alg (Bin Mul l r) = NAry EMul [Ch l, Ch r]
    alg (Bin op l r) = Fixed $ Bin op l r
    alg (Uni f t) = Fixed $ Uni f t
-- A rule is either a directional rule where pat1 can be replaced by pat2, a bidirectional rule 
-- where pat1 can be replaced or replace pat2, or a pattern with a conditional function 
-- describing when to apply the rule 
data Rule = Pattern :=> Pattern | Pattern :==: Pattern | Rule :| Condition

infix  3 :=>
infix  3 :==:
infixl 2 :|

instance Show Rule where
  show (a :=> b) = show a <> " => " <> show b
  show (a :==: b) = show a <> " == " <> show b
  show (a :| b) = show a <> " | <cond>"

-- A Query is a list of Atoms 
type Query = [Atom]

-- | A `Condition` is a predicate over a match's substitution that runs inside
-- the e-graph monad so it can fetch e-class data through 'ClassStore' (which
-- streams from a paged store when the graph is out-of-core). The quantification
-- over the monad is intentional: the same condition works for any 'ClassStore'
-- instance, including the IO-backed paged store.
newtype Condition = Condition (forall m. ClassStore m => Subst -> EGraphST m Bool)

-- An Atom is composed of either an e-class id or pattern variable id
-- and the tree that generated that pattern. Left is e-class id and Right is a VarPat.
type ClassOrVar = Either EClassId Int
data Atom = Atom ClassOrVar (SRTree ClassOrVar) deriving Show

-- | A substitution value: a single e-class (a matched pattern variable) or the
-- canonical multiset of e-class ids (a matched rest variable).
data SubVal = SVOne ClassOrVar | SVMap (IntMap Int) deriving Show

-- | Substitution map produced by matching a pattern.
type Subst = Map ClassOrVar SubVal

unFixPat :: Pattern -> SRTree Pattern
unFixPat (Fixed p) = p
unFixPat (VarPat _) = error "unFixPat: VarPat is not a fixed pattern"
unFixPat Hole       = error "unFixPat: Hole is not a fixed pattern"
unFixPat (NAry _ _) = error "unFixPat: NAry is not a fixed pattern"
{-# INLINE unFixPat #-}


instance Num Pattern where
  l + r = NAry EAdd [Ch l, Ch r]
  {-# INLINE (+) #-}
  l - r = NAry EAdd [Ch l, Ch (negate r)]
  {-# INLINE (-) #-}
  l * r = NAry EMul [Ch l, Ch r]
  {-# INLINE (*) #-}

  abs = Fixed . Uni Abs
  {-# INLINE abs #-}

  negate t = NAry EMul [Ch (Fixed (Const (-1))), Ch t]
  {-# INLINE negate #-}

  signum t = case t of
               Fixed (Const x) -> Fixed . Const $ signum x
               _               -> Fixed (Const 0)
  fromInteger x = Fixed $ Const (fromInteger x)
  {-# INLINE fromInteger #-}

instance Fractional Pattern where
  l / r = NAry EMul [Ch l, Ch (Fixed (Uni Recip r))]
  {-# INLINE (/) #-}

  fromRational = Fixed . Const . fromRational
  {-# INLINE fromRational #-}

instance Floating Pattern where
  pi      = Fixed $ Const  pi
  {-# INLINE pi #-}
  exp     = Fixed . Uni Exp
  {-# INLINE exp #-}
  log     = Fixed . Uni Log
  {-# INLINE log #-}
  sqrt    = Fixed . Uni Sqrt
  {-# INLINE sqrt #-}
  sin     = Fixed . Uni Sin
  {-# INLINE sin #-}
  cos     = Fixed . Uni Cos
  {-# INLINE cos #-}
  tan     = Fixed . Uni Tan
  {-# INLINE tan #-}
  asin    = Fixed . Uni ASin
  {-# INLINE asin #-}
  acos    = Fixed . Uni ACos
  {-# INLINE acos #-}
  atan    = Fixed . Uni ATan
  {-# INLINE atan #-}
  sinh    = Fixed . Uni Sinh
  {-# INLINE sinh #-}
  cosh    = Fixed . Uni Cosh
  {-# INLINE cosh #-}
  tanh    = Fixed . Uni Tanh
  {-# INLINE tanh #-}
  asinh   = Fixed . Uni ASinh
  {-# INLINE asinh #-}
  acosh   = Fixed . Uni ACosh
  {-# INLINE acosh #-}
  atanh   = Fixed . Uni ATanh
  {-# INLINE atanh #-}

  l ** r  = Fixed $ Bin Power l r
  {-# INLINE (**) #-}

  logBase l r = log l / log r
  {-# INLINE logBase #-}

target :: Rule -> Pattern
target (r :| _)   = target r
target (_ :=> t)  = t
target (_ :==: t) = t
{-# INLINE target #-}

source :: Rule -> Pattern
source (r :| _) = source r
source (s :=> _)  = s
source (s :==: _) = s
{-# INLINE source #-}

getConditions :: Rule -> [Condition]
getConditions (r :| c) = c : getConditions r
getConditions _ = []
{-# INLINE getConditions #-}

cleanDB :: Monad m => EGraphST m ()
cleanDB = modify' $ over (eDB. patDB) (const Map.empty)
{-# INLINE cleanDB #-}

-- | Returns the substitution rules
-- for every match of the pattern `source` inside the e-graph.
match :: ClassStore m => Pattern -> EGraphST m [(Subst, ClassOrVar)]
match src = if hasNAry src
              then matchNAry src
              else matchCached (compileToQuery src)
{-# INLINE match #-}

matchCached :: Monad m => (Query, [ClassOrVar], ClassOrVar) -> EGraphST m [(Subst, ClassOrVar)]
matchCached (q, vars, root) = do
  substs <- genericJoin q vars root               -- find the substituion rules for this pattern
  pure [ (s, case Map.lookup root s of
               Nothing -> error $ "MATCHCACHED_MISSING root=" <> show (getInt root) <> " substSize=" <> show (Map.size s)
               Just v  -> fromSVOne v)
       | s <- substs, Map.size s > 0 ]
{-# INLINE matchCached #-}

-- | True if the pattern (or a nested child) is an n-ary Add/Mul pattern.
hasNAry :: Pattern -> Bool
hasNAry (NAry _ _) = True
hasNAry (Fixed t)  = any hasNAry (getElems t)
hasNAry _          = False
{-# INLINE hasNAry #-}

-- | The operator trie key of the top-level pattern.
opOf :: Pattern -> SRTree ()
opOf (NAry EAdd _) = Bin Add () ()
opOf (NAry EMul _) = Bin Mul () ()
opOf (Fixed t)     = getOperator t
opOf _             = error "opOf: pattern has no operator"
{-# INLINE opOf #-}

-- | Matches an n-ary pattern against every root e-node of the operator trie.
-- A per-rule result budget ('ruleBudget') bounds the total number of matches
-- returned for one rule against one individual's nodes, and only the first
-- match per root e-class is kept, taming the O(k^2*m^2) backtracking of
-- Rest/Ch rules (e.g. factoring a common term out of a sum of products).
-- Keeping one match per root is sound: every returned match is genuine, and
-- the egraph merges the equivalent rewrites that further matches would apply,
-- so the rest of the root's matches are redundant work.
ruleBudget :: Int
ruleBudget = 64

matchNAry :: ClassStore m => Pattern -> EGraphST m [(Subst, ClassOrVar)]
matchNAry src = do
  db <- gets (_patDB . _eDB)
  case Map.lookup (opOf src) db of
    Nothing -> pure []
    Just trie -> go (IntMap.keys (_trie trie)) 0 []
  where
    go :: ClassStore m => [EClassId] -> Int -> [(Subst, ClassOrVar)] -> EGraphST m [(Subst, ClassOrVar)]
    go [] _ acc = pure (reverse acc)
    go _ n acc | n >= ruleBudget = pure (reverse acc)
    go (eid : eids) n acc = do
      substs <- recursiveMatch src eid Map.empty
      let newMs = take 1 [ (s, Left eid) | s <- substs ]
      go eids (n + length newMs) (foldr (:) acc newMs)
{-# INLINE matchNAry #-}

-- | Recursively match a pattern against the e-class `eid`, threading a
-- substitution map, returning every substitution that completes the match.
recursiveMatch :: ClassStore m => Pattern -> EClassId -> Subst -> EGraphST m [Subst]
recursiveMatch (VarPat c) eid subst =
  pure (bindVar subst (Right (fromEnum c)) eid)
recursiveMatch Hole _ subst = pure [subst]
recursiveMatch (Fixed t) eid subst = matchFixed t eid subst
recursiveMatch (NAry op ncs) eid subst = matchNAryNode op ncs eid subst
{-# INLINE recursiveMatch #-}

-- | Bind `v` to the e-class `eid`, enforcing that re-occurrences of `v` are
-- consistent.
bindVar :: Subst -> ClassOrVar -> EClassId -> [Subst]
bindVar subst v eid =
  case Map.lookup v subst of
    Just (SVOne e) | e == Left eid -> [subst]
    Just _                         -> []
    Nothing                        -> [Map.insert v (SVOne (Left eid)) subst]
{-# INLINE bindVar #-}

-- | Match a fixed tree pattern against the e-nodes of the e-class `eid`,
-- returning every substitution that completes the match across all candidate
-- e-nodes.
matchFixed :: ClassStore m => SRTree Pattern -> EClassId -> Subst -> EGraphST m [Subst]
matchFixed t eid subst = do
  ec <- getEClass eid
  let cands = [n | n <- Set.toList (_eNodes ec), eOpKey n == getOperator t]
  fmap concat $ forM cands $ \n -> matchChildren t subst n
  where
    matchChildren t s n = go (zip (getElems t) (enodeChildren n)) [s]
    go [] ss = pure ss
    go ((p, c) : ps) ss = do
      ms <- concat <$> mapM (\s -> recursiveMatch p c s) ss
      go ps ms
{-# INLINE matchFixed #-}

-- | The child e-class ids of an e-node, in canonical (sorted for ENAry) order.
enodeChildren :: ENode -> [EClassId]
enodeChildren (EUni _ t)   = [t]
enodeChildren (EBin _ l r) = [l, r]
enodeChildren (ENAry _ m)  = expandedList m
enodeChildren _            = []
{-# INLINE enodeChildren #-}

-- | Match an n-ary pattern node against the e-class `eid`: it must contain an
-- ENAry node of the given op, whose children are matched as a multiset. Every
-- ENAry node in the class is tried.
matchNAryNode :: ClassStore m => NOp -> [NChild] -> EClassId -> Subst -> EGraphST m [Subst]
matchNAryNode op ncs eid subst = do
  ec <- getEClass eid
  let nodes = [m | ENAry op' m <- Set.toList (_eNodes ec), op' == op]
  fmap concat $ forM nodes $ \m ->
    matchNChildren ncs m subst
{-# INLINE matchNAryNode #-}

-- | Match a sequence of n-ary children against a multiset of e-class ids.
-- Each 'Ch' consumes one matched child; a 'Rest' child consumes all remaining
-- children. Every multiset assignment is returned. Iterating over the distinct
-- child ids (the multiset's keys) is sound (duplicate copies only differ by
-- position, which 'decChild' already resolves) and avoids duplicate result
-- sets.
--
-- A per-call result budget ('matchCap') caps the number of substitutions
-- returned, bounding the O(k^2*m^2) backtracking of Rest/Ch rules such as
-- factoring a common term out of a sum of products. Sound: each result is a
-- genuine match; we merely stop enumerating once the budget is exhausted.
matchCap :: Int
matchCap = 64

matchNChildren :: ClassStore m => [NChild] -> IntMap Int -> Subst -> EGraphST m [Subst]
matchNChildren ncs children subst = reverse <$> goB ncs children subst matchCap
  where
    goB :: ClassStore m => [NChild] -> IntMap Int -> Subst -> Int -> EGraphST m [Subst]
    goB [] m s _
      | IntMap.null m = pure [s]
      | otherwise     = pure []
    goB (Rest c : ps) m s b = do
      let v = Right (fromEnum c)
      case Map.lookup v s of
        Just _  -> pure []  -- rest variable already bound
        Nothing -> goB ps IntMap.empty (Map.insert v (SVMap m) s) b
    goB (Ch p : ps) m s b
      | multiplicity m <= nCh ps = pure []  -- not enough children left
      | otherwise = goC (IntMap.keys m) 0 []
      where
        goC :: ClassStore m => [EClassId] -> Int -> [Subst] -> EGraphST m [Subst]
        goC [] _ acc = pure acc
        goC _ n acc | n >= b    = pure acc
        goC (c : cs) n acc = do
          ms <- recursiveMatch p c s
          goMs c ms cs n acc
        goMs :: ClassStore m => EClassId -> [Subst] -> [EClassId] -> Int -> [Subst] -> EGraphST m [Subst]
        goMs c [] cs n acc = goC cs n acc
        goMs c (s' : ms) cs n acc
          | n >= b     = pure acc
          | otherwise = do
              r <- goB ps (decChild c m) s' (b - n)
              let r' = take (b - n) r
                  n' = n + length r'
              goMs c ms cs n' (foldr (:) acc r')
    goB (MapP _ _ : _) _ _ _ = error "matchNChildren: MapP is only valid in targets"
{-# INLINE matchNChildren #-}

-- | Total number of children (counting multiplicities) in a multiset.
multiplicity :: IntMap Int -> Int
multiplicity = IntMap.foldr' (+) 0
{-# INLINE multiplicity #-}

-- | Remove one occurrence of `c` from the multiset (decrementing its
-- multiplicity, or dropping the key entirely when it reaches zero).
decChild :: Int -> IntMap Int -> IntMap Int
decChild c = IntMap.update (\n -> if n > 1 then Just (n - 1) else Nothing) c
{-# INLINE decChild #-}

-- | Number of 'Ch' patterns in a child pattern sequence (each consumes one
-- child, so at least this many children must remain).
nCh :: [NChild] -> Int
nCh = length . filter isCh
  where
    isCh (Ch _)   = True
    isCh _        = False
{-# INLINE nCh #-}

-- | Unwrap a single-e-class substitution value.
fromSVOne :: SubVal -> ClassOrVar
fromSVOne (SVOne v)    = v
fromSVOne (SVMap _)    = error "fromSVOne: expected a single e-class"
{-# INLINE fromSVOne #-}

-- | Returns a Query (list of atoms) of a pattern with pre-computed ordered vars
compileToQuery :: Pattern -> (Query, [ClassOrVar], ClassOrVar)
compileToQuery pat = (atoms, orderedVars atoms, root)
  where (atoms, root) = evalState (processPat pat) 256
      -- creates the atoms of a pattern
        processPat :: Pattern -> State Int (Query, ClassOrVar)
        processPat (VarPat x)  = pure ([], Right $ fromEnum x)
        processPat (NAry _ _)  = error "compileToQuery: n-ary pattern (use matchNAry instead)"
        processPat Hole        = error "compileToQuery: Hole is only valid in MapP targets"
        processPat (Fixed pat) = do
            -- get the next available var id and add as root
            v <- get
            let root = Right v
            -- updates the next available id
            modify (+1)
            -- recursivelly process the children of the pattern
            patChilds <- mapM processPat (getElems pat)
            -- create an atom composed of the
            -- root and the tree with the children
            -- replaced by the childs roots
            -- add the child atoms to the list
            let atoms = concatMap fst patChilds
                roots = map snd patChilds
                atom  = Atom root (replaceChildren roots pat)
                atoms' = atom:atoms
            pure (atoms', root)
{-# INLINE compileToQuery #-}

-- get the value from the Either Int Int
getInt :: ClassOrVar -> Int
getInt (Left a)  = a
getInt (Right a) = a
{-# INLINE getInt #-}

-- | returns the list of the children values
getElems :: SRTree a -> [a]
getElems (Bin _ l r) = [l,r]
getElems (Uni _ t)   = [t]
getElems _           = []
{-# INLINE getElems #-}

-- | Creates the substituion map for
-- the pattern variables for each one of the
-- matched subgraph
genericJoin :: (Monad m, HasCallStack) => Query -> [ClassOrVar] -> ClassOrVar -> EGraphST m [Subst]
genericJoin atoms vars root = go atoms vars
  where
    -- for each variable
    --   for each possible e-class id for that variable
    --      replace the var id with this e-class id, and
    --      recurse to find the possible matches for the next atom
    go :: Monad m => Query -> [ClassOrVar] -> EGraphST m [Subst]
    go atoms [] = pure [Map.empty] -- | _ <- atoms]
    go atoms (x:vars) = do cIds1 <- domainX x atoms root
                           maps <- forM cIds1 $ \classId -> do
                             map (Map.insert x (SVOne classId)) <$> go (updateVar x classId atoms) vars
                           pure (concat maps)
{-# INLINE genericJoin #-}



-- | returns the e-class id for a certain variable that
-- matches the pattern described by the atoms
domainX :: (Monad m, HasCallStack) => ClassOrVar -> Query -> ClassOrVar -> EGraphST m [ClassOrVar]
domainX var atoms root = do
  let atoms' = filter (elemOfAtom var) atoms -- :: [ClassOrVar]  -- look only in the atoms with this var
  map Left <$> intersectAtoms var atoms' root -- find the intersection of possible keys by each atom
{-# INLINE domainX #-}

-- | returns all e-class id that can matches this sequence of atoms
intersectAtoms :: (Monad m, HasCallStack) => ClassOrVar -> Query -> ClassOrVar -> EGraphST m [EClassId]
intersectAtoms _ [] root = pure []
intersectAtoms var (a:atoms) root = do
  a0 <- toCanon =<< go a
  Set.toList <$> (foldM (\acc atom -> do
    res <- go atom
    Set.intersection acc <$> toCanon res) a0 atoms)
  where
      toCanon x = if var==root
                     then pure x
                     else Set.fromList <$> (mapM canonical $ Set.toList x)

      go (Atom r t) =
        do let op = getOperator t
           mTrie <- gets ((Map.!? op) . _patDB . _eDB)
           case mTrie of
             Just trie -> pure (fromMaybe Set.empty $ intersectTries var IntMap.empty trie (r:getElems t))
             Nothing   -> pure Set.empty

{-# INLINE intersectAtoms #-}

-- | searches for the intersection of e-class ids that
-- matches each part of the query.
-- Returns Nothing if the intersection is empty.
--
-- var is the current variable being investigated
-- xs is the map of ids being investigated and their corresponding e-class id
-- trie is the current trie of the pattern
-- (i:ids) sequence of root : children of the atom to investigate
-- NOTE: it must be Maybe Set to differentiate between empty set and no answer
intersectTries :: ClassOrVar -> IntMap EClassId -> IntTrie -> [ClassOrVar] -> Maybe (HashSet EClassId)
intersectTries var xs trie [] = Just Set.empty
intersectTries var xs trie (i:ids) =
    case i of
      Left x  -> case IntMap.lookup x (_trie trie) of
                   Just subtrie -> intersectTries var xs subtrie ids
                   Nothing -> Nothing
      Right x -> if IntMap.member x xs
                    then case IntMap.lookup (xs IntMap.! x) (_trie trie) of
                           Just subtrie -> intersectTries var xs subtrie ids
                           Nothing -> Nothing
                    else if Right x == var
                            then if all (isDiffFrom x) ids
                                    then Just $ Set.fromList (IntMap.keys (_trie trie))
                                    else Just $ IntMap.foldrWithKey (\k v acc ->
                                                    case intersectTries var (IntMap.insert x k xs) v ids of
                                                      Nothing -> acc
                                                      _       -> Set.insert k acc) Set.empty (_trie trie)
                            else Just $ IntMap.foldrWithKey (\k v acc ->
                                                case intersectTries var (IntMap.insert x k xs) v ids of
                                                  Nothing -> acc
                                                  Just s  -> Set.union acc s
                                                     ) Set.empty (_trie trie)
{-# INLINE intersectTries #-}

-- | updates all occurrence of var with the new id x
updateVar :: ClassOrVar -> ClassOrVar -> Query -> Query
updateVar var x = map replace
  where
      replace (Atom r t) = let children = [if c == var then x else c | c <- getElems t]
                               t'       =  replaceChildren children t
                            in Atom (if r == var then x else r) t'
{-# INLINE updateVar #-}

-- | checks whether two ClassOrVar are different
-- only check if it is a pattern variable, else returns true
isDiffFrom :: Int -> ClassOrVar -> Bool
isDiffFrom x y = case y of
                   Left _ -> False
                   Right z -> x /= z
{-# INLINE isDiffFrom #-}

-- | checks if v is an element of an atom
elemOfAtom :: ClassOrVar -> Atom -> Bool
elemOfAtom v (Atom root tree) =
    case root of
      Left _  -> v `elem` getElems tree
      Right x -> Right x == v || v `elem` getElems tree
{-# INLINE elemOfAtom #-}

-- | sorts the variables in a query by the most frequently occurring
-- Ties are broken by putting an atom ROOT first. The root indexes the
-- operator trie directly, so matching it first replaces repeated whole-trie
-- folds (O(candidates x nodes)) with direct per-node trie descents. The old
-- tie-break (by id) put low-id pattern leaves before the high-id fresh root,
-- which made the root's domain include every operator node regardless of the
-- already-bound children (over-enumeration and O(n^2) folds).
-- Measured on the user config: 33s -> 19s (MT -N8), best loss unchanged.
orderedVars :: Query -> [ClassOrVar]
orderedVars atoms = sortBy (comparing key) $ RangeSet.toList $ RangeSet.fromList [a | atom <- atoms, a <- getIdsFrom atom, isRight a]
  where
    getIdsFrom (Atom r t) = r : getElems t
    isRight (Right _) = True
    isRight _ = False

    -- is the variable the ROOT of some atom (an index into the operator trie)?
    isHeader v = any (\a -> case a of Atom r _ -> r == v) atoms

    varCost :: ClassOrVar -> Int
    varCost var = foldr (\a acc -> if elemOfAtom var a then acc - 100 + atomLen a else acc) 0 atoms

    key :: ClassOrVar -> (Int, Int)
    key v = (varCost v, if isHeader v then 0 else 1)

    atomLen (Atom _ t) = 1 + length (getElems t)
{-# INLINE orderedVars #-}
