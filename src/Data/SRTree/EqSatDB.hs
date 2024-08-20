module Data.SRTree.EqSatDB where 

import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Recursion ( cataM )
import Control.Monad
import Control.Monad.State
import Control.Lens ( (+~), (-~), makeLenses, (^.), (.~), (&), element, over )
import Data.Set ( Set )
import Data.Map ( Map )
import Data.IntMap ( IntMap )
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import System.Random
import Debug.Trace
import Data.SRTree.Egraph
import Data.Maybe ( fromMaybe, isNothing, mapMaybe )
import Data.List ( nub, sortBy, intercalate )
import Data.Ord ( comparing )
import Data.String ( IsString(..) )

-- The database maps a symbol to an IntTrie
-- The IntTrie stores the possible paths from a certain e-class 
-- that matches a pattern 
type DB = Map (SRTree ()) IntTrie
-- The IntTrie is composed of the set of available keys (for convenience)
-- and an IntMap that maps one e-class id to the first child IntTrie,
-- the first child IntTrie will point to the next child and so on
data IntTrie = IntTrie { _keys :: Set EClassId, _trie :: IntMap IntTrie } -- deriving Show

-- A Pattern is either a fixed-point of a tree or an
-- index to a pattern variable. The pattern variable matches anything. 
-- TODO: instance of Num, Floating, etc. May need to change var to string.
data Pattern = Fixed (SRTree Pattern) | VarPat Char deriving Show -- Fixed structure of a pattern or a variable that matches anything

instance IsString Pattern where
  fromString []     = error "empty string in VarPat"
  fromString [c] | n >= 65 && n <= 122 = VarPat c where n = fromEnum c
  fromString s      = error $ "invalid string in VarPat: " <> s
-- A rule is either a directional rule where pat1 can be replaced by pat2, a bidirectional rule 
-- where pat1 can be replaced or replace pat2, or a pattern with a conditional function 
-- describing when to apply the rule 
data Rule = Pattern :=> Pattern | Pattern :==: Pattern | Rule :| Condition

infix 3 :=>
infix 3 :==:
infix 2 :|

-- A Query is a list of Atoms 
type Query = [Atom] 

type Condition = Map ClassOrVar ClassOrVar -> EGraph -> Bool

-- An Atom is composed of either an e-class id or pattern variable id
-- and the tree that generated that pattern 
type ClassOrVar = Either EClassId Int
data Atom = Atom ClassOrVar (SRTree ClassOrVar) deriving Show

unFixPat :: Pattern -> SRTree Pattern
unFixPat (Fixed p) = p 

-- Shows the IntTrie as {keys} -> {show IntTries}
instance Show IntTrie where
  show (IntTrie k t) = let keys  = intercalate "," (map show $ Set.toList k)
                           tries = intercalate "," (map (\(k,v) -> show k <> " -> " <> show v) $ IntMap.toList t)
                       in "{" <> keys <> "} - {" <> tries <> "}"


instance Num Pattern where
  l + r = Fixed $ Bin Add l r
  {-# INLINE (+) #-}
  l - r = Fixed $ Bin Sub l r
  {-# INLINE (-) #-}
  l * r = Fixed $ Bin Mul l r
  {-# INLINE (*) #-}

  abs = Fixed . Uni Abs
  {-# INLINE abs #-}

  negate t = Fixed (Const (-1)) * t
  {-# INLINE negate #-}

  signum t = case t of
               Fixed (Const x) -> Fixed . Const $ signum x
               _               -> Fixed (Const 0)
  fromInteger x = Fixed $ Const (fromInteger x)
  {-# INLINE fromInteger #-}

instance Fractional Pattern where
  l / r = Fixed $ Bin Div l r
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

-- | `createDB` creates a database of patterns from an e-graph
-- it simply calls addToDB for every pair (e-node, e-class id) from 
-- the e-graph. 
createDB :: EGraph -> DB
createDB eg = execState dbst Map.empty
    where dbst = mapM_ (uncurry addToDB) 
               $ Map.toList 
               $ _eNodeToEClass eg

-- | `addToDB` adds an e-node and e-class id to the database
addToDB :: ENode -> EClassId -> State DB ()
addToDB enode eid = do let ids = eid : children enode -- we will add the e-class id and the children ids 
                           op  = getOperator enode    -- changes Bin op l r to Bin op () () so `op` as a single entry in the DB
                       trie <- gets (Map.!? op)       -- gets the entry for op, if it exists 
                       case populate trie ids of      -- populates the trie 
                         Nothing -> pure ()
                         Just t  -> modify' (Map.insert op t) -- if something was created, insert back into the DB 

-- | Creates a singleton trie from an e-class id 
trie :: EClassId -> IntMap IntTrie -> IntTrie 
trie eid = IntTrie (Set.singleton eid)

-- | Populates an IntTrie with a sequence of e-class ids
populate :: Maybe IntTrie -> [EClassId] -> Maybe IntTrie
populate _ []         = Nothing
-- if it is a new entry, simply add the ids sequentially
populate Nothing eids = foldr f Nothing eids
  where
    f :: EClassId -> Maybe IntTrie -> Maybe IntTrie
    f eid (Just t) = Just $ trie eid (IntMap.singleton eid t)
    f eid Nothing  = Just $ trie eid IntMap.empty
-- if the entry already exists, insert the new key
-- and populate the next child entry recursivelly 
populate (Just tId) (eid:eids) = let keys = Set.insert eid (_keys tId)
                                     nextTrie = _trie tId IntMap.!? eid 
                                     val = fromMaybe (trie eid IntMap.empty) $ populate nextTrie eids
                                  in Just $ IntTrie keys (IntMap.insert eid val (_trie tId))
                                      
applyMatch :: CostFun -> Rule -> (Map ClassOrVar ClassOrVar, ClassOrVar) -> EGraphST ()
applyMatch costFun rule match =
  do eg <- get
     let conds = getConditions rule
     when (all (\c -> isValidConditions c match eg) conds) $
       do new_eclass <- reprPrat costFun (fst match) (target rule)
          _ <- merge costFun (getInt (snd match)) new_eclass
          pure ()

target :: Rule -> Pattern
target (r :| _)   = target r
target (_ :=> t)  = t
target (_ :==: t) = t

source :: Rule -> Pattern
source (r :| _) = source r
source (s :=> _)  = s
source (s :==: _) = s

getConditions :: Rule -> [Condition]
getConditions (r :| c) = c : getConditions r
getConditions _ = []

reprPrat :: CostFun -> Map ClassOrVar ClassOrVar -> Pattern -> EGraphST EClassId
reprPrat costFun subst (VarPat c)     = pure $ getInt $ subst Map.! (Right $ fromEnum c)
reprPrat costFun subst (Fixed target) = do newChildren <- mapM (reprPrat costFun subst) (getElems target)
                                           add costFun (replaceChildren newChildren target)

-- | returns `True` if the condition of a rule is valid for that match
isValidConditions :: Condition -> (Map ClassOrVar ClassOrVar, ClassOrVar) -> EGraph -> Bool
isValidConditions cond match eg = cond (fst match) eg

-- | Returns the substitution rules
-- for every match of the pattern `source` inside the e-graph.
match :: DB -> Pattern -> [(Map ClassOrVar ClassOrVar, ClassOrVar)]
match db source = [(s, s Map.! root) | s <- substs, Map.size s > 0]
  where 
    (q, root) = compileToQuery source  -- compile the source of the pattern into a query
    substs    = genericJoin db q       -- find the substituion rules for this pattern

-- | Returns a Query (list of atoms) of a pattern
compileToQuery :: Pattern -> (Query, ClassOrVar)
compileToQuery pat = evalState (processPat pat) 256 -- returns (atoms, root)
  where
      -- creates the atoms of a pattern
      processPat :: Pattern -> State Int (Query, ClassOrVar)
      processPat (VarPat x)  = pure ([], Right $ fromEnum x)
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

-- get the value from the Either Int Int
getInt :: ClassOrVar -> Int
getInt (Left a)  = a
getInt (Right a) = a

-- | returns the list of the children values
getElems :: SRTree a -> [a]
getElems (Bin _ l r) = [l,r]
getElems (Uni _ t)   = [t]
getElems _           = []

-- | Creates the substituion map for
-- the pattern variables for each one of the
-- matched subgraph
genericJoin :: DB -> Query -> [Map ClassOrVar ClassOrVar]
genericJoin db atoms = let vars = orderedVars atoms -- order the vars, starting with the most frequently occuring
                       in go atoms vars -- TODO: investigate why we need nub
  where
    -- for each variable
    --   for each possible e-class id for that variable
    --      replace the var id with this e-class id, and
    --      recurse to find the possible matches for the next atom
    go atoms [] = [Map.empty] -- | _ <- atoms]
    go atoms (x:vars) = [Map.insert x classId y | classId <- domainX db x atoms
                                                , y <- go (updateVar x classId atoms) vars]
                                                {-
    go atoms (x:vars) = do classId <- domainX db x atoms
                           let newAtoms = updateVar x classId atoms
                           y <- traceShow ("<<<<", go newAtoms vars) $ go newAtoms vars
                           traceShow (x, classId, y) $ pure $ Map.insert x classId y
                           -}

-- | returns the e-class id for a certain variable that
-- matches the pattern described by the atoms
domainX :: DB -> ClassOrVar -> Query -> [ClassOrVar]
domainX db var atoms = let ss = (map Left
                                  $ intersectAtoms var db          -- find the intersection of possible keys by each atom
                                  $ filter (elemOfAtom var) atoms) :: [ClassOrVar]  -- look only in the atoms with this var
                       in ss

-- | returns all e-class id that can matches this sequence of atoms
intersectAtoms :: ClassOrVar -> DB -> Query -> [EClassId]
intersectAtoms _ _ [] = []
intersectAtoms var db (a:atoms) = Set.toList $ foldr (\atom acc -> Set.intersection acc $ go atom) (go a) atoms
  where 
      go (Atom r t) = let op = getOperator t
                       in if op `Map.member` db -- if the e-graph contains the operator
                             -- try to find an intersection of the tries that matches each atom of the pattern
                             then fromMaybe Set.empty $ intersectTries var Map.empty (db Map.! op) (r:getElems t)
                             else Set.empty 

-- | searches for the intersection of e-class ids that
-- matches each part of the query.
-- Returns Nothing if the intersection is empty.
--
-- var is the current variable being investigated
-- xs is the map of ids being investigated and their corresponding e-class id
-- trie is the current trie of the pattern
-- (i:ids) sequence of root : children of the atom to investigate
intersectTries :: ClassOrVar -> Map ClassOrVar EClassId -> IntTrie -> [ClassOrVar] -> Maybe (Set EClassId)
intersectTries var xs trie [] = Just Set.empty 
intersectTries var xs trie (i:ids) = 
    case i of
      Left x  -> if x `Set.member` _keys trie 
                    -- if the current investigated id is an e-class id and
                    -- it is one of the keys of the trie...
                    -- ..try to match the next id with the next trie
                    then intersectTries var xs (_trie trie IntMap.! x) ids
                    else Nothing
      Right x -> if i `Map.member` xs
                    -- if it is a pattern variable under investigation
                    -- and the e-class id is part of the trie
                    then if xs Map.! i `Set.member` _keys trie
                            -- match the next id with the next trie
                            then intersectTries var xs (_trie trie IntMap.! (xs Map.! i)) ids 
                            else Nothing
                    else if Right x == var
                            -- not under investigation and is the var of interest
                            then if all (isDiffFrom x) ids 
                                    -- if there are no other occurrence of x in the next vars,
                                    -- the keys of the trie are all possible candidates
                                    then Just $ _keys trie
                                    -- oterwise, put i under investigation and check the next occurrences
                                    -- returning the intersection
                                    else Just $ IntMap.foldrWithKey (\k v acc ->
                                                    case intersectTries var (Map.insert i k xs) v ids of
                                                      Nothing -> acc
                                                      _       -> Set.insert k acc) Set.empty (_trie trie)
                            -- if it is not the var of interest
                            -- assign and test all possible e-class ids to it
                            -- and move forward
                            else Just $ IntMap.foldrWithKey (\k v acc ->
                                                case intersectTries var (Map.insert i k xs) v ids of
                                                  Nothing -> acc
                                                  Just s  -> Set.union acc s
                                                     ) Set.empty (_trie trie)



-- | updates all occurrence of var with the new id x
updateVar :: ClassOrVar -> ClassOrVar -> Query -> Query
updateVar var x = map replace
  where
      replace (Atom r t) = let children = [if c == var then x else c | c <- getElems t]
                               t'       =  replaceChildren children t 
                            in Atom (if r == var then x else r) t'

-- | checks whether two ClassOrVar are different
-- only check if it is a pattern variable, else returns true
isDiffFrom :: Int -> ClassOrVar -> Bool
isDiffFrom x y = case y of 
                   Left _ -> False
                   Right z -> x /= z 

-- | checks if v is an element of an atom
elemOfAtom :: ClassOrVar -> Atom -> Bool
elemOfAtom v (Atom root tree) =
    case root of 
      Left _  -> v `elem` getElems tree
      Right x -> Right x == v || v `elem` getElems tree

-- | sorts the variables in a query by the most frequently occurring
orderedVars :: Query -> [ClassOrVar]
orderedVars atoms = sortBy (comparing varCost) $ nub [a | atom <- atoms, a <- getIdsFrom atom, isRight a]
  where
    getIdsFrom (Atom r t) = r : getElems t
    isRight (Right _) = True 
    isRight _ = False


    varCost :: ClassOrVar -> Int 
    varCost var = foldr (\a acc -> if elemOfAtom var a then acc - 100 + atomLen a else acc) 0 atoms

    atomLen (Atom _ t) = 1 + length (getElems t)
