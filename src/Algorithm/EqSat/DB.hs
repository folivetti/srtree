{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
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
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List (intercalate, nub, sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.SRTree
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString (..))

import Debug.Trace

-- A Pattern is either a fixed-point of a tree or an
-- index to a pattern variable. The pattern variable matches anything. 
data Pattern = Fixed (SRTree Pattern) | VarPat Char deriving Show -- Fixed structure of a pattern or a variable that matches anything

-- The instance for `IsString` for a `Pattern` is 
-- valid only for a single letter char from a-zA-Z. 
-- The patterns can be written as "x" + "y", for example,
-- and it will translate to `Fixed (Bin Add (VarPat 120) (VarPat 121)`.
instance IsString Pattern where
  fromString []     = error "empty string in VarPat"
  fromString [c] | n >= 65 && n <= 122 = VarPat c where n = fromEnum c
  fromString s      = error $ "invalid string in VarPat: " <> s

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

-- A `Condition` is a function that takes a substution map,
-- an e-graph and returns whether the pattern attends the condition.
type Condition = Map ClassOrVar ClassOrVar -> EGraph -> Bool

-- An Atom is composed of either an e-class id or pattern variable id
-- and the tree that generated that pattern. Left is e-class id and Right is a VarPat.
type ClassOrVar = Either EClassId Int
data Atom = Atom ClassOrVar (SRTree ClassOrVar) deriving Show

unFixPat :: Pattern -> SRTree Pattern
unFixPat (Fixed p) = p
{-# INLINE unFixPat #-}


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


cleanDB :: Monad m => EGraphST m ()
cleanDB = modify' $ over (eDB. patDB) (const Map.empty)

-- | Returns the substitution rules
-- for every match of the pattern `source` inside the e-graph.
match :: Monad m => Pattern -> EGraphST m [(Map ClassOrVar ClassOrVar, ClassOrVar)]
match src = do
  let (q, root) = compileToQuery src     -- compile the source of the pattern into a query
  substs <- genericJoin q root               -- find the substituion rules for this pattern
  pure [(s, s Map.! root) | s <- substs, Map.size s > 0]

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
genericJoin :: Monad m => Query -> ClassOrVar -> EGraphST m [Map ClassOrVar ClassOrVar]
genericJoin atoms root = do
  let vars = orderedVars atoms -- order the vars, starting with the most frequently occuring
  go atoms vars -- TODO: investigate why we need nub
  where
    -- for each variable
    --   for each possible e-class id for that variable
    --      replace the var id with this e-class id, and
    --      recurse to find the possible matches for the next atom
    go :: Monad m => Query -> [ClassOrVar] -> EGraphST m [Map ClassOrVar ClassOrVar]
    go atoms [] = pure [Map.empty] -- | _ <- atoms]
    go atoms (x:vars) = do cIds1 <- domainX x atoms root
                           maps <- forM cIds1 $ \classId -> do
                             map (Map.insert x classId) <$> go (updateVar x classId atoms) vars
                           pure (concat maps)


     -- [Map.insert x classId y | classId <- domainX db x atoms
     --                                           , y <- go (updateVar x classId atoms) vars]


-- | returns the e-class id for a certain variable that
-- matches the pattern described by the atoms
domainX :: Monad m => ClassOrVar -> Query -> ClassOrVar -> EGraphST m [ClassOrVar]
domainX var atoms root = do
  let atoms' = filter (elemOfAtom var) atoms -- :: [ClassOrVar]  -- look only in the atoms with this var
  map Left <$> intersectAtoms var atoms' root -- find the intersection of possible keys by each atom

  --let ss = (map Left
  --                                $ intersectAtoms var db
  --                                $
  --                     in ss

-- | returns all e-class id that can matches this sequence of atoms
intersectAtoms :: Monad m => ClassOrVar -> Query -> ClassOrVar -> EGraphST m [EClassId]
intersectAtoms _ [] root = pure []
intersectAtoms var (a:atoms) root = do
  a0 <- go a
  Set.toList <$> (foldM (\acc atom -> Set.intersection acc <$> go atom) a0 atoms)
  where
      -- canonize everything except the root for consistency
      -- doing this here prevents traversing the map again
      toCanon x = if var==root
                     then pure x
                     else Set.fromList <$> (mapM canonical $ Set.toList x)

      go (Atom r t) = do
        let op = getOperator t
        mTrie <- gets ((Map.!? op) . _patDB . _eDB)
        case mTrie of
          Just trie -> pure (fromMaybe Set.empty $ intersectTries var Map.empty trie (r:getElems t))
          Nothing   -> pure Set.empty
          -- TODO: remove FlexibleContexts
        --if op `Map.member` db -- if the e-graph contains the operator
                               -- try to find an intersection of the tries that matches each atom of the pattern
        --  then
        --  else pure Set.empty

-- | searches for the intersection of e-class ids that
-- matches each part of the query.
-- Returns Nothing if the intersection is empty.
--
-- var is the current variable being investigated
-- xs is the map of ids being investigated and their corresponding e-class id
-- trie is the current trie of the pattern
-- (i:ids) sequence of root : children of the atom to investigate
-- NOTE: it must be Maybe Set to differentiate between empty set and no answer
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
