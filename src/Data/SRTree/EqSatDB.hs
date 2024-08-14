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
import Data.SRTree.EqSat1
import Data.Maybe ( fromMaybe )
import Data.Char ( ord ) 
import Data.List ( nub, sortBy )
import Data.Ord ( comparing )

-- The database maps a symbol to an IntTrie
-- The IntTrie stores the possible paths from a certain e-class 
-- that matches a pattern 
type DB = Map (SRTree ()) IntTrie
-- The IntTrie is composed of the set of available keys (for convenience)
-- and an IntMap that maps one e-class id to the first child IntTrie,
-- the first child IntTrie will point to the next child and so on
data IntTrie = IntTrie { _keys :: Set EClassId, _trie :: IntMap IntTrie } deriving Show

-- A Pattern is either a fixed-point of a tree or an
-- index to a pattern variable. The pattern variable matches anything. 
data Pattern = Fixed (Fix SRTree) | VarPat Char -- Fixed structure of a pattern or a variable that matches anything 

-- A rule is either a directional rule where pat1 can be replaced by pat2, a bidirectional rule 
-- where pat1 can be replaced or replace pat2, or a pattern with a conditional function 
-- describing when to apply the rule 
data Rule = Pattern :=> Pattern | Pattern :==: Pattern | Rule :| (IntMap EClassId -> EGraph -> Bool)

-- A Query is a list of Atoms 
type Query = [Atom] 

-- An Atom is composed of either an e-class id or pattern variable id
-- and the tree that generated that pattern 
type ClassOrVar = Either EClassId Int
data Atom = Atom ClassOrVar (SRTree ClassOrVar)

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
                                      
match :: DB -> Pattern -> _
match db source = [(s, s Map.! root) | s <- substs, Map.size s > 0]
  where 
    (q, root) = compileToQuery source 
    substs    = genericJoin db q 

compileToQuery :: Pattern -> (Query, ClassOrVar)
compileToQuery pat = (atoms, root)
  where
      getInt (Left a)  = a
      getInt (Right a) = a

      (atoms, root) = evalState (processPat pat) 256
      processPat :: Pattern -> State Int (Query, ClassOrVar)
      processPat (VarPat x)  = pure ([], Right $ ord x)
      processPat (Fixed pat) = do
          v <- get 
          let root = Right v 
          modify (+1)
          let children = getChildren pat 
          patChilds <- mapM (processPat . Fixed) children -- [processPat (Fixed child) | child <- children]
          let atoms = concatMap fst patChilds
              roots = map snd patChilds
              atom  = Atom root (replaceChildren roots (unfix pat))
              atoms' = atom:atoms
          pure (atoms', root)

genericJoin = undefined 

getElems (Bin _ l r) = [l,r]
getElems (Uni _ t)   = [t]
getElems _           = []

updateVar :: ClassOrVar -> ClassOrVar -> Query -> Query
updateVar var x = map replace
  where
      replace (Atom r t) = let children = [if c == var then x else c | c <- getElems t]
                               t'       =  replaceChildren children t 
                            in Atom (if r == var then x else r) t'

orderedVars :: Query -> [ClassOrVar]
orderedVars atoms = sortBy (comparing varCost) $ nub [a | atom <- atoms, a <- getIdsFrom atom, isRight a] 
  where
    getIdsFrom (Atom r t) = r : getElems t
    isRight (Right _) = True 
    isRight _ = False


    elemOfAtom :: ClassOrVar -> Atom -> Bool
    elemOfAtom v (Atom root tree) =
        case root of 
          Left _  -> v `elem` getElems tree
          Right x -> Right x == v 

    varCost :: ClassOrVar -> Int 
    varCost var = foldr (\a acc -> if elemOfAtom var a then acc - 100 + atomLen a else acc) 0 atoms

    atomLen (Atom _ t) = 1 + length (getElems t)
