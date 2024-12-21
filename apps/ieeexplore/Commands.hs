{-# language OverloadedStrings #-}
{-# language TupleSections #-}

module Commands where

import Control.Applicative ((<|>))
import Data.Attoparsec.ByteString.Char8 hiding ( match )
import qualified Data.ByteString.Char8 as B
import Data.Maybe
import Data.Monoid (All(..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Control.Monad.State.Strict
import qualified Data.Map as Map
import qualified Data.HashSet as Set
import qualified Data.Massiv.Array as MA
import Data.List ( nub, sortOn )

import Data.SRTree
import Data.SRTree.Datasets
import Data.SRTree.Recursion
import Data.SRTree.Eval
import Data.SRTree.Print hiding ( printExpr )
import Text.ParseSR (SRAlgs(..), parseSR, parsePat)

import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.Opt

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Build
import Algorithm.EqSat.Info
import Algorithm.EqSat.Queries
import Algorithm.EqSat.DB
import Algorithm.EqSat.Simplify

import Data.Binary ( encode, decode )
import qualified Data.ByteString.Lazy as BS

import Util

-- * Parsing

-- top 5 by fitness|mdl [less than 5 params, less than 10 nodes]
data Command  = Top Int Filter Criteria PatStr
              | Distribution FilterDist (Maybe Limit)
              -- below these will not be a parsable command
              | Report EClassId ArgOpt
              | Optimize EClassId Int ArgOpt
              | Insert String ArgOpt
              | Subtrees EClassId -- TODO: bug
              | Pareto Criteria -- TODO
              | CountPat String
              | Save String
              | Load String

type Filter = EClass -> Bool -- pattern?
type FilterDist = Int -> Bool
data Criteria = ByFitness | ByDL deriving Eq
data Limit = Limit Int Bool deriving Show
data PatStr = PatStr String Bool | AntiPatStr String Bool | NoPat
type ArgOpt = (Distribution, DataSet, DataSet)

-- top 10 with <=10|=10 size with <=4 parameters by fitness|dl matching pat
-- report id
-- optimize id
-- insert eq
-- subtrees id
-- distribution with size <=10 limited at 10 asc|dsc

parseCmd parser = eitherResult . (`feed` "") . parse parser . putEOL . B.strip

stripSp = many' (char ' ')

parseTop = do n <- decimal
              stripSp
              filters  <- many' parseFilter
              stripSp
              criteria <- fromMaybe ByFitness . listToMaybe <$> many' parseCriteria
              stripSp
              pats' <- many' (parsePattern <|> parseAnti)
              pats <- case pats' of
                        [] -> pure $ NoPat
                        (x:_) -> pure $ x
              pure $ Top n (getAll . mconcat filters) criteria pats

parseDist = do filters <- fromMaybe (const True) . listToMaybe <$> many' parseFilterDist
               stripSp
               limit   <- listToMaybe <$> many' parseLimit
               pure $ Distribution filters limit

parseFilter = do stringCI "with"
                 stripSp
                 field <- parseSz <|> parseCost <|> parseParams
                 stripSp
                 cmp <- parseCmp
                 pure (\ec -> All $ cmp (field ec))
parseFilterDist = do stringCI "with"
                     stripSp
                     stringCI "size"
                     stripSp
                     cmp <- parseCmp
                     pure cmp

parseSz = stringCI "size" >> pure (_size . _info)
parseCost = stringCI "cost" >> pure (_cost . _info)
parseParams = stringCI "parameters" >> pure (mbLen . _theta . _info)
   where
      mbLen Nothing = 0
      mbLen (Just ps) = MA.unSz $ MA.size ps
parseCmp = do op <- parseLEQ <|> parseLT <|> parseEQ <|> parseGEQ <|> parseGT
              stripSp
              n <- decimal
              pure (`op` n)

parseLT  = string "<"  >> pure (<)
parseLEQ = string "<=" >> pure (<=)
parseEQ  = string "="  >> pure (==)
parseGEQ = string ">="  >> pure (>=)
parseGT  = string ">" >> pure (>)

parsePattern = do stringCI "matching"
                  stripSp
                  b <- option True parseRoot
                  pat <- many' anyChar
                  pure $ PatStr pat b
parseAnti = do stringCI "not matching"
               stripSp
               b <- option True parseRoot
               pat <- many' anyChar
               pure $ AntiPatStr pat b

parseLimit = do stringCI "limited at"
                stripSp
                n <- decimal
                stripSp
                ascOrdsc <- stringCI "asc" <|> stringCI "dsc"
                pure $ Limit n (ascOrdsc == "asc")
parseRoot = do stringCI "root"
               stripSp
               pure False
parseCriteria = parseByFit <|> parseByDL
parseByFit = do stringCI "by fitness"
                pure ByFitness
parseByDL  = do stringCI "by dl"
                pure ByDL

putEOL :: B.ByteString -> B.ByteString
putEOL bs | B.last bs == '\n' = bs
          | otherwise         = B.snoc bs '\n'

-- running
run (Top n filters criteria NoPat) = do
   let getFun = if criteria == ByFitness then getTopFitEClassThat else getTopDLEClassThat
   ids <- egraph $ getFun n filters
   printSimpleMultiExprs $ reverse ids

run (Top n filters criteria withPat) = do
   let (pat', getFun, isParents) =
          case withPat of
            PatStr p parent     -> (p, if criteria == ByFitness then getTopFitEClassIn    else getTopDLEClassIn, parent)
            AntiPatStr p parent -> (p, if criteria == ByFitness then getTopFitEClassNotIn else getTopDLEClassNotIn, parent)

   let etree = parsePat $ B.pack pat'
   case etree of
     Left _ -> io.putStrLn $ "no parse for " <> pat'
     Right pat -> do
        ecs' <- egraph $ (Prelude.map fromLeft . Prelude.filter isLeft . Prelude.map snd) <$> match pat
        ecs  <- egraph $ Prelude.mapM canonical ecs'
                           >>= getParents isParents
        ids  <- egraph $ getFun n filters ecs
        printSimpleMultiExprs (reverse $ nub ids)

run (Distribution pSz mLimit) = do
  ee <- egraph $ IntSet.toList . IntSet.fromList <$> getAllEvaluatedEClasses
  allPats <- egraph $ getAllPatternsFrom Map.empty ee
  let (n, isAsc) = case mLimit of
                     Nothing -> (Map.size allPats, True)
                     Just (Limit sz asc) -> (sz, asc)
  printMultiCounts (Prelude.take n
                   $ sortOn (if isAsc then snd else negate . snd)
                   $ Map.toList
                   $ Map.filterWithKey (\k v -> k /= VarPat 'A' && pSz (lenPat k))
                   allPats)

run (Report eid (dist, trainData, testData)) = egraph $ printExpr trainData testData dist eid

run (Optimize eid nIters (dist, trainData, testData)) = do -- dist trainData testData
   t <- egraph $ getBestExpr eid
   (f, theta) <- egraph $ fitnessFunRep nIters dist trainData trainData t
   egraph $ insertFitness eid f theta
   printSimpleMultiExprs [eid]

run (Insert expr argOpt) = do
  let etree = parseSR TIR "" False $ B.pack expr
  case etree of
    Left _     -> io.putStrLn $ "no parse for " <> expr
    Right tree -> do eid <- egraph $ fromTree myCost tree
                     run (Optimize eid 100 argOpt)

run (Subtrees eid) = do
   isValid <- egraph $ gets ((IntMap.member eid) . _eClass)
   if isValid
     then do ids <- egraph $ getAllChildEClasses eid
             printSimpleMultiExprs ids
     else io.putStrLn $ "Invalid id."

run (Pareto crit) = do
   maxSize <- egraph $ gets (fst . IntMap.findMax . _sizeFitDB . _eDB)
   ecs <- egraph $ case crit of
            ByFitness -> getParetoEcsUpTo True  1 maxSize
            ByDL      -> getParetoEcsUpTo False 1 maxSize
   printSimpleMultiExprs ecs

run (CountPat spat) = do
  let etree = parsePat $ B.pack spat
  case etree of
    Left _     -> io.putStrLn $ "no parse for " <> spat
    Right pat  -> do (p, cnt) <- countPattern pat
                     io . putStrLn $ spat <> " appears in " <> show cnt <> " equations."

run (Save fname) = do
  eg <- egraph get
  io $ BS.writeFile fname (encode eg)

run (Load fname) = do
  eg <- io $ BS.readFile fname
  egraph $ put (decode eg)

-- * auxiliary functions

getParents False ecs = pure ecs
getParents True  ecs = IntSet.toList <$> getParentsOf (IntSet.fromList ecs) 500000 (IntSet.fromList ecs)

isBest (e', en') = do e <- canonical e'
                      best <- gets (_best . _info . (IntMap.! e) . _eClass) >>= canonize
                      en <- canonize en'
                      pure (en == best)

getParentsOf :: IntSet.IntSet -> Int -> IntSet.IntSet -> RndEGraph IntSet.IntSet
getParentsOf visited n queue | IntSet.size queue >= n = pure queue
getParentsOf visited n queue =
   do ecs          <- Prelude.mapM canonical (IntSet.toList queue)
      parents'     <- IntSet.unions <$> Prelude.mapM canonizeParents ecs
      uneval       <- gets (_unevaluated . _eDB)
      grandParents <- getParentsOf (IntSet.union visited parents') (n-1) parents'
      pure (IntSet.filter (not . (`IntSet.member` uneval)) $ (queue <> grandParents))
   where
      canonizeParents ec = do parents <- gets (_parents . (IntMap.! ec) . _eClass)
                                          >>= Prelude.mapM (\(e, en) -> isBest (e, en) >>= \b -> pure (e, en, b)) . Set.toList
                                          >>= pure . Set.fromList

                              pure $ IntSet.fromList . Prelude.map (\(e, _, _) -> e) . Set.toList $
                                    Set.filter (\(e, en, b) -> b && ec `Prelude.elem` (childrenOf en)
                                                   && not (e `IntSet.member` visited)
                                                ) parents


isLeft (Left _)   = True
isLeft _          = False
fromLeft (Left x) = x
fromLeft _        = undefined

getAllPatternsFrom :: Monad m => Map.Map Pattern Int -> [EClassId] -> EGraphST m (Map.Map Pattern Int)
getAllPatternsFrom counts []     = pure counts
getAllPatternsFrom counts (x:xs) = do pats <- Map.fromListWith (+) . Prelude.map (,1) <$> getAllPatterns x
                                      getAllPatternsFrom (Map.unionWith (+) pats counts) xs

relabelVarPat :: Pattern -> Pattern
relabelVarPat t = alg t `evalState` 65
   where
      alg :: Pattern -> State Int Pattern
      alg (VarPat _) = do ix <- Control.Monad.State.Strict.get; Control.Monad.State.Strict.modify (+1); pure (VarPat $ toEnum ix)
      alg (Fixed (Uni f t')) = do t <- alg t'; pure $ Fixed (Uni f t)
      alg (Fixed (Bin op l' r')) = do l <- alg l'; r <- alg r'; pure $ Fixed (Bin op l r)
      alg pt                   = pure pt

lenPat :: Pattern -> Int
lenPat (Fixed (Uni _ t)) = 1 + lenPat t
lenPat (Fixed (Bin _ l r)) = 1 + lenPat l + lenPat r
lenPat _ = 1

countPattern pat = do
  ecs' <- egraph $ (Prelude.map fromLeft . Prelude.filter isLeft . Prelude.map snd) <$> match pat
  ecs <- egraph $ Prelude.mapM canonical ecs'
                    >>= getEvaluated
  pure (pat, IntSet.size ecs)

getEvaluated ecs = getParentsOf (IntSet.fromList ecs) 500000 (IntSet.fromList ecs)

getAllPatterns :: Monad m => EClassId -> EGraphST m [Pattern]
getAllPatterns eid = do
   eid' <- canonical eid
   best <- gets (_best . _info . (IntMap.! eid') . _eClass)
   case best of
      Var ix     -> pure [VarPat 'A', Fixed (Var ix)]
      Param ix   -> pure [VarPat 'A', Fixed (Param ix)]
      Const x    -> pure [VarPat 'A', Fixed (Const x)]
      Uni f t    -> do pats <- getAllPatterns t
                       pure (VarPat 'A' : [relabelVarPat $ Fixed (Uni f t') | t' <- pats])
      Bin op l r | l==r -> do pats <- getAllPatterns l
                              pure (VarPat 'A' : [relabelVarPat $ Fixed (Bin op l' l') | l' <- pats])
                  | otherwise -> do patsL <- getAllPatterns l
                                    patsR <- getAllPatterns r
                                    pure (VarPat 'A' : [relabelVarPat $ Fixed (Bin op l' r') | l' <- patsL, r' <- patsR])


