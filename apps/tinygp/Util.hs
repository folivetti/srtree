{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}

module Util where

import qualified Data.Map.Strict as Map
import Data.Massiv.Array as MA hiding (forM_, forM)
import Data.SRTree
import Data.SRTree.Eval
import Algorithm.SRTree.Opt
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Build
import Algorithm.EqSat.Info

import Algorithm.SRTree.NonlinearOpt
import System.Random
import Algorithm.SRTree.Likelihoods
--import Algorithm.SRTree.ModelSelection
--import Algorithm.SRTree.Opt
import qualified Data.IntMap.Strict as IM
import Control.Monad.State.Strict
import Control.Monad ( when, replicateM, forM, forM_ )
import Data.Maybe ( fromJust )
import Data.List ( maximumBy )
import Data.Function ( on )
import List.Shuffle ( shuffle )
import Data.List.Split ( splitOn )
import Data.Char ( toLower )
import qualified Data.IntSet as IntSet
import Data.SRTree.Datasets
import Algorithm.EqSat.Queries


type DataSet = (SRMatrix, PVector, Maybe PVector)


getTrain :: ((a, b1, c1, d1), (c2, b2), c3, d2) -> (a, b1, c2)
getTrain ((a, b, _, _), (c, _), _, _) = (a,b,c)

getX :: DataSet -> SRMatrix
getX (a, _, _) = a

getTarget :: DataSet -> PVector
getTarget (_, b, _) = b

getError :: DataSet -> Maybe PVector
getError (_, _, c) = c

loadTrainingOnly fname b = getTrain <$> loadDataset fname b


parseNonTerms = Prelude.map toNonTerm . splitOn ","
  where
    binTerms = Map.fromList [ (Prelude.map toLower (show op), op) | op <- [Add .. AQ]]
    uniTerms = Map.fromList [ (Prelude.map toLower (show f), f) | f <- [Abs .. Cube]]
    toNonTerm xs' = let xs = Prelude.map toLower xs'
                    in case binTerms Map.!? xs of
                          Just op -> Right $ \l r -> Fix $ Bin op l r
                          Nothing -> case uniTerms Map.!? xs of
                                          Just f -> Left $ \t -> Fix $ Uni f t
                                          Nothing -> error $ "invalid non-terminal " <> show xs

