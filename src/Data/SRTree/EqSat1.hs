{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.EqSat1
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Equality Saturation for SRTree
--
-----------------------------------------------------------------------------

module Data.SRTree.EqSat1 where

import Data.SRTree
import Data.SRTree.Eval
import Data.SRTree.Recursion ( cataM )
import Control.Monad
import Control.Monad.State
import Control.Lens ( (+~), (-~), makeLenses, (^.), (.~), (&), element, over )
import Data.IntMap
import Data.Set ( Set )
import Data.Map ( Map )
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Random
import Data.Ratio
import Debug.Trace
import Data.SRTree.Egraph
import Data.SRTree.EqSatDB

-- eqSat :: Scheduler -> Expr -> Rules -> Cost -> Expr
eqSat = undefined

-- getBest :: Cost -> EGraph -> EClassId -> Expr
getBest = undefined

-- runEqSat :: EGraph -> Scheduler -> Rules -> EGraph
runEqSat = undefined

-- matchWithScheduler :: DB -> Int -> ScheduleMap -> Int -> Rule -> [(Rule, Match)]
matchWithScheduler = undefined
