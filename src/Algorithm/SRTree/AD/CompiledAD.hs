-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.AD.CompiledAD
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Automatic Differentiation for Expression trees
--
-----------------------------------------------------------------------------

module Algorithm.SRTree.AD.CompiledAD
         ( CompiledTree(..)
         ) where

import Data.SRTree.Internal
import qualified Data.Vector.Unboxed          as VU
import qualified Data.Vector as VB

-- ---------------------------------------------------------------------
-- Public entry point -- same signature/behaviour as before.
-- ---------------------------------------------------------------------
data CompiledTree = CompiledTree
  { ctNodes  :: !(VB.Vector (SRTree Int))            -- id -> node, children already resolved to ids
  , ctRoot   :: !Int
  , ctDyn    :: !(VU.Vector Bool)                    -- id -> depends on theta?
  , ctStatic :: VU.Vector Double                     -- flat [node * m + row]; 0-filled for dynamic ids
  , ctM      :: !Int
  , ctNPred  :: !Int                                 -- root + 1 (stride for flat static)
  , ctKind   :: !(VU.Vector Int)                     -- id -> node kind: 0 Var, 1 Param, 2 Const, 3 Uni, 4 Bin
  , ctArg    :: !(VU.Vector Int)                     -- id -> Param: param ix; Uni: child id; Bin: left id
  , ctArg2   :: !(VU.Vector Int)                     -- id -> Bin: right id; else 0
  , ctFcode  :: !(VU.Vector Int)                     -- id -> Uni: fromEnum Function
  , ctOcode  :: !(VU.Vector Int)                     -- id -> Bin: fromEnum Op
  }
