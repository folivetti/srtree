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
  , ctStatic :: !(VB.Vector (VU.Vector Double))       -- precomputed values; empty vector for dynamic ids
  , ctM      :: !Int
  }
