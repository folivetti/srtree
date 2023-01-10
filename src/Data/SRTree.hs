-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables, ConstraintKinds
--
-- Expression tree for Symbolic Regression
--
-----------------------------------------------------------------------------
module Data.SRTree 
         ( SRTree(..)
         , Function(..)
         , OptIntPow(..)
         , traverseIx
         , arity
         , getChildren
         , countNodes
         , countVarNodes
         , countOccurrences
         , deriveBy
         , simplify
         , derivative
         , evalFun
         , inverseFunc
         , evalTree
         , evalTreeMap
         , evalTreeWithMap
         , evalTreeWithVector
         , relabelOccurrences
         , relabelParams
         )
         where
         
import Data.SRTree.Internal ( SRTree(..)
         , Function(..)
         , OptIntPow(..)
         , traverseIx
         , arity
         , getChildren
         , countNodes
         , countVarNodes
         , countOccurrences
         , deriveBy
         , simplify
         , derivative
         , evalFun
         , inverseFunc
         , evalTree
         , evalTreeMap
         , evalTreeWithMap
         , evalTreeWithVector
         , relabelOccurrences
         , relabelParams
         )
