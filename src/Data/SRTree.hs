-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
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
         , IndexedTree
         , NamedTree
         , Function(..)
         , Op(..)
         , param
         , var
         , constv
         , arity
         , getChildren
         , childrenOf
         , replaceChildren
         , getOperator
         , countNodes
         , countVarNodes
         , countConsts
         , countParams
         , countParamsUniq
         , countOccurrences
         , countUniqueTokens
         , numberOfVars
         , getIntConsts
         , relabelParams
         , relabelParamsOrder
         , relabelVars
         , constsToParam
         , floatConstsToParam
         , paramsToConst
         , removeProtectedOps
         , convertProtectedOps
         , Fix (..)
         )
         where
         
import Data.SRTree.Internal 
         ( SRTree(..)
         , NamedTree
         , IndexedTree
         , Function(..)
         , Op(..)
         , param
         , var
         , constv
         , arity
         , getChildren
         , childrenOf
         , replaceChildren
         , getOperator
         , countNodes
         , countVarNodes
         , countConsts
         , countParams
         , countParamsUniq
         , countOccurrences
         , countUniqueTokens
         , numberOfVars
         , getIntConsts
         , relabelParams
         , relabelParamsOrder
         , relabelVars
         , constsToParam
         , floatConstsToParam
         , paramsToConst
         , removeProtectedOps
         , convertProtectedOps
         , Fix (..)
         )
