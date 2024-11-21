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
         , countOccurrences
         , countUniqueTokens
         , numberOfVars
         , getIntConsts
         , relabelParams
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
         , countOccurrences
         , countUniqueTokens
         , numberOfVars
         , getIntConsts
         , relabelParams
         , relabelVars
         , constsToParam
         , floatConstsToParam
         , paramsToConst
         , removeProtectedOps
         , convertProtectedOps
         , Fix (..)
         )
