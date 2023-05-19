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
         , Op(..)
         , param
         , var
         , arity
         , getChildren
         , countNodes
         , countVarNodes
         , countConsts
         , countParams
         , countOccurrences
         , deriveBy
         , deriveByVar
         , deriveByParam
         , derivative
         , forwardMode
         , gradParams
         , gradParams2
         , evalFun
         , evalOp
         , inverseFunc
         , evalTree
         , relabelParams
         , constsToParam
         , floatConstsToParam
         )
         where
         
import Data.SRTree.Internal 
         ( SRTree(..)
         , Function(..)
         , Op(..)
         , param
         , var
         , arity
         , getChildren
         , countNodes
         , countVarNodes
         , countConsts
         , countParams
         , countOccurrences
         , deriveBy
         , deriveByVar
         , deriveByParam
         , derivative
         , forwardMode
         , gradParams
         , gradParams2
         , evalFun
         , evalOp
         , inverseFunc
         , evalTree
         , relabelParams
         , constsToParam
         , floatConstsToParam
         , paramsToConst
         , Fix (..)
         )
