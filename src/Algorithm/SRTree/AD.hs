-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.AD 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Automatic Differentiation for Expression trees
--
-----------------------------------------------------------------------------

module Algorithm.SRTree.AD
         ( compileFunAndGrad
         , ADBackEnd(..)
         ) where

import qualified Data.Vector.Unboxed  as VU
import qualified Data.Vector.Storable as V
import Data.SRTree
import Algorithm.SRTree.AD.Unboxed
import Algorithm.SRTree.AD.Accelerate

data ADBackEnd = SingleThread | MultiThread | Accelerate deriving (Read, Show)

compileFunAndGrad :: ADBackEnd -> [VU.Vector Double] -> VU.Vector Double -> Maybe (VU.Vector Double) -> Fix SRTree -> V.Vector Double -> (Double, V.Vector Double)
compileFunAndGrad SingleThread xss ys mYerr tree = evalGrad (compileTree xss ys mYerr tree)
compileFunAndGrad MultiThread xss ys mYerr tree  = evalGradMulti (compileTreeMulti xss ys mYerr tree)
compileFunAndGrad Accelerate xss ys mYerr tree   = compileAccelerateTree (compileTree xss ys mYerr tree) xss ys
