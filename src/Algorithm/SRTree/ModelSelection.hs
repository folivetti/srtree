{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
-------------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.SRTree.ModelSelection
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
-- Helper functions for model selection criteria
-------------------------------------------------------------------------------

module Algorithm.SRTree.ModelSelection 
    ( bic
    , aic
    , evidence
    , fractionalBayesFactor
    , mdl
    , mdlLatt
    , mdlFreq
    , logFunctional
    , logFunctionalFreq
    , module Algorithm.SRTree.Compile
    ) where

import Algorithm.SRTree.Utils ( det )
import Algorithm.SRTree.Likelihoods ( fisherNLL, hessianNLL, nll, Distribution(..) )
import Data.SRTree
import Data.SRTree.Eval (Target, Columns)
import Data.SRTree.Recursion (cata)
import qualified Data.Vector.Unboxed as U
import Algorithm.SRTree.Compile

import Debug.Trace

-- | Bayesian information criterion
bic :: EvaluatedTree -> Double
bic et = valParams et * log (valRows et) + 2 * valLoss et
{-# INLINE bic #-}

-- | Akaike information criterion
aic :: EvaluatedTree -> Double
aic et = 2 * valParams et + 2 * valLoss et
{-# INLINE aic #-}

-- | Evidence
evidence :: EvaluatedTree -> Double
evidence et = (1 - b) * valLoss et - valParams et / 2 * log b
  where
    b = 1 / sqrt (valRows et)
{-# INLINE evidence #-}

fractionalBayesFactor :: EvaluatedTree -> Double
fractionalBayesFactor et = (1 - b) * valLoss et - valParams et / 2 * log b + f_compl + valParams et / 2 * log(2*pi*nup)
  where
    b = 1 / sqrt (valRows et)
    nup = exp(1 - log 3)
    f_compl = countNodes (valTree et) * log (countUniqueTokens (valTree et))
{-# INLINE fractionalBayesFactor #-}

-- | MDL as described in
-- Bartlett, Deaglan J., Harry Desmond, and Pedro G. Ferreira. "Exhaustive symbolic regression." IEEE Transactions on Evolutionary Computation (2023).
mdl :: EvaluatedTree -> Double
mdl et = valLoss et + logFunctional (valTree et) + valLogParams et
{-# INLINE mdl #-}

-- | MDL Lattice as described in
-- Bartlett, Deaglan, Harry Desmond, and Pedro Ferreira. "Priors for symbolic regression." Proceedings of the Companion Conference on Genetic and Evolutionary Computation. 2023.
mdlLatt :: EvaluatedTree -> Double
mdlLatt et = valLoss et + logFunctional (valTree et) + valLogParamsLattice et
{-# INLINE mdlLatt #-}

-- | same as `mdl` but weighting the functional structure by frequency calculated using a wiki information of
-- physics and engineering functions
mdlFreq :: EvaluatedTree -> Double
mdlFreq et = valLoss et + logFunctionalFreq (valTree et) + valLogParams et
{-# INLINE mdlFreq #-}

-- log of the functional complexity
logFunctional :: Fix SRTree -> Double
logFunctional tree = countNodes tree * log (countUniqueTokens tree') + foldr (\c acc -> log (abs c) + acc) 0 consts  + log(2) * numberOfConsts
  where
    tree' = fst $ floatConstsToParam tree
    consts = getIntConsts tree
    numberOfConsts = fromIntegral $ length consts
{-# INLINE logFunctional #-}

-- same as above but weighted by frequency
logFunctionalFreq :: Fix SRTree -> Double
logFunctionalFreq tree = treeToNat tree'  + foldr (\c acc -> log (abs c) + acc) 0 consts  + countVarNodes tree * log (numberOfVars tree)
  where
    tree' = fst $ floatConstsToParam tree
    consts = getIntConsts tree
{-# INLINE logFunctionalFreq #-}


treeToNat :: Fix SRTree -> Double
treeToNat = cata $ \case
  Uni f t -> funToNat f + t
  Bin op l r -> opToNat op + l + r
  _ -> 0.6610799229372109
  where
    opToNat :: Op -> Double
    opToNat Add = 2.500842464597881
    opToNat Sub = 2.500842464597881
    opToNat Mul = 1.720356134912558
    opToNat Div = 2.60436883851265
    opToNat Power = 2.527957363394847
    opToNat PowerAbs = 2.527957363394847
    opToNat AQ = 2.60436883851265

    funToNat :: Function -> Double
    funToNat Sqrt = 4.780867285331753
    funToNat Log = 4.765599813200964
    funToNat Exp = 4.788589331425663
    funToNat Abs = 6.352564869783006
    funToNat Sin = 5.9848400896576885
    funToNat Cos = 5.474014465891698
    funToNat Sinh = 8.038963823353235
    funToNat Cosh = 8.262107374667444
    funToNat Tanh = 7.85664226655928
    funToNat Tan = 8.262107374667444
    funToNat _ = 8.262107374667444
{-# INLINE treeToNat #-}
