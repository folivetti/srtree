{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.SRTree.ModelSelection 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
-- Helper functions for model selection criteria
--
-----------------------------------------------------------------------------

module Algorithm.SRTree.ModelSelection where

import Algorithm.Massiv.Utils ( det )
import Algorithm.SRTree.Likelihoods
    ( PVector, SRMatrix, fisherNLL, hessianNLL, nll, Distribution )
import Data.Massiv.Array (Ix2 (..), Sz (..), (!-!))
import qualified Data.Massiv.Array as A
import Data.SRTree
import Data.SRTree.Eval (evalTree)
import Data.SRTree.Recursion (cata)
import qualified Data.Vector.Storable as VS

import Debug.Trace

-- | Bayesian information criterion
bic :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
bic dist mYerr xss ys theta tree = p * log n + 2 * nll dist mYerr xss ys tree theta
  where
    (A.Sz (fromIntegral -> p)) = A.size theta
    (A.Sz (fromIntegral -> n)) = A.size ys
{-# INLINE bic #-}

-- | Akaike information criterion
aic :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
aic dist mYerr xss ys theta tree = 2 * p + 2 * nll dist mYerr xss ys tree theta
  where
    (A.Sz (fromIntegral -> p)) = A.size theta
    (A.Sz (fromIntegral -> n)) = A.size ys
{-# INLINE aic #-}

-- | Evidence 
evidence :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
evidence dist mYerr xss ys theta tree = (1 - b) * nll dist mYerr xss ys tree theta - p / 2 * log b
  where
    (A.Sz (fromIntegral -> p)) = A.size theta
    (A.Sz (fromIntegral -> n)) = A.size ys
    b = 1 / sqrt n
{-# INLINE evidence #-}

fractionalBayesFactor :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
fractionalBayesFactor dist mYerr xss ys theta tree = (1 - b) * nll dist mYerr xss ys tree theta - p / 2 * log b + f_compl + p / 2 * log(2*pi*nup)
  where
    (A.Sz (fromIntegral -> p)) = A.size theta
    (A.Sz (fromIntegral -> n)) = A.size ys
    b = 1 / sqrt n
    nup = exp(1 - log 3)
    f_compl = countNodes tree * log (countUniqueTokens tree)
{-# INLINE fractionalBayesFactor #-}

-- | MDL as described in 
-- Bartlett, Deaglan J., Harry Desmond, and Pedro G. Ferreira. "Exhaustive symbolic regression." IEEE Transactions on Evolutionary Computation (2023).
mdl :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
mdl dist mYerr xss ys theta tree =   nll' dist mYerr xss ys theta tree
                                   + logFunctional tree
                                   + logParameters dist mYerr xss ys theta tree
  where
    fisher = fisherNLL dist mYerr xss ys tree theta
    theta' = A.computeAs A.S $ A.zipWith (\t f -> if isSignificant t f then t else 0.0) theta fisher
    isSignificant v f = abs (v / sqrt(12 / f) ) >= 1
{-# INLINE mdl #-}

-- | MDL Lattice as described in
-- Bartlett, Deaglan, Harry Desmond, and Pedro Ferreira. "Priors for symbolic regression." Proceedings of the Companion Conference on Genetic and Evolutionary Computation. 2023.
mdlLatt :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
mdlLatt dist mYerr xss ys theta tree = nll' dist mYerr xss ys theta' tree
                                     + logFunctional tree
                                     + logParametersLatt dist mYerr xss ys theta tree
  where
    fisher = fisherNLL dist mYerr xss ys tree theta
    theta' = A.computeAs A.S $ A.zipWith (\t f -> if isSignificant t f then t else 0.0) theta fisher
    isSignificant v f = abs (v / sqrt(12 / f) ) >= 1
{-# INLINE mdlLatt #-}

-- | same as `mdl` but weighting the functional structure by frequency calculated using a wiki information of
-- physics and engineering functions
mdlFreq :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
mdlFreq dist mYerr xss ys theta tree = nll dist mYerr xss ys tree theta
                                     + logFunctionalFreq tree
                                     + logParameters dist mYerr xss ys theta tree
{-# INLINE mdlFreq #-}

-- log of the functional complexity
logFunctional :: Fix IndexedTree -> Double
logFunctional tree = countNodes tree * log (countUniqueTokens tree')
                   + foldr (\c acc -> log (abs c) + acc) 0 consts 
                   + log(2) * numberOfConsts
  where
    tree'          = fst $ floatConstsToParam tree
    consts         = getIntConsts tree
    numberOfConsts = fromIntegral $ length consts
    signs          = sum [1 | a <- getIntConsts tree, a < 0] -- TODO: will we use that?
{-# INLINE logFunctional #-}

-- same as above but weighted by frequency 
logFunctionalFreq  :: Fix IndexedTree -> Double
logFunctionalFreq tree = treeToNat tree' 
                       + foldr (\c acc -> log (abs c) + acc) 0 consts  
                       + countVarNodes tree * log (numberOfVars tree)
  where
    tree'  = fst $ floatConstsToParam tree
    consts = getIntConsts tree
{-# INLINE logFunctionalFreq #-}

-- log of the parameters complexity
logParameters :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
logParameters dist mYerr xss ys theta tree = -(p / 2) * log 3 + 0.5 * logFisher + logTheta
  where
    -- p      = fromIntegral $ VS.length theta
    fisher = fisherNLL dist mYerr xss ys tree theta

    (logTheta, logFisher, p) = foldr addIfSignificant (0, 0, 0)
                             $ zip (A.toList theta) (A.toList fisher)

    addIfSignificant (v, f) (acc_v, acc_f, acc_p)
       | isSignificant v f = (acc_v + log (abs v), acc_f + log f, acc_p + 1)
       | otherwise         = (acc_v, acc_f, acc_p)

    isSignificant v f = abs (v / sqrt(12 / f) ) >= 1

-- same as above but for the Lattice 
logParametersLatt :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
logParametersLatt dist mYerr xss ys theta tree = 0.5 * p * (1 - log 3) + 0.5 * log detFisher
  where
    fisher = fisherNLL dist mYerr xss ys tree theta
    detFisher = det $ hessianNLL dist mYerr xss ys tree theta

    (logTheta, logFisher, p) = foldr addIfSignificant (0, 0, 0)
                             $ zip (A.toList theta) (A.toList fisher)

    addIfSignificant (v, f) (acc_v, acc_f, acc_p)
       | isSignificant v f = (acc_v + log (abs v), acc_f + log f, acc_p + 1)
       | otherwise         = (acc_v, acc_f, acc_p)

    isSignificant v f = abs (v / sqrt(12 / f) ) >= 1

-- flipped version of nll
nll' :: Distribution -> Maybe PVector -> SRMatrix -> PVector -> PVector -> Fix IndexedTree -> Double
nll' dist mYerr xss ys theta tree = nll dist mYerr xss ys tree theta
{-# INLINE nll' #-}

treeToNat :: Fix IndexedTree -> Double
treeToNat = cata $
  \case
    Uni f t    -> funToNat f + t
    Bin op l r -> opToNat op + l + r
    _          -> 0.6610799229372109
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
    funToNat Log  = 4.765599813200964
    funToNat Exp  = 4.788589331425663
    funToNat Abs  = 6.352564869783006
    funToNat Sin  = 5.9848400896576885
    funToNat Cos  = 5.474014465891698
    funToNat Sinh = 8.038963823353235
    funToNat Cosh = 8.262107374667444
    funToNat Tanh = 7.85664226655928
    funToNat Tan  = 8.262107374667444
    funToNat _    = 8.262107374667444
    --funToNat Factorial = 7.702491586732021
{-# INLINE treeToNat #-}
