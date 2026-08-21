{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.EqSat.Simplify
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :
--
-- Module containing the algebraic rules and simplification function.
--
-----------------------------------------------------------------------------
module Algorithm.EqSat.Simplify ( Rule(..), simplifyEqSatDefault, applyMergeOnlyDftl, rewrites, rewritesParams, rewriteBasic, rewritesFun, rewritesSimple, rewritesWithConstant, myCost ) where

import Algorithm.EqSat (eqSat, applySingleMergeOnlyEqSat)
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.DB
  ( ClassOrVar,
    Condition (Condition),
    NChild (Ch, MapP, Rest),
    Pattern (Fixed, Hole, NAry, VarPat),
    Rule (..),
    Subst,
    SubVal (SVMap, SVOne),
    getInt,
  )
import Control.Monad.State.Strict (evalState)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Map (Map)
import qualified Data.Map as Map
import Data.SRTree

-- | A constraint over a match's substitution: when applied to a substitution it
-- runs in the e-graph monad and fetches e-class data through 'ClassStore', so it
-- works on a paged (out-of-core) graph whose resident cache is bounded/empty.
type ConstrFun = Pattern -> Condition

constrainOnVal :: (Consts -> Bool) -> Pattern -> Condition
constrainOnVal f (VarPat c) = Condition $ \subst -> do
    let cid = getInt $ case Map.lookup (Right (fromEnum c)) subst of
                        Nothing -> error $ "CONSTRAINVAL_MISSING var=" <> show (fromEnum c) <> " substSize=" <> show (Map.size subst)
                        Just (SVOne v) -> v
                        Just (SVMap _) -> error $ "CONSTRAINVAL_REST_AS_SINGLE var=" <> show (fromEnum c)
    ec <- getEClass cid
    pure (f (_consts . _info $ ec))
constrainOnVal _ _ = Condition $ \_ -> pure False

-- TODO: aux functions to avoid repeated pattern in constraint creation 
--
-- check if a matched pattern contains constant 
isConstPt :: ConstrFun
isConstPt = constrainOnVal $ 
    \case
       ConstVal _ -> True 
       _          -> False

-- check if the matched pattern is a positive constant 
isConstPos :: ConstrFun
isConstPos = constrainOnVal $
    \case
      ConstVal x -> x > 0 
      _          -> False

isNotParam :: ConstrFun
isNotParam = constrainOnVal $
   \case
      ParamIx _ -> False
      _         -> True

-- check if the matched pattern is nonzero
isNotZero :: ConstrFun
isNotZero = constrainOnVal $
    \case
       ConstVal x -> abs x > 1e-9
       _          -> True

-- check if the matched pattern is even 
isEven :: ConstrFun
isEven = constrainOnVal $
    \case
       ConstVal x -> ceiling x == floor x && even (round x) 
       _          -> True

-- check if the matched pattern is integer
isInteger :: ConstrFun
isInteger = constrainOnVal $
    \case
       ConstVal x -> ceiling x == floor x
       _          -> True

-- check if the matched pattern is positive
isPositive :: ConstrFun
isPositive = constrainOnVal $
    \case
       ConstVal x -> x > 0
       _          -> True

-- check if the matched pattern is valid
isValid :: ConstrFun
isValid = constrainOnVal $
    \case
       ConstVal x -> not (isNaN x || isInfinite x)
       _          -> True

-- | e-class ids bound to a rest variable
restEidsOf :: Char -> Subst -> [EClassId]
restEidsOf c subst = case Map.lookup (Right (fromEnum c)) subst of
                       Just (SVMap m) -> expandedList m
                       _              -> []

-- | every e-class bound to a rest variable holds a valid value
allValidRest :: Char -> Condition
allValidRest c = Condition $ \subst -> do
    let eids = restEidsOf c subst
        validEid eid = getEClass eid >>= \ec ->
            pure $ case _consts . _info $ ec of
                     ConstVal x -> not (isNaN x || isInfinite x)
                     _          -> True
    and <$> mapM validEid eids

-- basic algebraic rules
rewriteBasic :: [Rule]
rewriteBasic =
    [
      -- B7/B8/C5: factor a common term out of a sum of products, and the
      -- reverse (distribute), which make x*(y+z) and x*y+x*z equivalent.
      NAry EAdd [ Ch (NAry EMul [Ch "x", Rest '1'])
                , Ch (NAry EMul [Ch "x", Rest '2'])
                , Rest '3' ]
        :=>
      NAry EAdd [ Ch (NAry EMul [ Ch "x"
                                , Ch (NAry EAdd [Rest '1', Rest '2'])
                                ])
                , Rest '3' ]
    , NAry EAdd [ Ch (NAry EMul [ Ch "x"
                                , Ch (NAry EAdd [Rest '1'])
                                ])
                , Rest '2' ]
        :=>
      NAry EAdd [ MapP (NAry EMul [Ch "x", Ch Hole]) '1'
                , Rest '2' ]
    -- C5: x*y - z*x = x*(y - z)
    , NAry EAdd [ Ch (NAry EMul [Ch "x", Rest '1'])
                , Ch (NAry EMul [Ch (Fixed (Const (-1))), Ch "x", Ch "z"])
                , Rest '3' ]
        :=>
      NAry EAdd [ Ch (NAry EMul [ Ch "x"
                                , Ch (NAry EAdd [Rest '1', Ch (negate (VarPat 'z'))])
                                ])
                , Rest '3' ]
    -- B1: group duplicate factors into a power (x*x = x^2)
    , NAry EMul [Ch "x", Ch "x"] :=> "x" ** 2
    -- C9: binomial expansion of a closed 2-ary square
    , ("x" + "y") ** 2 :=> "x" ** 2 + 2 * "x" * "y" + "y" ** 2
    -- C10: x^2 + x*y + ... = x*(x + y) + ...
    , NAry EAdd [ Ch (Fixed (Bin Power (VarPat 'x') (Fixed (Const 2))))
                , Ch (NAry EMul [Ch "x", Rest '1'])
                , Rest '2' ]
        :=>
      NAry EAdd [ Ch (NAry EMul [ Ch "x"
                                , Ch (NAry EAdd [Ch "x", Rest '1'])
                                ])
                , Rest '2' ]
    ]

-- rules for nonlinear functions 
rewritesFun :: [Rule]
rewritesFun =
    [
      log (exp "x")  :=> "x"
    -- C11: log(x*y*z*...) = log x + log y + ...
    , log (NAry EMul [Rest '1']) :=> NAry EAdd [MapP (Fixed (Uni Log Hole)) '1']
    , log ("x" ** "y") :=> "y" * log "x"
    , log (powabs "x" "y") :=> "y" * log (abs "x")
    -- C12: abs(x*y*z*...) = abs x * abs y * ...
    , abs (NAry EMul [Rest '1']) :=> NAry EMul [MapP (Fixed (Uni Abs Hole)) '1']
    , abs ("x" ** "y") :=> abs "x" ** "y"
    , recip (recip "x") :=> "x" :| isNotZero "x"
    -- C13: (x*y*z*...)^w = x^w * y^w * ...   [was disabled: combinatorial blowup on (x*x)^t; the multiset matcher + matchCap bound that]
    , (NAry EMul [Rest '1']) ** "z" :=> NAry EMul [MapP (Hole ** VarPat 'z') '1']
    , abs "x" ** "y" :=> "x" ** "y" :| isEven "y"
    -- C14: sqrt(x*x) = abs x
    , sqrt (NAry EMul [Ch "x", Ch "x"]) :=> abs "x"
    ]

-- Rules that reduces redundant parameters
constReduction :: [Rule]
constReduction =
    [
      -- B3: 0 + rest = rest
      NAry EAdd [Ch (Fixed (Const 0)), Rest '1'] :=> NAry EAdd [Rest '1']
    , "x" ** 1 :=> "x"
    , powabs "x" 1 :=> abs "x"

    -- B9: x^y * x^z = x^(y+z)
    , NAry EMul [Ch (Fixed (Bin Power (VarPat 'x') (VarPat 'y'))), Ch (Fixed (Bin Power (VarPat 'x') (VarPat 'z')))]
        :==:
      Fixed (Bin Power (VarPat 'x') (NAry EAdd [Ch (VarPat 'y'), Ch (VarPat 'z')]))
        :| isPositive "x"
    -- B10: |x|^y * |x|^z = |x|^(y+z)  (fixed: target used "y+x" instead of "y+z")
    , NAry EMul [Ch (Fixed (Bin PowerAbs (VarPat 'x') (VarPat 'y'))), Ch (Fixed (Bin PowerAbs (VarPat 'x') (VarPat 'z')))]
        :=>
      Fixed (Bin PowerAbs (VarPat 'x') (NAry EAdd [Ch (VarPat 'y'), Ch (VarPat 'z')]))
    -- B11: (x^y)^z = x^(y*z)
    , Fixed (Bin Power (Fixed (Bin Power (VarPat 'x') (VarPat 'y'))) (VarPat 'z'))
        :==:
      Fixed (Bin Power (VarPat 'x') (NAry EMul [Ch (VarPat 'y'), Ch (VarPat 'z')]))
        :| isPositive "x"
    , powabs (powabs "x" "y") "z" :=> powabs "x" ("y" * "z")
    ]

rewritesWithConstant :: [Rule]
rewritesWithConstant =
    [
      "x" - "x" :=> 0
    , "x" / "x" :=> 1 :| isNotZero "x"
    , "x" ** "y" * "x" :=> "x" ** ("y" + 1) :| isPositive "x"
    , 1 ** "x" :=> 1
    , powabs 1 "x" :=> 1
    , log (sqrt "x") :=> 0.5 * log "x" :| isNotParam "x"
    , "x" ** (1/2)   :==: sqrt "x"
    , powabs "x" (1/2) :=> sqrt (abs "x")
    , "x" ** (1/3) :==: Fixed (Uni Cbrt "x")
    -- B4: 0 * rest = 0 (provided every factor is valid)
    , NAry EMul [Ch (Fixed (Const 0)), Rest '1'] :=> 0 :| allValidRest '1'
    , 0 ** "x" :=> 0 :| isPositive "x"
    , powabs 0 "x" :=> 0
    -- n-ary cancellation: x + y - x = y
    , NAry EAdd [ Ch "a"
                , Ch (NAry EMul [ Ch (Fixed (Const (-1.0))), Ch "a" ])
                , Rest 'r' ]
        :=> NAry EAdd [Rest 'r']
    -- combining like terms: x + x = 2*x
    , NAry EAdd [ Ch "a", Ch "a", Rest 'r' ]
        :=> NAry EAdd [ Ch (2 * "a"), Rest 'r' ]
    ]
rewritesWithParam :: [Rule]
rewritesWithParam =
    [
      "x" - "x" :=> Fixed (Param 0)
    , "x" / "x" :=> Fixed (Param 0) :| isNotZero "x"
    , 1 ** "x" :=> Fixed (Param 0)
    , powabs 1 "x" :=> Fixed (Param 0)
    ]

rewritesSimple :: [Rule]
rewritesSimple = rewriteBasic <> constReduction <> rewritesFun
powabs l r = Fixed (Bin PowerAbs l r)

-- | default cost function for simplification
-- TODO:
-- num_params:
--   length:
--      terminal < nonterminal:
--        symbol comparison (constants, parameters, variables x0, x10, x2)
--          op priorities (+, -, *, inv_div, pow, abs, exp, log, log10, sqrt)
--            univariates
myCost :: SRTree Int -> Int
myCost (Var _)      = 1
myCost (Const _)    = 3
myCost (Param _)    = 3
myCost (Y _)        = 1
myCost (Bin op l r) = 2 + l + r
myCost (Uni _ t)    = 3 + t

-- all rewrite rules
rewrites :: [Rule]
rewrites = rewriteBasic <> constReduction <> rewritesFun <> rewritesWithConstant
rewritesParams :: [Rule]
rewritesParams = rewriteBasic <> constReduction <> rewritesFun <> rewritesWithParam

-- | simplify using the default parameters
simplifyEqSatDefault :: Fix SRTree -> Fix SRTree
simplifyEqSatDefault t = eqSat t rewrites myCost 30 `evalState` emptyGraphNoTrack

-- | simplifies with custom parameters
simplifyEqSat :: [Rule] -> CostFun -> Int -> Fix SRTree -> Fix SRTree
simplifyEqSat rwrts costFun it t = eqSat t rwrts costFun it `evalState` emptyGraph

-- | apply a single step of merge-only using default rules
applyMergeOnlyDftl :: ClassStore m => CostFun -> EGraphST m ()
applyMergeOnlyDftl costFun = applySingleMergeOnlyEqSat costFun rewrites
