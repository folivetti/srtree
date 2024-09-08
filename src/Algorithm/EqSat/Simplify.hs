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
module Algorithm.EqSat.Simplify ( simplifyEqSatDefault, applyMergeOnlyDftl ) where

import Algorithm.EqSat (eqSat, applySingleMergeOnlyEqSat)
import Algorithm.EqSat.Egraph
import Algorithm.EqSat.EqSatDB
  ( ClassOrVar,
    Pattern (VarPat),
    Rule ((:=>), (:|)),
    getInt,
  )
import Control.Monad.State.Lazy (evalState)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Map (Map)
import qualified Data.Map as Map
import Data.SRTree

type ConstrFun = Pattern -> Map ClassOrVar ClassOrVar -> EGraph -> Bool 

constrainOnVal :: (Consts -> Bool) -> Pattern -> Map ClassOrVar ClassOrVar -> EGraph -> Bool 
constrainOnVal f (VarPat c) subst eg =
    let cid = getInt $ subst Map.! Right (fromEnum c)
     in f (_consts . _info $ _eClass eg IM.! cid)
constrainOnVal _ _ _ _ = False 

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
       ConstVal x -> abs x < 1e-9
       _          -> True

-- check if the matched pattern is even 
isEven :: ConstrFun
isEven = constrainOnVal $
    \case
       ConstVal x -> ceiling x == floor x && even (round x) 
       _          -> True

-- basic algebraic rules 
rewriteBasic :: [Rule]
rewriteBasic =
    [
      "x" * "x" :=> "x" ** 2
    , "x" * "y" :=> "y" * "x"
    , "x" + "y" :=> "y" + "x"
    , ("x" ** "y") * "x" :=> "x" ** ("y" + 1) :| isConstPt "y"
    , ("x" ** "y") * ("x" ** "z") :=> "x" ** ("y" + "z")
    , ("x" + "y") + "z" :=> "x" + ("y" + "z")
    , ("x" + "y") - "z" :=> "x" + ("y" - "z")
    , ("x" * "y") * "z" :=> "x" * ("y" * "z")
    , ("x" * "y") + ("x" * "z") :=> "x" * ("y" + "z")
    , "x" - ("y" + "z") :=> ("x" - "y") - "z"
    , "x" - ("y" - "z") :=> ("x" - "y") + "z"
    , ("x" * "y") / "z" :=> ("x" / "z") * "y" :| isNotZero "z"
    , "x" * ("y" / "z") :=> ("x" / "z") * "y" :| isNotZero "z"
    , "x" / ("y" * "z") :=> ("x" / "z") / "y" :| isNotZero "z"
    , ("w" * "x") + ("z" * "x") :=> ("w" + "z") * "x" :| isConstPt "w" :| isConstPt "z"
    , ("w" * "x") - ("z" * "x") :=> ("w" - "z") * "x" :| isConstPt "w" :| isConstPt "z"
    , ("w" * "x") / ("z" * "y") :=> ("w" / "z") * ("x" / "y") :| isConstPt "w" :| isConstPt "z" :| isNotZero "z"
    , (("x" * "y") + ("z" * "w")) :=> "x" * ("y" + ("z" / "x") * "w") :| isConstPt "x" :| isConstPt "z" :| isNotZero "x"
    , (("x" * "y") - ("z" * "w")) :=> "x" * ("y" - ("z" / "x") * "w") :| isConstPt "x" :| isConstPt "z" :| isNotZero "x"
    , (("x" * "y") * ("z" * "w")) :=> ("x" * "z") * ("y" * "w") :| isConstPt "x" :| isConstPt "z"
    ]

-- rules for nonlinear functions 
rewritesFun :: [Rule]
rewritesFun =
    [
      log (sqrt "x") :=> 0.5 * log "x" :| isNotParam "x"
    , log (exp "x")  :=> "x"
    , exp (log "x")  :=> "x"
    , "x" ** (1/2)   :=> sqrt "x"
    , log ("x" * "y") :=> log "x" + log "y" :| isConstPos "x"
    , log ("x" / "y") :=> log "x" - log "y" :| isConstPos "x"
    , log ("x" ** "y") :=> "y" * log "x"
    , sqrt ("x" ** "y") :=> "x" ** ("y" / 2) :| isEven "y"
    , sqrt ("y" * "x") :=> sqrt "y" * sqrt "x"
    , sqrt ("y" / "x") :=> sqrt "y" / sqrt "x"
    , abs ("x" * "y") :=> abs "x" * abs "y" :| isConstPt "x"
    , sqrt ("z" * ("x" - "y")) :=> sqrt (negate "z") * sqrt ("y" - "x")
    , sqrt ("z" * ("x" + "y")) :=> sqrt "z" * sqrt ("x" + "y")
    ]

-- Rules that reduces redundant parameters
constReduction :: [Rule]
constReduction =
    [
      0 + "x" :=> "x"
    , "x" - 0 :=> "x"
    , 1 * "x" :=> "x"
    , 0 * "x" :=> 0 :| isNotParam "x"
    , 0 / "x" :=> 0 :| isNotZero "x"
    , "x" - "x" :=> 0 :| isNotParam "x"
    , "x" / "x" :=> 1 :| isNotZero "x" :| isNotParam "x"
    , "x" ** 1 :=> "x"
    , 0 ** "x" :=> 0
    , 1 ** "x" :=> 1
    , "x" * (1 / "x") :=> 1 :| isNotParam "x" :| isNotZero "x"
    , 0 - "x" :=> negate "x"
    , "x" + negate "y" :=> "x" - "y"
    , negate ("x" * "y") :=> (negate "x") * "y" :| isConstPt "x"
    ]

-- | default cost function for simplification
myCost :: SRTree Int -> Int
myCost (Var _) = 1
myCost (Const _) = 1
myCost (Param _) = 1
myCost (Bin op l r) = 2 + l + r
myCost (Uni _ t) = 3 + t

-- all rewrite rules
rewrites :: [Rule]
rewrites = rewriteBasic <> constReduction <> rewritesFun

-- | simplify using the default parameters 
simplifyEqSatDefault :: Fix SRTree -> Fix SRTree
simplifyEqSatDefault t = eqSat t rewrites myCost 30 `evalState` emptyGraph

-- | simplifies with custom parameters
simplifyEqSat :: [Rule] -> CostFun -> Int -> Fix SRTree -> Fix SRTree
simplifyEqSat rwrts costFun it t = eqSat t rwrts costFun it `evalState` emptyGraph

-- | apply a single step of merge-only using default rules
applyMergeOnlyDftl :: Monad m => CostFun -> EGraphST m ()
applyMergeOnlyDftl costFun = applySingleMergeOnlyEqSat costFun rewrites
