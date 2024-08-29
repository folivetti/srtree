{-# LANGUAGE OverloadedStrings #-}
module Data.SRTree.Simplify ( simplifyEqSatDefault ) where

import Data.SRTree 
import Data.SRTree.Egraph
import Control.Monad.State.Lazy
import Data.SRTree.EqSatDB
import Data.SRTree.EqSat1

import Data.Map ( Map )
import Data.IntMap ( IntMap )
import qualified Data.Map as Map
import qualified Data.IntMap as IM

isConstPt :: Pattern -> Map.Map ClassOrVar ClassOrVar -> EGraph -> Bool
isConstPt (VarPat c) subst eg =
    let cid = getInt $ subst Map.! (Right $ fromEnum c)
    in case (_consts . _info) (_eClass eg IM.! cid) of
         ConstVal x -> True
         _ -> False
isConstPt _ _ _ = False

isConstPos :: Pattern -> Map.Map ClassOrVar ClassOrVar -> EGraph -> Bool
isConstPos (VarPat c) subst eg =
    let cid = getInt $ subst Map.! (Right $ fromEnum c)
    in case (_consts . _info) (_eClass eg IM.! cid) of
         ConstVal x -> x > 0
         _ -> False
isConstPos _ _ _ = False

isNotZero :: Pattern -> Map.Map ClassOrVar ClassOrVar -> EGraph -> Bool
isNotZero (VarPat c) subst eg =
    let cid = getInt $ subst Map.! (Right $ fromEnum c)
    in case (_consts . _info) (_eClass eg IM.! cid) of
         ConstVal x -> abs x < 1e-9
         _ -> True
isNotZero _ _ _ = True

notZero (VarPat c) subst eg =
  let cid = getInt $ subst Map.! (Right $ fromEnum c)
   in case (_consts . _info) (_eClass eg IM.! cid) of
         ConstVal x -> x /= 0
         _ -> True
notZero _ _ _ = True

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
    , ("w" * "x") / ("z" * "y") :=> ("w" / "z") * ("x" / "y") :| isConstPt "w" :| isConstPt "z" :| isNotZero "z"
    , (("x" * "y") + ("z" * "w")) :=> "x" * ("y" + ("z" / "x") * "w") :| isConstPt "x" :| isConstPt "z" :| isNotZero "x"
    , (("x" * "y") - ("z" * "w")) :=> "x" * ("y" - ("z" / "x") * "w") :| isConstPt "x" :| isConstPt "z" :| isNotZero "x"
    , (("x" * "y") * ("z" * "w")) :=> ("x" * "z") * ("y" * "w") :| isConstPt "x" :| isConstPt "z"
    ]

rewritesFun =
    [
      log (sqrt "x") :=> 0.5 * log "x"
    , log (exp "x")  :=> "x"
    , exp (log "x")  :=> "x"
    , "x" ** (1/2)   :=> sqrt "x"
    , log ("x" * "y") :=> log "x" + log "y" :| isConstPos "x"
    , log ("x" / "y") :=> log "x" - log "y" :| isConstPos "x"
    , log ("x" ** "y") :=> "y" * log "x"
    , sqrt ("y" * "x") :=> sqrt "y" * sqrt "x"
    , sqrt ("y" / "x") :=> sqrt "y" / sqrt "x"
    , abs ("x" * "y") :=> abs "x" * abs "y" :| isConstPt "x"
    , sqrt ("z" * ("x" - "y")) :=> sqrt (negate "z") * sqrt ("y" - "x")
    , sqrt ("z" * ("x" + "y")) :=> sqrt "z" * sqrt ("x" + "y")
    ]

-- Rules that reduces redundant parameters
constReduction =
    [
      0 + "x" :=> "x"
    , "x" - 0 :=> "x"
    , 1 * "x" :=> "x"
    , 0 * "x" :=> 0
    , 0 / "x" :=> 0 :| notZero "x"
    , "x" - "x" :=> 0
    , "x" / "x" :=> 1 :| notZero "x"
    , "x" ** 1 :=> "x"
    , 0 ** "x" :=> 0
    , 1 ** "x" :=> 1
    , "x" * (1 / "x") :=> 1
    , 0 - "x" :=> negate "x"
    , "x" + negate "y" :=> "x" - "y"
    , negate ("x" * "y") :=> (negate "x") * "y" :| isConstPt "x"
    ]

myCost :: SRTree Int -> Int
myCost (Var _) = 1
myCost (Const _) = 1
myCost (Param _) = 1
myCost (Bin op l r) = 2 + l + r
myCost (Uni _ t) = 3 + t

rewrites = rewriteBasic <> constReduction <> rewritesFun

simplifyEqSatDefault :: Fix SRTree -> Fix SRTree
simplifyEqSatDefault t = eqSat t rewrites myCost 30 `evalState` emptyGraph
