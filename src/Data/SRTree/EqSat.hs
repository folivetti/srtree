{-# language DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language LambdaCase #-}
{-# language TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Data.SRTree.EqSat ( simplifyEqSat ) where

import Control.Applicative (liftA2)
import Control.Monad (unless)
import Data.AEq ( AEq((~==)) )
import Data.Eq.Deriving ( deriveEq1 )
import Data.Equality.Analysis ( Analysis(..) )
import Data.Equality.Graph ( EGraph, ClassId, Language, ENode(unNode), represent, merge, find, children, rebuild, emptyEGraph )
import Data.Equality.Graph.Lens hiding ((^.))
import Data.Equality.Graph.Lens qualified as L
import Data.Equality.Matching
import Data.Equality.Matching.Database ( Subst )
import Data.Equality.Saturation
import Data.Equality.Saturation.Scheduler ( BackoffScheduler(BackoffScheduler) )
import Data.Foldable qualified as F
import Data.IntMap.Strict qualified as IM
import Data.Maybe (isJust, isNothing)
import Data.Ord.Deriving ( deriveOrd1 )
import Data.SRTree hiding (Fix(..))
import Data.SRTree.Eval
import Data.SRTree.Recursion qualified as R
import Data.Set qualified as S
import Text.Show.Deriving ( deriveShow1 )
import Data.Function ((&))
import Data.Foldable ( toList )

import Debug.Trace ( traceShow )

deriving instance Foldable SRTree
deriving instance Traversable SRTree

deriveEq1 ''SRTree
deriveOrd1 ''SRTree
deriveShow1 ''SRTree

instance Num (Pattern SRTree) where
  l + r = NonVariablePattern $ Bin Add l r
  l - r = NonVariablePattern $ Bin Sub l r
  l * r = NonVariablePattern $ Bin Mul l r
  abs   = NonVariablePattern . Uni Abs

  negate t    = fromInteger (-1) * t
  signum _    = undefined
  fromInteger = NonVariablePattern . Const . fromInteger

instance Fractional (Pattern SRTree) where
    (/) a b      = NonVariablePattern $ Bin Div a b
    fromRational = NonVariablePattern . Const . fromRational

instance Floating (Pattern SRTree) where
  pi      = NonVariablePattern $ Const pi
  exp     = NonVariablePattern . Uni Exp
  log     = NonVariablePattern . Uni Log
  sqrt    = NonVariablePattern . Uni Sqrt
  sin     = NonVariablePattern . Uni Sin
  cos     = NonVariablePattern . Uni Cos
  tan     = NonVariablePattern . Uni Tan
  asin    = NonVariablePattern . Uni ASin
  acos    = NonVariablePattern . Uni ACos
  atan    = NonVariablePattern . Uni ATan
  sinh    = NonVariablePattern . Uni Sinh
  cosh    = NonVariablePattern . Uni Cosh
  tanh    = NonVariablePattern . Uni Tanh
  asinh   = NonVariablePattern . Uni ASinh
  acosh   = NonVariablePattern . Uni ACosh
  atanh   = NonVariablePattern . Uni ATanh

  l ** r      = NonVariablePattern (Bin Power l r)
  logBase l r = undefined


instance Analysis (Maybe Double) SRTree where
    -- type Domain SRTreeF = Maybe Double
    makeA = evalConstant -- ((\c -> egr L.^._class c._data) <$> e)

    joinA Nothing Nothing  = Nothing
    joinA (Just a) Nothing = Just a
    joinA Nothing (Just b) = Just b
    joinA (Just a) (Just b)
      | isNaN a || isInfinite a = Just a
      | isNaN b || isInfinite b = Just b
      | (abs (a-b) <= 1e-6 || a ~== b || (a == 0 && b == (-0)) || (a == (-0) && b == 0) ) = Just a
      | otherwise = (error $ "Merged non-equal constants!" <> show a <> " " <> show b <> " " <> show (a==b))

    modifyA cl eg0
      = case eg0 L.^._class cl._data of
          Nothing -> let ns = S.filter (null . children) $ eg0 L.^._class cl._nodes
                      in if S.null ns
                            then eg0
                            else let eg1 = eg0 & _class cl._nodes %~ S.filter (null . children)
                                 in traceShow (ns,eg0,eg1) eg1
          Just d  ->
                -- Add constant as e-node
            let (new_c, eg1) = represent (Fix (Const d)) eg0
                (rep, eg2)  = merge cl new_c eg1
                eg3 = eg2 & _class rep._nodes %~ S.filter (null . children)
                -- Prune all except leaf e-nodes
            in if isNaN d
                  then eg1 & _class new_c._nodes %~ S.filter (null .children)
                  else eg3

evalConstant :: SRTree (Maybe Double) -> Maybe Double
evalConstant = \case
    -- Exception: Negative exponent: BinOp Pow e1 e2 -> liftA2 (^) e1 (round <$> e2 :: Maybe Integer)
    Bin Div (Just 0) _   -> Just 0
    Bin Mul (Just 0) _   -> Just 0
    Bin Mul _ (Just 0)   -> Just 0 
    Bin Power _ (Just 0) -> Just 1

    Bin Div e1 e2 -> liftA2 (/) e1 e2 >>= check
    Bin Sub e1 e2 -> liftA2 (-) e1 e2 >>= check
    Bin Mul e1 e2 -> liftA2 (*) e1 e2 >>= check
    Bin Add e1 e2 -> liftA2 (+) e1 e2 >>= check
    Bin Power e1 e2 -> liftA2 (**) e1 e2 >>= check
    Uni f e1 -> e1 >>= check . evalFun f
    Var _ -> Nothing
    Const x -> Just x >>= check
    Param _ -> Nothing
  where
    check x = if isNaN x || isInfinite x then Nothing else Just x

cost :: CostFunction SRTree (Int, String)
cost = \case
  Const x       -> (5, show x)
  Var   v       -> (1, 'x':show v)
  Bin Add c1 c2 -> (fst c1 + fst c2 + 1, "Add" <> snd c1 <> snd c2)
  Bin Mul c1 c2 -> (fst c1 + fst c2 + 1, "Mul" <> snd c1 <> snd c2)
  Bin op c1 c2   -> (fst c1 + fst c2 + 3, show op <> snd c1 <> snd c2)
  Uni fun c       -> (2 * fst c + 1, show fun <> snd c)
  Param _       -> (5, "Param")

unsafeGetSubst :: Pattern SRTree -> Subst -> ClassId
unsafeGetSubst (NonVariablePattern _) _ = error "unsafeGetSubst: NonVariablePattern; expecting VariablePattern"
unsafeGetSubst (VariablePattern v) subst = case IM.lookup v subst of
      Nothing -> error "Searching for non existent bound var in conditional"
      Just class_id -> class_id

getValData v subst egr = egr L.^._class (unsafeGetSubst v subst)._data

all_not :: Double -> [Pattern SRTree] -> RewriteCondition (Maybe Double) SRTree
all_not val vs subst egr =
    all (\v -> (getValData v subst egr) /= Just val) vs

any_not_const :: [Pattern SRTree] -> RewriteCondition (Maybe Double) SRTree
any_not_const vs subst egr =
    any (\v -> (getValData v subst egr) == Nothing) vs
all_not_const :: [Pattern SRTree] -> RewriteCondition (Maybe Double) SRTree
all_not_const vs subst egr =
    all (\v -> (getValData v subst egr) == Nothing) vs

all_not_param :: [Pattern SRTree] -> RewriteCondition (Maybe Double) SRTree
all_not_param vs subst egr =
    all (\v -> (getValData v subst egr) == Nothing) vs

is_not_neg_const :: Pattern SRTree -> RewriteCondition (Maybe Double) SRTree
is_not_neg_const v subst egr =
    (fmap (>=0) ((getValData v subst egr)) == Just True)

is_not_neg_consts :: Pattern SRTree -> Pattern SRTree -> RewriteCondition (Maybe Double) SRTree
is_not_neg_consts v1 v2 subst egr =
    (fmap (>=0) ((getValData v1 subst egr)) == Just True) ||
    (fmap (>=0) ((getValData v2 subst egr)) == Just True) -- &&
   -- ((fmap (<0) (egr L.^._class (unsafeGetSubst v1 subst)._data) == Just True) -- &&
   --  (fmap (<0) (egr L.^._class (unsafeGetSubst v2 subst)._data) == Just True)
   -- )

is_negative :: Pattern SRTree -> RewriteCondition (Maybe Double) SRTree
is_negative v subst egr =
    fmap (<0) ((getValData v subst egr)) == Just True

is_const :: Pattern SRTree -> RewriteCondition (Maybe Double) SRTree
is_const v subst egr =
    case ((getValData v subst egr)) of
         Nothing -> False
         Just x  -> not (isNaN x) && not (isInfinite x)

is_not_const :: Pattern SRTree -> RewriteCondition (Maybe Double) SRTree
is_not_const v subst egr =
    isNothing ((getValData v subst egr))

is_not_nan :: Pattern SRTree -> RewriteCondition (Maybe Double) SRTree
is_not_nan v subst egr =
  case (getValData v subst egr) of
       Nothing -> True
       Just x  -> not (isNaN x) && not (isInfinite x)

has_no_term :: (Analysis a SRTree) => Pattern SRTree -> RewriteCondition a SRTree
has_no_term v subst egr =
    any (is_term . unNode) (egr L.^._class (unsafeGetSubst v subst)._nodes)
  where
    is_term = \case
                    Var _ -> True
                    Param _ -> True
                    Const _ -> True
                    _ -> False

is_param :: (Analysis a SRTree) => Pattern SRTree -> RewriteCondition a SRTree
is_param v subst egr =
    any (is_term . unNode) (egr L.^._class (unsafeGetSubst v subst)._nodes)
  where
    is_term = \case
                    Param _ -> True
                    _ -> False

any_no_param :: (Analysis a SRTree) => [Pattern SRTree] -> RewriteCondition a SRTree
any_no_param vs subst egr =
    any (\v -> any (is_term . unNode) (egr L.^._class (unsafeGetSubst v subst)._nodes)) vs
  where
    is_term = \case
                    Param _ -> False
                    _ -> True

is_not_same_var :: (Analysis a SRTree) => Pattern SRTree -> Pattern SRTree -> RewriteCondition a SRTree
is_not_same_var v1 v2 subst egr = find (unsafeGetSubst v1 subst) egr /= find (unsafeGetSubst v2 subst) egr

has_no_loop :: (Analysis a SRTree) => Pattern SRTree -> Pattern SRTree -> RewriteCondition a SRTree
has_no_loop v1 v2 subst egr =
    let cId1 = find (unsafeGetSubst v1 subst) egr 
        cId2 = find (unsafeGetSubst v2 subst) egr
        c1 = map canon $ getChildren cId1
        c2 = map canon $ getChildren cId2
        gc1 = concatMap (map canon . getChildren) c1
        gc2 = concatMap (map canon . getChildren) c2
    in null (filter (==cId1) (c2 <> gc2)) && null (filter (==cId2) (c1 <> gc1))
  where
    getChildren cid = concatMap children $ egr L.^._class cid . _nodes
    canon c = find c egr

not_too_high :: Pattern SRTree -> RewriteCondition (Maybe Double) SRTree
not_too_high v subst egr =
  let cId = find (unsafeGetSubst v subst) egr
   in getHeight 10 cId
  where
    --getTree cid = egr L.^._class cid
    --getChildren cid = concatMap children $ egr L.^._class cid . _nodes
    getParents c = filter (\ci -> canon ci /= canon c) $ toList $ fmap fst $ egr L.^._class c . _parents
    getSame    c = filter (\ci -> canon ci == canon c) $ toList $ fmap fst $ egr L.^._class c . _parents
    canon c = find c egr
    getHeight 0 c = False
    getHeight n c = let parents = getParents c
                        loop    = getSame c
                    in if null loop
                          then foldr (\ci acc -> acc && getHeight (n-1) (canon ci)) True parents
                          else False
                    {-
    getHeight  n cid
      | n >= 5    = False
      | otherwise = foldr (\c acc -> acc && getHeight (n+1) (canon c)) True (getChildren cid)
      -}
type ATree = Maybe Double

rewriteBasic1 :: [Rewrite ATree SRTree]
rewriteBasic1 = --fmap (:| all_not_const ["x"])
    [
      "x" * "x" := "x" ** 2
    ]

rewriteBasic2 :: [Rewrite ATree SRTree]
rewriteBasic2 = -- fmap (:| all_not_const ["x", "y"])
    [
      "x" * "y" := "y" * "x"
    , "x" + "y" := "y" + "x"
    , ("x" ** "y") * "x" := "x" ** ("y" + 1) :| is_const "y"
    , ("x" * "y") / "x" := "y"
    ]

rewriteBasic3 :: [Rewrite ATree SRTree]
rewriteBasic3 = -- fmap (:| all_not_const ["x", "y", "z"])
    --fmap (\p -> p :| not_too_high "x" :| not_too_high "y"  :| not_too_high "z")
    [
      ("x" ** "y") * ("x" ** "z") := "x" ** ("y" + "z") 
    , ("x" + "y") + "z" := "x" + ("y" + "z")
    , ("x" + "y") - "z" := "x" + ("y" - "z")
    , ("x" * "y") * "z" := "x" * ("y" * "z")
    , ("x" * "y") + ("x" * "z") := "x" * ("y" + "z")
    , "x" - ("y" + "z") := ("x" - "y") - "z"
    , "x" - ("y" - "z") := ("x" - "y") + "z"
    , ("x" * "y") / "z" := ("x" / "z") * "y"
    ]

rewriteBasic4 :: [Rewrite ATree SRTree]
rewriteBasic4 =
    [
      ("w" * "x") / ("z" * "y") := ("w" / "z") * ("x" / "y") :| is_const "w" :| is_const "z"
    ]

rewritesFun1 :: [Rewrite ATree SRTree]
rewritesFun1 = 
    [
      log (sqrt "x") := 0.5 * log "x"
    , log (exp "x")  := "x"
    , exp (log "x")  := "x"
    , "x" ** (1/2)   := sqrt "x" 
    ]

rewritesFun2 :: [Rewrite ATree SRTree]
rewritesFun2 = 
    [
      log ("x" * "y") := log "x" + log "y"
    , log ("x" / "y") := log "x" - log "y"
    , log ("x" ** "y") := "y" * log "x"
    , sqrt ("y" * "x") := sqrt "y" * sqrt "x"
    , sqrt ("y" / "x") := sqrt "y" / sqrt "x"
    , abs ("x" * "y") := abs "x" * abs "y"
    ]

rewritesFun3 :: [Rewrite ATree SRTree]
rewritesFun3 = 
    [
      sqrt ("z" * ("x" - "y")) := sqrt (negate "z") * sqrt ("y" - "x")
    , sqrt ("z" * ("x" + "y")) := sqrt "z" * sqrt ("x" + "y")
    ]

-- Rules that reduces redundant parameters
constReduction1 :: [Rewrite ATree SRTree]
constReduction1 = 
    [
      0 + "x" := "x"
    , "x" - 0 := "x"
    , 1 * "x" := "x"
    , 0 * "x" := 0
    , 0 / "x" := 0 :| all_not 0 ["x"]
    , "x" - "x" := 0
    , "x" / "x" := 1 :| all_not 0 ["x"]
    , "x" ** 1 := "x"
    , 0 ** "x" := 0
    , 1 ** "x" := 1
    , "x" * (1 / "x") := 1
    , 0 - "x" := negate "x"
    ]

constReduction2 :: [Rewrite ATree SRTree] 
constReduction2 =
    [
      "x" + negate "y" := "x" - "y"
    ]

rewritesBasic0 :: [Rewrite (Maybe Double) SRTree]
rewritesBasic0 =
    [ 
        "x" * "y" := "y" * "x" -- :| not_too_high "x" -- :| has_no_loop "x" "y" -- :| not_too_high "x" :| not_too_high "y"
      , ("x" * "y") * "z" := "x" * ("y" * "z") -- :| any_not_const ["x", "y", "z"] -- :| not_too_high "x" :| not_too_high "y" :| not_too_high "z"
      , "x" - "x" := 0
      , "x" * 0 := 0

    ]

rewrites = concat [rewriteBasic1, rewriteBasic2, rewriteBasic3, constReduction1, constReduction2]--, rewriteBasic4]
rewritesConst = concat [rewriteBasic1, rewriteBasic2, rewriteBasic3, rewriteBasic4, constReduction1, constReduction2] 

rewriteTree :: (Analysis a l, Language l, Ord cost) => [Rewrite a l] -> Int -> Int -> CostFunction l cost -> Fix l -> Fix l
rewriteTree rules n coolOff c t = fst $ equalitySaturation' (BackoffScheduler n coolOff) t rules c

rewriteAll, rewriteConst :: Fix SRTree -> Fix SRTree
--rewriteAll   = rewriteTree  (rewritesBasic <> constReduction <> rewritesFun) 2500 2 cost
rewriteAll   = rewriteTree  rewrites 100 0 cost
rewriteConst = rewriteTree rewritesConst 100 0 cost

rewriteUntilNoChange :: [Fix SRTree -> Fix SRTree] -> Int -> Fix SRTree -> Fix SRTree
rewriteUntilNoChange _ 0 t = t
rewriteUntilNoChange rs n t
  | t == t'   = t'
  | otherwise = rewriteUntilNoChange (tail rs <> [head rs]) (n-1) t'
  where t' = head rs t

simplifyEqSat :: R.Fix SRTree -> R.Fix SRTree
-- simplifyEqSat = relabelParams . fromEqFix . rewriteUntilNoChange [rewriteAll] 2 . rewriteConst . toEqFix
-- traceShow (represent (toEqFix t) emptyEGraph :: (ClassId, EGraph ATree SRTree)) $
simplifyEqSat t = (relabelParams . fromEqFix . rewriteAll . rewriteAll . rewriteAll . toEqFix) t
--simplifyEqSat = relabelParams . fromEqFix . rewriteConst . toEqFix

fromEqFix :: Fix SRTree -> R.Fix SRTree
fromEqFix = cata alg
  where
    alg (Const x) = R.Fix (Const x)
    alg (Var ix) = R.Fix (Var ix)
    alg (Param ix) = R.Fix (Param ix)
    alg (Bin op l r) = R.Fix (Bin op l r)
    alg (Uni f t) = R.Fix (Uni f t)

toEqFix :: R.Fix SRTree -> Fix SRTree
toEqFix = R.cata alg
  where
    alg (Const x) = Fix (Const x)
    alg (Var ix) = Fix (Var ix)
    alg (Param ix) = Fix (Param ix)
    alg (Bin op l r) = Fix (Bin op l r)
    alg (Uni f t) = Fix (Uni f t)
