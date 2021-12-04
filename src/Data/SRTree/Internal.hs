{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Internal 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Expression tree for Symbolic Regression
--
-----------------------------------------------------------------------------

module Data.SRTree.Internal 
         ( SRTree(..)
         , Function(..)
         , OptIntPow(..)
         , traverseIx
         , arity
         , getChildren
         , countNodes
         , countVarNodes
         , countOccurrences
         , deriveBy
         , simplify
         , derivative
         , evalFun
         , inverseFunc
         , evalTree
         , evalTreeMap
         , evalTreeWithMap
         , evalTreeWithVector
         , relabelOccurrences
         )
         where

import Data.Bifunctor

import Data.Map.Strict (Map(..), (!), (!?), insert, fromList)
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative hiding (Const)

-- | Tree structure to be used with Symbolic Regression algorithms.
-- This structure is parametrized by the indexing type to retrieve the values
-- of a variable and the type of the output value.
data SRTree ix val = 
   Empty 
 | Var ix
 | Const val
 | Fun Function (SRTree ix val)
 | Pow (SRTree ix val) Int
 | SRTree ix val `Add`     SRTree ix val
 | SRTree ix val `Sub`     SRTree ix val
 | SRTree ix val `Mul`     SRTree ix val
 | SRTree ix val `Div`     SRTree ix val
 | SRTree ix val `Power`   SRTree ix val
 | SRTree ix val `LogBase` SRTree ix val
     deriving (Show, Eq, Ord, Functor)

-- | Functions that can be applied to a subtree.
data Function = 
    Id 
  | Abs
  | Sin 
  | Cos 
  | Tan 
  | Sinh
  | Cosh
  | Tanh 
  | ASin 
  | ACos 
  | ATan
  | ASinh
  | ACosh 
  | ATanh 
  | Sqrt 
  | Square 
  | Log 
  | Exp 
     deriving (Show, Read, Eq, Ord, Enum)

-- | A class for optimized `(^^)` operators for specific types.
-- This was created because the integer power operator for
-- interval arithmetic must be aware of the dependency problem,
-- thus the default `(^)` doesn't work.
class OptIntPow a where
  (^.) :: a -> Int -> a
  infix 8 ^.
  
instance OptIntPow Double where
  (^.) = (^^)
  {-# INLINE (^.) #-}
instance OptIntPow Float where
  (^.) = (^^)
  {-# INLINE (^.) #-}
  
 
instance OptIntPow (SRTree ix val) where
  (^.) = Pow
  {-# INLINE (^.) #-}
   
instance (Eq ix, Eq val, Num val) => Num (SRTree ix val) where
  0 + r                   = r
  l + 0                   = l
  (Const c1) + (Const c2) = Const $ c1 + c2
  l + r                   = Add l r
  {-# INLINE (+) #-}

  0 - r                   = (-1) * r
  l - 0                   = l
  (Const c1) - (Const c2) = Const $ c1 - c2
  l - r                   = Sub l r
  {-# INLINE (-) #-}

  0 * r                   = 0
  l * 0                   = 0
  1 * r                   = r
  l * 1                   = l 
  (Const c1) * (Const c2) = Const $ c1 * c2
  l * r                   = Mul l r
  {-# INLINE (*) #-}
    
  abs         = Fun Abs
  {-# INLINE abs #-}
  
  signum t    = case t of
                  Const x -> Const $ signum x
                  _       -> Const 0
  fromInteger = Const . fromInteger
  {-# INLINE fromInteger #-}

instance (Eq ix, Eq val, Fractional val) => Fractional (SRTree ix val) where
  0 / r                   = 0
  l / 1                   = l
  (Const c1) / (Const c2) = Const $ c1/c2
  l / r                   = Div l r
  {-# INLINE (/) #-}
  
  fromRational = Const . fromRational
  {-# INLINE fromRational #-}
  
instance (Eq ix, Eq val, Floating val) => Floating (SRTree ix val) where  
  pi      = Const  pi
  {-# INLINE pi #-}
  exp     = evalToConst . Fun Exp
  {-# INLINE exp #-}
  log     = evalToConst . Fun Log
  {-# INLINE log #-}
  sqrt    = evalToConst . Fun Sqrt
  {-# INLINE sqrt #-}
  sin     = evalToConst . Fun Sin
  {-# INLINE sin #-}
  cos     = evalToConst . Fun Cos
  {-# INLINE cos #-}
  tan     = evalToConst . Fun Tan
  {-# INLINE tan #-}
  asin    = evalToConst . Fun ASin
  {-# INLINE asin #-}
  acos    = evalToConst . Fun ACos
  {-# INLINE acos #-}
  atan    = evalToConst . Fun ATan
  {-# INLINE atan #-}
  sinh    = evalToConst . Fun Sinh
  {-# INLINE sinh #-}
  cosh    = evalToConst . Fun Cosh
  {-# INLINE cosh #-}
  tanh    = evalToConst . Fun Tanh
  {-# INLINE tanh #-}
  asinh   = evalToConst . Fun ASinh
  {-# INLINE asinh #-}
  acosh   = evalToConst . Fun ACosh
  {-# INLINE acosh #-}
  atanh   = evalToConst . Fun ATanh
  {-# INLINE atanh #-}

  0 ** r  = 0
  1 ** r  = 1
  l ** 0  = 1
  l ** 1  = l
  l ** r  = evalToConst $ Power l r
  {-# INLINE (**) #-}

  logBase 1 r = 0
  logBase l r = evalToConst $ LogBase l r
  {-# INLINE logBase #-}

instance Bifunctor SRTree where
  first f Empty         = Empty
  first f (Var ix)      = Var $ f ix
  first f (Fun g t)     = Fun g $ first f t
  first f (Pow t k)     = Pow (first f t) k
  first f (Add l r)     = Add (first f l) (first f r)
  first f (Sub l r)     = Sub (first f l) (first f r)
  first f (Mul l r)     = Mul (first f l) (first f r)
  first f (Div l r)     = Div (first f l) (first f r)
  first f (Power l r)   = Power (first f l) (first f r)
  first f (LogBase l r) = LogBase (first f l) (first f r)
  {-# INLINE first #-}
  
  second                = fmap
  {-# INLINE second #-}

instance Applicative (SRTree ix) where
  pure = Const

  Empty         <*> t = Empty
  Var ix        <*> t = Var ix
  Const f       <*> t = fmap f t
  Fun g tf      <*> t = Fun g $ tf <*> t
  Pow tf k      <*> t = Pow (tf <*> t) k
  Add lf rf     <*> t = Add (lf <*> t) (rf <*> t)
  Sub lf rf     <*> t = Sub (lf <*> t) (rf <*> t)
  Mul lf rf     <*> t = Mul (lf <*> t) (rf <*> t)
  Div lf rf     <*> t = Div (lf <*> t) (rf <*> t)
  Power lf rf   <*> t = Power (lf <*> t) (rf <*> t)
  LogBase lf rf <*> t = LogBase (lf <*> t) (rf <*> t)
 
instance Foldable (SRTree ix) where
  foldMap f Empty     = mempty
  foldMap f (Var ix)  = mempty
  foldMap f (Const c) = f c
  foldMap f t         = mconcat $ map (foldMap f) $ getChildren t

instance Traversable (SRTree ix) where
  traverse mf Empty         = pure Empty
  traverse mf (Var ix)      = pure $ Var ix
  traverse mf (Const c)     = Const <$> mf c
  traverse mf (Fun g t)     = Fun g <$> traverse mf t
  traverse mf (Pow t k)     = (`Pow` k) <$> traverse mf t
  traverse mf (Add l r)     = Add <$> traverse mf l <*> traverse mf r
  traverse mf (Sub l r)     = Sub <$> traverse mf l <*> traverse mf r
  traverse mf (Mul l r)     = Mul <$> traverse mf l <*> traverse mf r
  traverse mf (Div l r)     = Div <$> traverse mf l <*> traverse mf r
  traverse mf (Power l r)   = Power <$> traverse mf l <*> traverse mf r
  traverse mf (LogBase l r) = LogBase <$> traverse mf l <*> traverse mf r

-- | Same as `traverse` but for the first type parameter.
traverseIx :: Applicative f => (ixa -> f ixb) -> SRTree ixa val -> f (SRTree ixb val)
traverseIx mf Empty         = pure Empty
traverseIx mf (Var ix)      = Var <$> mf ix
traverseIx mf (Const c)     = pure $ Const c
traverseIx mf (Fun g t)     = Fun g <$> traverseIx mf t
traverseIx mf (Pow t k)     = (`Pow` k) <$> traverseIx mf t
traverseIx mf (Add l r)     = Add <$> traverseIx mf l <*> traverseIx mf r
traverseIx mf (Sub l r)     = Sub <$> traverseIx mf l <*> traverseIx mf r
traverseIx mf (Mul l r)     = Mul <$> traverseIx mf l <*> traverseIx mf r
traverseIx mf (Div l r)     = Div <$> traverseIx mf l <*> traverseIx mf r
traverseIx mf (Power l r)   = Power <$> traverseIx mf l <*> traverseIx mf r
traverseIx mf (LogBase l r) = LogBase <$> traverseIx mf l <*> traverseIx mf r

-- | Arity of the current node
arity :: SRTree ix val -> Int
arity Empty     = 0
arity (Var _)   = 0
arity (Const _) = 0
arity (Fun _ _) = 1
arity (Pow _ _) = 1
arity _         = 2
{-# INLINE arity #-}

-- | Get the children of a node. Returns an empty list in case of a leaf node.
getChildren :: SRTree ix val -> [SRTree ix val]
getChildren Empty         = []
getChildren (Var _)       = []
getChildren (Const _)     = []
getChildren (Fun _ t)     = [t]
getChildren (Pow t _)     = [t]
getChildren (Add l r)     = [l, r]
getChildren (Sub l r)     = [l, r]
getChildren (Mul l r)     = [l, r]
getChildren (Div l r)     = [l, r]
getChildren (Power l r)   = [l, r]
getChildren (LogBase l r) = [l, r]
{-# INLINE getChildren #-}

-- Support function to simplify operations applied to const subtrees.
evalToConst :: Floating val => SRTree ix val -> SRTree ix val  
evalToConst (Fun g (Const c))               = Const $ evalFun g c
evalToConst (Power (Const c1) (Const c2))   = Const $ c1**c2
evalToConst (LogBase (Const c1) (Const c2)) = Const $ logBase c1 c2
evalToConst t                               = t
{-# INLINE evalToConst #-}

-- Support function to sum the types of nodes specified by `f`.
sumCounts :: (SRTree ix val -> Int) -> Int -> SRTree ix val -> Int
sumCounts f val = foldr (\c v -> f c + v) val . getChildren
{-# INLINE sumCounts #-}

-- | Count the number of nodes in a tree.
countNodes :: SRTree ix val -> Int
countNodes Empty = 0
countNodes t     = sumCounts countNodes 1 t
{-# INLINE countNodes #-}

-- | Count the number of `Var` nodes
countVarNodes :: SRTree ix val -> Int
countVarNodes (Var _) = 1
countVarNodes t       = sumCounts countVarNodes 0 t
{-# INLINE countVarNodes #-}

-- | Count the occurrences of variable indexed as `ix`
countOccurrences :: Eq ix => SRTree ix val -> ix -> Int
countOccurrences (Var ix) iy = if ix==iy then 1 else 0
countOccurrences t        iy = sumCounts (`countOccurrences` iy) 0 t
{-# INLINE countOccurrences #-}

-- | Creates an `SRTree` representing the partial derivative of the input by the variable indexed by `ix`.
deriveBy :: (Eq ix, Eq val, Floating val) => ix -> SRTree ix val -> SRTree ix val
deriveBy _  Empty    = Empty
deriveBy dx (Var ix)
  | dx == ix  = 1
  | otherwise = 0
deriveBy dx (Const val) = 0
deriveBy dx (Fun g t)   =
  case deriveBy dx t of
    0  -> 0
    1  -> derivative g t
    t' -> derivative g t * t'
deriveBy dx (Pow t 0)   = 0    
deriveBy dx (Pow t 1)   = deriveBy dx t
deriveBy dx (Pow t k)   = 
  case deriveBy dx t of
    0 -> 0
    Const val -> Const (val * fromIntegral k) * (t ^. (k-1))
    t'        -> fromIntegral k * (t ^. (k-1)) * t'
deriveBy dx (Add l r)     = deriveBy dx l + deriveBy dx r
deriveBy dx (Sub l r)     = deriveBy dx l - deriveBy dx r
deriveBy dx (Mul l r)     = deriveBy dx l * r + l * deriveBy dx r
deriveBy dx (Div l r)     = (deriveBy dx l * r - l * deriveBy dx r) / r ^. 2
deriveBy dx (Power l r)   = l ** (r-1) * (r * deriveBy dx l + l * log l * deriveBy dx r)
deriveBy dx (LogBase l r) = deriveBy dx (log l / log r)

-- | Simplifies the `SRTree`.
simplify :: (Eq ix, Eq val, Floating val, OptIntPow val) => SRTree ix val -> SRTree ix val
simplify (Fun g t) = evalToConst . Fun g $ simplify t
simplify (Pow t 0) = 1    
simplify (Pow t 1) = simplify t
simplify (Pow t k) =
  case simplify t of
    Const c -> Const $ c ^. k
    t'      -> Pow t' k
    
simplify (Add l r)     = simplify l + simplify r
simplify (Sub l r)     = simplify l - simplify r
simplify (Mul l r)     = simplify l * simplify r
simplify (Div l r)     = simplify l / simplify r
simplify (Power l r)   = simplify l ** simplify r
simplify (LogBase l r) = logBase (simplify l) (simplify r)
simplify t             = t

-- | Derivative of a Function
derivative :: (Eq ix, Eq val, Floating val) => Function -> SRTree ix val -> SRTree ix val
derivative Id      = const 1
derivative Abs     = \x -> x / abs x
derivative Sin     = cos
derivative Cos     = negate.sin
derivative Tan     = recip . (**2.0) . cos
derivative Sinh    = cosh
derivative Cosh    = sinh
derivative Tanh    = (1-) . (**2.0) . tanh
derivative ASin    = recip . sqrt . (1-) . (^2)
derivative ACos    = negate . recip . sqrt . (1-) . (^2)
derivative ATan    = recip . (1+) . (^2)
derivative ASinh   = recip . sqrt . (1+) . (^2)
derivative ACosh   = \x -> 1 / (sqrt (x-1) * sqrt (x+1))
derivative ATanh   = recip . (1-) . (^2)
derivative Sqrt    = recip . (2*) . sqrt
derivative Square  = (2*)
derivative Exp     = exp
derivative Log     = recip
{-# INLINE derivative #-}

-- | Evaluates a function.
evalFun :: Floating val => Function -> val -> val
evalFun Id      = id
evalFun Abs     = abs
evalFun Sin     = sin
evalFun Cos     = cos
evalFun Tan     = tan
evalFun Sinh    = sinh
evalFun Cosh    = cosh
evalFun Tanh    = tanh
evalFun ASin    = asin
evalFun ACos    = acos
evalFun ATan    = atan
evalFun ASinh   = asinh
evalFun ACosh   = acosh
evalFun ATanh   = atanh
evalFun Sqrt    = sqrt
evalFun Square  = (^2)
evalFun Exp     = exp
evalFun Log     = log
{-# INLINE evalFun #-}

-- | Returns the inverse of a function. This is a partial function.
inverseFunc :: Function -> Function
inverseFunc Id     = Id
inverseFunc Sin    = ASin
inverseFunc Cos    = ACos
inverseFunc Tan    = ATan
inverseFunc Tanh   = ATanh
inverseFunc ASin   = Sin
inverseFunc ACos   = Cos
inverseFunc ATan   = Tan
inverseFunc ATanh  = Tanh
inverseFunc Sqrt   = Square
inverseFunc Square = Sqrt
inverseFunc Log    = Exp
inverseFunc Exp    = Log
inverseFunc x      = error $ show x ++ " has no support for inverse function"
{-# INLINE inverseFunc #-}

-- | Evaluates a tree with the variables stored in a `Reader` monad.
evalTree :: (Floating val, OptIntPow val) => SRTree ix val -> Reader (ix -> Maybe val) (Maybe val)
evalTree Empty         = pure Nothing
evalTree (Const c)     = pure $ Just c
evalTree (Var ix)      = askAbout ix
evalTree (Fun f t)     = evalFun f <$$> evalTree t
evalTree (Pow t k)     = (^. k) <$$> evalTree t
evalTree (Add l r)     = (+)  <$*> evalTree l <*> evalTree r
evalTree (Sub l r)     = (-)  <$*> evalTree l <*> evalTree r
evalTree (Mul l r)     = (*)  <$*> evalTree l <*> evalTree r
evalTree (Div l r)     = (/)  <$*> evalTree l <*> evalTree r
evalTree (Power l r)   = (**) <$*> evalTree l <*> evalTree r
evalTree (LogBase l r) = logBase <$*> evalTree l <*> evalTree r

-- | Evaluates a tree with the variables stored in a `Reader` monad while mapping the constant 
-- values to a different type.
evalTreeMap :: (Floating v1, OptIntPow v1, Floating v2, OptIntPow v2) => (v1 -> v2) -> SRTree ix v1 -> Reader (ix -> Maybe v2) (Maybe v2)
evalTreeMap f Empty         = pure Nothing
evalTreeMap f (Const c)     = pure $ Just $ f c
evalTreeMap f (Var ix)      = askAbout ix
evalTreeMap f (Fun g t)     = evalFun g <$$> evalTreeMap f t
evalTreeMap f (Pow t k)     = (^. k) <$$> evalTreeMap f t
evalTreeMap f (Add l r)     = (+)  <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (Sub l r)     = (-)  <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (Mul l r)     = (*)  <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (Div l r)     = (/)  <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (Power l r)   = (**) <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (LogBase l r) = logBase <$*> evalTreeMap f l <*> evalTreeMap f r

-- lift functions inside nested applicatives.
(<$$>) :: (Applicative f, Applicative g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) = fmap . fmap
{-# INLINE (<$$>) #-}
(<$*>) :: (Applicative f, Applicative g) => (a -> b -> c) -> f (g a) -> f (g b -> g c)
op <$*> m = liftA2 op <$> m
{-# INLINE (<$*>) #-}

-- applies the argument `x` in the function carried by the `Reader` monad.
askAbout :: x -> Reader (x -> a) a
askAbout x = asks ($ x)
{-# INLINE askAbout #-}

-- | Example of using `evalTree` with a Map.
evalTreeWithMap :: (Ord ix, Floating val, OptIntPow val) => SRTree ix val -> Map ix val -> Maybe val
evalTreeWithMap t m = runReader (evalTree t) (m !?)
{-# INLINE evalTreeWithMap #-}

-- | Example of using `evalTree` with a Vector.
evalTreeWithVector :: (Floating val, OptIntPow val) => SRTree Int val -> V.Vector val -> Maybe val
evalTreeWithVector t v = runReader (evalTree t) (v V.!?)
{-# INLINE evalTreeWithVector #-}

-- | Relabel occurences of a var into a tuple (ix, Int).
relabelOccurrences :: forall ix val . Ord ix => SRTree ix val -> SRTree (ix, Int) val
relabelOccurrences t = traverseIx updVar t `evalState` M.empty 
  where
    updVar :: ix -> State (Map ix Int) (ix, Int)
    updVar ix = do
      s <- get
      case s !? ix of
        Nothing -> do put $ insert ix 0 s
                      pure (ix, 0)
        Just c  -> do put $ insert ix (c+1) s
                      pure (ix, c+1)
