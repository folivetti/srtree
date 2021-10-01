{-# language FlexibleInstances, DeriveFunctor #-}
module Tree where

import Data.Bifunctor
import Numeric.Interval ((|^^|),Interval(..))

-- | Expression tree
data Tree ix val = 
   Empty 
 | Var ix
 | Const val
 | Fun Function (Tree ix val)
 | Pow (Tree ix val) Int
 | Tree ix val `Add`     Tree ix val
 | Tree ix val `Sub`     Tree ix val
 | Tree ix val `Mul`     Tree ix val
 | Tree ix val `Div`     Tree ix val
 | Tree ix val `Power`   Tree ix val
 | Tree ix val `LogBase` Tree ix val
     deriving (Show, Eq, Ord, Functor)

-- | Transformation Functions 
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

class OptIntPow a where
  (^.) :: a -> Int -> a
  
instance OptIntPow Double where
  (^.) = (^^)
instance OptIntPow Float where
  (^.) = (^^)
instance (Ord a, Floating a) => OptIntPow (Interval a) where
  (^.) = (|^^|)
  
instance (Eq ix, Eq val, Num val) => Num (Tree ix val) where
  0 + r                   = r
  l + 0                   = l
  (Const c1) + (Const c2) = Const $ c1 + c2
  l + r                   = Add l r

  0 - r                   = (-1) * r
  l - 0                   = l
  (Const c1) - (Const c2) = Const $ c1 - c2
  l - r                   = Sub l r

  0 * r                   = 0
  l * 0                   = 0
  1 * r                   = r
  l * 1                   = l 
  (Const c1) * (Const c2) = Const $ c1 * c2
  l * r                   = Mul l r
    
  abs         = Fun Abs
  signum t    = case t of
                  Const x -> Const $ signum x
                  _       -> Const 0
  fromInteger = Const . fromInteger

instance (Eq ix, Eq val, Fractional val) => Fractional (Tree ix val) where
  0 / r                   = 0
  l / 1                   = l
  (Const c1) / (Const c2) = Const $ c1/c2
  l / r                   = Div l r
  fromRational = Const . fromRational
  
instance (Eq ix, Eq val, Floating val) => Floating (Tree ix val) where  
  pi      = Const  pi
  exp     = evalToConst . Fun Exp
  log     = evalToConst . Fun Log
  sqrt    = evalToConst . Fun Sqrt
  sin     = evalToConst . Fun Sin
  cos     = evalToConst . Fun Cos
  tan     = evalToConst . Fun Tan
  asin    = evalToConst . Fun ASin
  acos    = evalToConst . Fun ACos
  atan    = evalToConst . Fun ATan
  sinh    = evalToConst . Fun Sinh
  cosh    = evalToConst . Fun Cosh
  tanh    = evalToConst . Fun Tanh
  asinh   = evalToConst . Fun ASinh
  acosh   = evalToConst . Fun ACosh
  atanh   = evalToConst . Fun ATanh

  0 ** r  = 0
  1 ** r  = 1
  l ** 0  = 1
  l ** 1  = l
  l ** r  = evalToConst $ Power l r

  logBase 1 r = 0
  logBase l r = evalToConst $ LogBase l r

instance Bifunctor Tree where
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
  
  second                = fmap

instance Applicative (Tree ix) where
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
 
instance Foldable (Tree ix) where
  foldMap f Empty     = mempty
  foldMap f (Var ix)  = mempty
  foldMap f (Const c) = f c
  foldMap f t         = mconcat $ map (foldMap f) $ getChildren t

instance Traversable (Tree ix) where
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

traverseIx :: Applicative f => (ixa -> f ixb) -> Tree ixa val -> f (Tree ixb val)
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

-- | arity of the current node
arity :: Tree ix val -> Int
arity Empty     = 0
arity (Var _)   = 0
arity (Const _) = 0
arity (Fun _ _) = 1
arity (Pow _ _) = 1
arity _         = 2

-- | get the children of a node
getChildren :: Tree ix val -> [Tree ix val]
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
  
evalToConst :: Floating val => Tree ix val -> Tree ix val  
evalToConst (Fun g (Const c))               = Const $ evalFun g c
evalToConst (Power (Const c1) (Const c2))   = Const $ c1**c2
evalToConst (LogBase (Const c1) (Const c2)) = Const $ logBase c1 c2
evalToConst t                               = t
  
(***) :: Tree ix val -> Int -> Tree ix val
(***) = Pow
infixr 8 ***

sumCountsTree :: (Tree ix val -> Int) -> Int -> Tree ix val -> Int
sumCountsTree f val = foldr (\c v -> f c + v) val . getChildren

countNodes :: Tree ix val -> Int
countNodes Empty = 0
countNodes t     = sumCountsTree countNodes 1 t

countVarNodes :: Tree ix val -> Int
countVarNodes (Var _) = 1
countVarNodes t       = sumCountsTree countVarNodes 0 t

countOccurrences :: Eq ix => Tree ix val -> ix -> Int
countOccurrences (Var ix) iy = if ix==iy then 1 else 0
countOccurrences t        iy = sumCountsTree (`countOccurrences` iy) 0 t

replaceChild :: Tree ix val -> Tree ix val -> Maybe (Tree ix val)
replaceChild (Fun g _) t = Just $ Fun g t
replaceChild (Pow _ k) t = Just $ Pow t k
replaceChild _         _ = Nothing 

replaceChildren :: Tree ix val -> Tree ix val -> Tree ix val -> Maybe (Tree ix val)
replaceChildren (Add _ _) l r     = Just $ Add l r
replaceChildren (Sub _ _) l r     = Just $ Sub l r
replaceChildren (Mul _ _) l r     = Just $ Mul l r
replaceChildren (Div _ _) l r     = Just $ Div l r
replaceChildren (Power _ _) l r   = Just $ Power l r
replaceChildren (LogBase _ _) l r = Just $ LogBase l r
replaceChildren _             _ _ = Nothing

deriveTreeBy :: (Eq ix, Eq val, Floating val) => ix -> Tree ix val -> Tree ix val
deriveTreeBy _  Empty    = Empty
deriveTreeBy dx (Var ix)
  | dx == ix  = 1
  | otherwise = 0
deriveTreeBy dx (Const val) = 0
deriveTreeBy dx (Fun g t)   =
  case deriveTreeBy dx t of
    0  -> 0
    1  -> derivative g t
    t' -> derivative g t * t'
deriveTreeBy dx (Pow t 0)   = 0    
deriveTreeBy dx (Pow t 1)   = deriveTreeBy dx t
deriveTreeBy dx (Pow t k)   = 
  case deriveTreeBy dx t of
    0 -> 0
    Const val -> Const (val * fromIntegral k) * (t *** (k-1))
    t'        -> fromIntegral k * (t *** (k-1)) * t'
deriveTreeBy dx (Add l r)     = deriveTreeBy dx l + deriveTreeBy dx r
deriveTreeBy dx (Sub l r)     = deriveTreeBy dx l - deriveTreeBy dx r
deriveTreeBy dx (Mul l r)     = deriveTreeBy dx l * r + l * deriveTreeBy dx r
deriveTreeBy dx (Div l r)     = (deriveTreeBy dx l * r - l * deriveTreeBy dx r) / r *** 2
deriveTreeBy dx (Power l r)   = l ** (r-1) * (r * deriveTreeBy dx l + l * log l * deriveTreeBy dx r)
deriveTreeBy dx (LogBase l r) = deriveTreeBy dx (log l / log r)

simplify :: (Eq ix, Eq val, Floating val, OptIntPow val) => Tree ix val -> Tree ix val
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

derivative :: (Eq ix, Eq val, Floating val) => Function -> Tree ix val -> Tree ix val
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
