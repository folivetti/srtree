{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.AD 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Automatic Differentiation for Expression trees
--
-----------------------------------------------------------------------------

module Data.SRTree.AD
         ( forwardMode
         , forwardModeUnique
         , reverseModeUnique
         ) where

import Data.SRTree.Internal
import Data.SRTree.Eval
import Data.SRTree.Derivative
import Data.SRTree.Recursion

import qualified Data.DList as DL
import qualified Data.Vector as V
import qualified Data.Vector.Storable as VS
import Data.Vector.Storable ((!))
import Data.Bifunctor (second)

newtype Tape a = Tape { untape :: [a] } deriving (Show, Functor)

instance Num a => Num (Tape a) where
  (Tape x) + (Tape y) = Tape $ zipWith (+) x y
  (Tape x) - (Tape y) = Tape $ zipWith (-) x y
  (Tape x) * (Tape y) = Tape $ zipWith (*) x y
  abs (Tape x) = Tape (map abs x)
  signum (Tape x) = Tape (map signum x)
  fromInteger x = Tape [fromInteger x]
  negate (Tape x) = Tape $ map (*(-1)) x
instance Floating a => Floating (Tape a) where
  pi = Tape [pi]
  exp (Tape x) = Tape (map exp x)
  log (Tape x) = Tape (map log x)
  sqrt (Tape x) = Tape (map sqrt x)
  sin (Tape x) = Tape (map sin x)
  cos (Tape x) = Tape (map cos x)
  tan (Tape x) = Tape (map tan x)
  asin (Tape x) = Tape (map asin x)
  acos (Tape x) = Tape (map acos x)
  atan (Tape x) = Tape (map atan x)
  sinh (Tape x) = Tape (map sinh x)
  cosh (Tape x) = Tape (map cosh x)
  tanh (Tape x) = Tape (map tanh x)
  asinh (Tape x) = Tape (map asinh x)
  acosh (Tape x) = Tape (map acosh x)
  atanh (Tape x) = Tape (map atanh x)
  (Tape x) ** (Tape y) = Tape $ zipWith (**) x y
instance Fractional a => Fractional (Tape a) where
  fromRational x = Tape [fromRational x]
  (Tape x) / (Tape y) = Tape $ zipWith (/) x y
  recip (Tape x) = Tape $ map recip x

-- | Calculates the numerical derivative of a tree using forward mode
-- provided a vector of variable values `xss`, a vector of parameter values `theta` and
-- a function that changes a Double value to the type of the variable values.
forwardMode :: (Show a, Num a, Floating a) => V.Vector a -> VS.Vector Double -> (Double -> a) -> Fix SRTree -> [a]
forwardMode xss theta f = untape . fst (mutu alg1 alg2)
  where
      n = VS.length theta
      repMat v = Tape $ replicate n v
      zeroes = repMat $ f 0
      twos  = repMat $ f 2
      tapeXs = [repMat $ xss V.! ix | ix <- [0 .. V.length xss - 1]]
      tapeTheta = [repMat $ f (theta ! ix) | ix <- [0 .. n - 1]]
      paramVec = [ Tape [if ix==iy then f 1 else f 0 | iy <- [0 .. n-1]] | ix <- [0 .. n-1] ]

      alg1 (Var ix)        = zeroes
      alg1 (Param ix)      = paramVec !! ix
      alg1 (Const _)       = zeroes
      alg1 (Uni f t)       = derivative f (snd t) * fst t
      alg1 (Bin Add l r)   = fst l + fst r
      alg1 (Bin Sub l r)   = fst l - fst r
      alg1 (Bin Mul l r)   = (fst l * snd r) + (snd l * fst r)
      alg1 (Bin Div l r)   = ((fst l * snd r) - (snd l * fst r)) / snd r ** twos
      alg1 (Bin Power l r) = snd l ** (snd r - 1) * ((snd r * fst l) + (snd l * log (snd l) * fst r))

      alg2 (Var ix)     = tapeXs !! ix
      alg2 (Param ix)   = tapeTheta !! ix
      alg2 (Const c)    = repMat $ f c
      alg2 (Uni g t)    = fmap (evalFun g) (snd t)
      alg2 (Bin op l r) = evalOp op (snd l) (snd r)

-- | The function `forwardModeUnique` calculates the numerical gradient of the tree and evaluates the tree at the same time. It assumes that each parameter has a unique occurrence in the expression. This should be significantly faster than `forwardMode`.
forwardModeUnique  :: (Show a, Num a, Floating a) => V.Vector a -> VS.Vector Double -> (Double -> a) -> Fix SRTree -> (a, [a])
forwardModeUnique xss theta f = second DL.toList . cata alg
  where
      n = VS.length theta

      alg (Var ix)        = (xss V.! ix, DL.empty)
      alg (Param ix)      = (f $ theta ! ix, DL.singleton 1)
      alg (Const c)       = (f c, DL.empty)
      alg (Uni f (v, gs)) = let v' = evalFun f v
                                dv = derivative f v
                             in (v', DL.map (*dv) gs)
      alg (Bin Add (v1, l) (v2, r)) = (v1+v2, DL.append l r)
      alg (Bin Sub (v1, l) (v2, r)) = (v1-v2, DL.append l (DL.map negate r))
      alg (Bin Mul (v1, l) (v2, r)) = (v1*v2, DL.append (DL.map (*v2) l) (DL.map (*v1) r))
      alg (Bin Div (v1, l) (v2, r)) = let dv = (-v1/v2^2) 
                                       in (v1/v2, DL.append (DL.map (/v2) l) (DL.map (*dv) r))
      alg (Bin Power (v1, l) (v2, r)) = let dv1 = v1 ** (v2 - 1)
                                            dv2 = v1 * log v1
                                         in (v1 ** v2, DL.map (*dv1) (DL.append (DL.map (*v2) l) (DL.map (*dv2) r)))

data TupleF a b = S a | T a b | B a b b deriving Functor -- hi, I'm a tree
type Tuple a = Fix (TupleF a)

-- | Same as above, but using reverse mode, that is much faster.
reverseModeUnique  :: forall a . (Show a, Num a, Floating a) => V.Vector a -> VS.Vector Double -> (Double -> a) -> Fix SRTree -> (a, [a])
reverseModeUnique xss theta f t = (getTop fwdMode, DL.toList g)
  where
      fwdMode = cata forward t
      g = accu reverse combine t (1, fwdMode)

      oneTpl x  = Fix $ S x
      tuple x y = Fix $ T x y
      branch x y z = Fix $ B x y z
      getTop (Fix (S x)) = x
      getTop (Fix (T x y)) = x
      getTop (Fix (B x y z)) = x
      unCons (Fix (T x y)) = y
      getBranches (Fix (B x y z)) = (y,z)

      -- forward just creates a new tree with the partial
      -- evaluation of the nodes
      forward (Var ix)     = oneTpl (xss V.! ix)
      forward (Param ix)   = oneTpl (f $ theta ! ix)
      forward (Const c)    = oneTpl (f c)
      forward (Uni f t)    = let v = getTop t
                              in tuple (evalFun f v) t
      forward (Bin op l r) = let vl = getTop l
                                 vr = getTop r
                              in branch (evalOp op vl vr) l r

      -- reverse walks from the root to the leaf calculating the
      -- partial derivative with respect to an arbitrary variable
      -- up to that point
      reverse (Var ix)     (dx,   _)        = Var ix
      reverse (Param ix)   (dx,   _)        = Param ix
      reverse (Const v)    (dx,   _)        = Const v
      reverse (Uni f t)    (dx, unCons -> v) =
          let g'  = derivative f (getTop v)
           in Uni f (t, ( dx*g', v ))
      reverse (Bin op l r) (dx, getBranches -> (vl, vr)) = 
          let (dxl, dxr) = diff op dx (getTop vl) (getTop vr)
           in Bin op (l, (dx*dxl, vl)) (r, (dx*dxr, vr))

      -- dx is the current derivative so far
      -- fx is the evaluation of the left branch
      -- gx is the evaluation of the right branch
      diff Add dx fx gy = (dx, dx)
      diff Sub dx fx gy = (dx, negate dx)
      diff Mul dx fx gy = (dx * gy, dx * fx)
      diff Div dx fx gy = (dx / gy, dx * (-fx/gy^2))
      diff Power dx fx gy = let dxl = dx * fx ** (gy - 1)
                                dv2 = fx * log fx
                             in (dxl * gy, dxl * dv2)


      -- once we reach a leaf with a parameter, we return a singleton
      -- with that derivative upwards until the root
      combine (Var ix)     s = DL.empty
      combine (Param ix)   s = DL.singleton $ fst s
      combine (Const c)    s = DL.empty
      combine (Uni _ gs)   s = gs
      combine (Bin op l r) s = DL.append l r

{-
reverseModeDiagHessUnique  :: forall a . (Show a, Num a, Floating a) => V.Vector a -> V.Vector Double -> (Double -> a) -> Fix SRTree -> (a, [a], [a])
reverseModeDiagHessUnique xss theta f t = (getTop fwdMode, DL.toList g)
  where
      fwdMode = cata forward t
      g = accu reverse combine t ((1, 1), fwdMode)

      oneTpl x  = Fix $ S x
      tuple x y = Fix $ T x y
      branch x y z = Fix $ B x y z
      getTop (Fix (S x)) = x
      getTop (Fix (T x y)) = x
      getTop (Fix (B x y z)) = x
      unCons (Fix (T x y)) = y
      getBranches (Fix (B x y z)) = (y,z)

      -- forward just creates a new tree with the partial
      -- evaluation of the nodes
      forward (Var ix)     = oneTpl (xss ! ix)
      forward (Param ix)   = oneTpl (f $ theta ! ix)
      forward (Const c)    = oneTpl (f c)
      forward (Uni f t)    = let v = getTop t
                              in tuple (evalFun f v) t
      forward (Bin op l r) = let vl = getTop l
                                 vr = getTop r
                              in branch (evalOp op vl vr) l r

      -- reverse walks from the root to the leaf calculating the
      -- partial derivative with respect to an arbitrary variable
      -- up to that point
      reverse (Var ix)     ((dx, ddx),   _)        = Var ix
      reverse (Param ix)   ((dx, ddx),   _)        = Param ix
      reverse (Const v)    ((dx, ddx),   _)        = Const v
      reverse (Uni f t)    ((dx, ddx), unCons -> v) =
          let g'  = derivative f (getTop v)
              g'' = doubleDerivative f (getTop v)
           in Uni f (t, ( (dx*g', ddx * g'^2 + dx * g''), v ))
      reverse (Bin op l r) ((dx, ddx), getBranches -> (vl, vr)) = 
          let (dxl, dxr) = diff op dx (getTop vl) (getTop vr)
              (ddxl, ddxr) = ddiff op dx ddx (getTop vl) (getTop vr)
              ddxl' = ddx * dxl^2 + dx * ddxl
              ddxr' = ddx * dxr^2 + dx * ddxr
           in Bin op (l, ((dx*dxl, ddxl'), vl)) (r, ((dx*dxr, ddxr'), vr))

{ -
h(f(x))

h' f' 1
(h'' f'^2 + h' f'') . 1^2 + h'f' . 0


h(f + g)


ln( x^2 + y^2 )

1/u -1/u^2
2x  2
2y  2

dh/dx = h' 1 f'
dh/dy = h' 1 g'

ddh_x = h'' 1 f'^2 + h' 1 f''
ddh_y = h'' 1 g'^2 + h' 1 g''


ln( x^2 * y^2 )

dh_x = h' g f' = 1/(x^2 y^2) * y^2 * 2x = 2/x
dh_y = h' f g' = 1/(x^2 y^2) * x^2 * 2y = 2/y

ddh_x = h'' g^2 f'^2 + h' g f'' = -1/(x^2 y^2)^2 * y^4 * 4x^2 + 1/(x^2y^2) * y^2 2 = -4/x^2 + 2/x^2 = -2/x^2
ddh_y = h'' f^2 g'^2 + h' f g'' = -2/y^2

ln( x^2 / y^2 )

1/ x^2/y^2

dh_x = h' (1/g) f' = y^2/x^2 * 1/y^2 * 2x = 2/x
dh_y = h' (-f/g^2) g' = y^2/x^2 * (-x^2 / y^4) * 2y = -2/y

ddh_x = h'' (1/g^2) f'^2 + h' (1/g) f'' = -y^4/x^4 (1 / y^4) (4x^2) + y^2/x^2 (1/y^2) 2 = -4/x^2 + 2/x^2 = -2/x^2
ddh_y = (h' d'' + h''d'^2) g'^2 + h' d' g'' = 4/y^2 - 2/y^2 = 2/y^2

h' = y^2/x^2
h'' = -y^4/x^4
d' = -f/g^2 = -x^2/y^4
d'' = 2f/g^3 = 2x^2/y^6

(y^2/x^2 2x^2/y^6 - y^4/x^4 x^4/y^8) 4y^2 = 8/y^2 - 4/y^2 = 4/y^2
y^2/x^2 (-x^2/y^4) 2 = -2/y^2

ln( x^2 ^ y^2 )

h' = 1 / (x^2 ^ y^2)
h'' = - 1 / (x^2 ^ 2*y^2)

dh_x  = 1 / (x^2 ^ y^2) * y^2 * x^2(y^2-1) * 2x = 2 * y^2 / x
ddh_x = 
- }
      -- dx is the current derivative so far
      -- fx is the evaluation of the left branch
      -- gx is the evaluation of the right branch
      diff Add dx fx gy = (dx, dx)
      diff Sub dx fx gy = (dx, negate dx)
      diff Mul dx fx gy = (dx * gy, dx * fx)
      diff Div dx fx gy = (dx / gy, dx * (-fx/gy^2))
      diff Power dx fx gy = let dxl = dx * fx ** (gy - 1)
                                dv2 = fx * log fx
                             in (dxl * gy, dxl * dv2)

      ddiff Add dx ddx fx gy = (ddx, ddx)
      ddiff Sub dx ddx fx gy = (ddx, negate ddx)
      ddiff Mul dx ddx fx gy = (ddx * gy, ddx * fx)
      ddiff Div dx ddx fx gy = (ddx / gy, fx * (2*dx^2 - gy*ddx) / gy^3)
      ddiff Power dx ddx vl vr = let ddxl = vr * vl**(vr - 2) * (vl * ddx + (vr - 1)*dx^2)
                                     ddxr = 
                                     dv2 = vl * log vl
                                  in (dxl * vr, dxl * dv2)


      -- once we reach a leaf with a parameter, we return a singleton
      -- with that derivative upwards until the root
      combine (Var ix)     s = DL.empty
      combine (Param ix)   s = DL.singleton $ fst s
      combine (Const c)    s = DL.empty
      combine (Uni _ gs)   s = gs
      combine (Bin op l r) s = DL.append l r
-}

