{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
{-# language TupleSections #-}
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

import qualified Data.Massiv.Array as M
import Data.Massiv.Array hiding (map, zipWith, replicate)
import qualified Data.Vector as V 

import qualified Data.DList as DL
import Data.Bifunctor (bimap, first, second)
import Debug.Trace ( traceShow ) 

type Jacob = [SRVector Double]

newtype Tape a = Tape { untape :: [a] } deriving (Show, Functor, Eq)

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
forwardMode :: SRMatrix (SRVector Double) -> PVector -> Fix SRTree -> (SRVector Double, Jacob)
forwardMode xss theta tree = bimap (head.untape) untape (cata alg tree)
  where
      (Sz p)         = M.size theta
      cmp            = getComp $ V.head xss
      (Sz n)         = M.size $ V.head xss
      f              = M.replicate cmp (Sz n)
      repMat v       = Tape $ replicate p v
      zeroes         = repMat $ f 0
      ones           = repMat $ f 1
      twos           = repMat $ f 2
      tapeXs         = [repMat $ xss V.! ix | ix <- [0 .. V.length xss - 1]]
      tapeTheta      = [repMat $ f (theta ! ix) | ix <- [0 .. p - 1]]
      paramVec       = [ Tape [if ix==iy then f 1 else f 0 | iy <- [0 .. p-1]] | ix <- [0 .. p-1] ]

      alg (Var ix)        = (tapeXs !! ix, zeroes)
      alg (Param ix)      = (tapeTheta !! ix, paramVec !! ix)
      alg (Const c)       = (repMat (f c), zeroes)
      alg (Uni f t)       = (fmap (evalFun f) (fst t), fmap (derivative f) (fst t) * snd t)
      alg (Bin Add l r)   = (fst l + fst r, snd l + snd r)
      alg (Bin Sub l r)   = (fst l - fst r, snd l - snd r)
      alg (Bin Mul l r)   = (fst l * fst r, (snd l * fst r) + (fst l * snd r))
      alg (Bin Div l r)   = (fst l / fst r, ((snd l * fst r) - (fst l * snd r)) / fst r ** twos)
      alg (Bin Power l r) = (fst l ** fst r, fst l ** (fst r - ones) * ((fst r * snd l) + (fst l * log (fst l) * snd r)))

-- | The function `forwardModeUnique` calculates the numerical gradient of the tree and evaluates the tree at the same time. It assumes that each parameter has a unique occurrence in the expression. This should be significantly faster than `forwardMode`.
forwardModeUnique  :: SRMatrix (SRVector Double) -> PVector -> Fix SRTree -> (SRVector Double, [SRVector Double])
forwardModeUnique xss theta = second DL.toList . cata alg
  where
      (Sz n) = M.size theta
      (Sz m) = M.size (V.head xss)
      cmp = getComp (V.head xss)
      f = M.replicate cmp (Sz m) -- (m :. n))

      alg (Var ix)        = (xss V.! ix, DL.empty)
      alg (Param ix)      = (f $ theta ! ix, DL.singleton $ f 1)
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

    
data TupleF a b = Single a | T a b | Branch a b b deriving Functor -- hi, I'm a tree
type Tuple a = Fix (TupleF a)

-- | Same as above, but using reverse mode, that is much faster.
reverseModeUnique  :: SRMatrix (SRVector Double) -> PVector -> Fix SRTree -> (SRVector Double, [SRVector Double])
reverseModeUnique xss theta t = (getTop fwdMode, DL.toList g)
  where
      fwdMode = cata forward t
      g = accu reverse combine t (1, fwdMode)
      (Sz m) = M.size (V.head xss)
      cmp = getComp (V.head xss)
      f = M.replicate cmp (Sz m) -- (m :. n))

      oneTpl x  = Fix $ Single x
      tuple x y = Fix $ T x y
      branch x y z = Fix $ Branch x y z
      getTop (Fix (Single x)) = x
      getTop (Fix (T x y)) = x
      getTop (Fix (Branch x y z)) = x
      unCons (Fix (T x y)) = y
      getBranches (Fix (Branch x y z)) = (y,z)

      -- forward just creates a new tree with the partial
      -- evaluation of the nodes
      forward (Var ix)     = oneTpl (xss V.! ix)
      forward (Param ix)   = oneTpl (f $ theta ! ix)
      forward (Const c)    = oneTpl (f c)
      forward (Uni g t)    = let v = getTop t
                              in tuple (evalFun g v) t
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
           in Bin op (l, (dxl, vl)) (r, (dxr, vr))

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
