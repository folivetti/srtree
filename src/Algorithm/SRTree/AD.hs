{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
{-# language FlexibleContexts #-}
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

module Algorithm.SRTree.AD
         ( forwardMode
         , forwardModeUnique
         , reverseModeUnique
         ) where

import Data.SRTree.Internal
import Data.SRTree.Eval
import Data.SRTree.Derivative
import Data.SRTree.Recursion

import qualified Data.Massiv.Array as M
import qualified Data.Massiv.Array.Unsafe as UMA
import Data.Massiv.Array hiding (map, zipWith, replicate, forM_)
import qualified Data.Vector as V 

import qualified Data.DList as DL
import Data.Bifunctor (bimap, first, second)
import Control.Monad ( forM_ )
import Debug.Trace ( traceShow ) 
import GHC.IO (unsafePerformIO)

-- | Calculates the numerical derivative of a tree using forward mode
-- provided a vector of variable values `xss`, a vector of parameter values `theta` and
-- a function that changes a Double value to the type of the variable values.
-- uses unsafe operations to use mutable array instead of a tape
forwardMode :: Array S Ix2 Double -> Array S Ix1 Double -> Fix SRTree -> (Array S Ix1 Double, Array S Ix2 Double)
forwardMode xss theta tree = (yhat, jacob)
  where 
    (yhat, mJacob) = unsafePerformIO $ cataM lToR alg tree
    jacob          = unsafePerformIO $ M.freeze cmp mJacob
    (Sz p)         = M.size theta
    (Sz (m :. n))  = M.size xss
    cmp            = getComp xss
    f              = M.replicate cmp (Sz m)

    alg (Var ix) = do tape <- M.newMArray (Sz2 m p) 0 
                      pure (computeAs S (xss <! ix), tape)
    alg (Const c) = do tape <- M.newMArray (Sz2 m p) 0
                       pure (f c, tape)
    alg (Param ix) = do tape <- M.newMArray (Sz2 m p) 0
                        forM_ [0 .. m-1] $ \i -> UMA.unsafeWrite tape (i :. ix) 1
                        pure (f (theta ! ix), tape)
    alg (Uni f (t, tape)) = do let y = computeAs S $ M.map (derivative f) t 
                               forM_ [0 .. m-1] $ \i -> do 
                                   let yi = y ! i 
                                   forM_ [0 .. p-1] $ \j -> do 
                                       v <- UMA.unsafeRead tape (i :. j) 
                                       UMA.unsafeWrite tape (i :. j) (yi * v)
                               pure (computeAs S $ M.map (evalFun f) $ delay t, tape)
    alg (Bin op (l, tl) (r, tr)) = do 
        let y = computeAs S $ evalOp op (delay l) (delay r) 
        forM_ [0 .. m-1] $ \i -> do 
            let li = l ! i
                ri = r ! i
            forM_ [0 .. p-1] $ \j -> do 
                vl <- UMA.unsafeRead tl (i :. j)
                vr <- UMA.unsafeRead tr (i :. j)
                case op of 
                  Add -> UMA.unsafeWrite tl (i :. j) (vl+vr)
                  Sub -> UMA.unsafeWrite tl (i :. j) (vl-vr)
                  Mul -> UMA.unsafeWrite tl (i :. j) (vl * ri + vr * li)
                  Div -> UMA.unsafeWrite tl (i :. j) ((vl * ri - vr * li) / ri^2)
                  Power -> UMA.unsafeWrite tl (i :. j) (li ** (ri - 1) * ((ri - vl) + li * log li * vr))
        pure (y, tl)

    lToR (Var ix) = pure (Var ix)
    lToR (Param ix) = pure (Param ix)
    lToR (Const c) = pure (Const c)
    lToR (Uni f mt) = Uni f <$> mt
    lToR (Bin op ml mr) = Bin op <$> ml <*> mr

-- | The function `forwardModeUnique` calculates the numerical gradient of the tree and evaluates the tree at the same time. It assumes that each parameter has a unique occurrence in the expression. This should be significantly faster than `forwardMode`.
forwardModeUnique  :: SRMatrix -> PVector -> Fix SRTree -> (SRVector, SRMatrix)
forwardModeUnique xss theta = second (M.computeAs S . throwEither . M.stackSlicesM 1 . DL.toList) . cata alg
  where
      (Sz n) = M.size theta

      alg (Var ix)        = (xss <! ix, DL.empty)
      alg (Param ix)      = (replicateAs xss $ theta ! ix, DL.singleton $ replicateAs xss 1)
      alg (Const c)       = (replicateAs xss c, DL.empty)
      alg (Uni f (v, gs)) = let v' = evalFun f v
                                dv = derivative f v
                             in (v', DL.map (*dv) gs)
      alg (Bin Add (v1, l) (v2, r)) = (v1+v2, DL.append l r)
      alg (Bin Sub (v1, l) (v2, r)) = (v1-v2, DL.append l (DL.map negate r))
      alg (Bin Mul (v1, l) (v2, r)) = (v1*v2, DL.append (DL.map (*v2) l) (DL.map (*v1) r))
      alg (Bin Div (v1, l) (v2, r)) = let dv = ((-v1)/v2^2) 
                                       in (v1/v2, DL.append (DL.map (/v2) l) (DL.map (*dv) r))
      alg (Bin Power (v1, l) (v2, r)) = let dv1 = v1 ** (v2 - 1)
                                            dv2 = v1 * log v1
                                         in (v1 ** v2, DL.map (*dv1) (DL.append (DL.map (*v2) l) (DL.map (*dv2) r)))

    
data TupleF a b = Single a | T a b | Branch a b b deriving Functor -- hi, I'm a tree
type Tuple a = Fix (TupleF a)

-- | Same as above, but using reverse mode, that is much faster.
reverseModeUnique  :: SRMatrix -> PVector -> Fix SRTree -> (SRVector, SRMatrix)
reverseModeUnique xss theta t = (getTop fwdMode, computeAs S $ throwEither $ stackSlicesM 1 $ DL.toList g)
  where
      fwdMode = cata forward t
      g       = accu reverse combine t (1, fwdMode)

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
      forward (Var ix)     = oneTpl (xss <! ix)
      forward (Param ix)   = oneTpl (replicateAs xss $ theta ! ix)
      forward (Const c)    = oneTpl (replicateAs xss c)
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
      diff Div dx fx gy = (dx / gy, dx * ((-fx)/gy^2))
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
