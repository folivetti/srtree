{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
{-# language FlexibleContexts #-}
{-# language BangPatterns #-}
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
         , forwardModeUniqueJac
         ) where

import Data.SRTree.Internal
import Data.SRTree.Eval
import Data.SRTree.Derivative
import Data.SRTree.Recursion

import qualified Data.Massiv.Array as M
import qualified Data.Massiv.Array.Unsafe as UMA
import Data.Massiv.Array hiding (map, zipWith, replicate, forM_)
import Data.Massiv.Core.Operations ( unsafeLiftArray )
import qualified Data.Vector as V 

import qualified Data.DList as DL
import Data.Bifunctor (bimap, first, second)
import Control.Monad ( forM_ )
import Debug.Trace ( traceShow, trace )
import GHC.IO (unsafePerformIO)
import Control.Monad.ST
import Algorithm.SRTree.NonlinearOpt

import Data.SRTree.Print ( showExpr )

applyUni f (Left t)  =
    Left $ M.map (evalFun f) t
applyUni f (Right t) =
    Right $ evalFun f t
{-# INLINE applyUni #-}

applyDer f (Left t)  =
    Left $ M.map (derivative f) t
applyDer f (Right t) =
    Right $ derivative f t
{-# INLINE applyDer #-}

negate' (Left t) = Left $ M.map negate t
negate' (Right t) = Right $ negate t
{-# INLINE negate' #-}

applyBin op (Left ly) (Left ry) =
    Left $ case op of
             Add -> ly !+! ry
             Sub -> ly !-! ry
             Mul -> ly !*! ry
             Div -> ly !/! ry
             Power -> ly .** ry

applyBin op (Left ly) (Right ry)  =
    Left $ unsafeLiftArray (\ x -> evalOp op x ry) ly
applyBin op (Right ly) (Left ry)  =
    Left $ unsafeLiftArray (\ x -> evalOp op ly x) ry
applyBin op (Right ly) (Right ry) =
    Right $ evalOp op ly ry
{-# INLINE applyBin #-}

(Left y) !?? ix  = y ! ix
(Right y) !?? ix = y
{-# INLINE (!??) #-}

-- | Calculates the numerical derivative of a tree using forward mode
-- provided a vector of variable values `xss`, a vector of parameter values `theta` and
-- a function that changes a Double value to the type of the variable values.
-- uses unsafe operations to use mutable array instead of a tape
forwardMode :: Array S Ix2 Double -> Array S Ix1 Double -> SRVector -> Fix SRTree -> (Array D Ix1 Double, Array S Ix1 Double)
forwardMode xss theta err tree = let (yhat, jacob) = runST $ cataM lToR alg tree
                                 in (fromEither yhat, computeAs S err ><! jacob)
  where 
    (Sz p)               = M.size theta
    (Sz (m :. n))        = M.size xss
    cmp                  = getComp xss
    fromEither (Left y)  = y
    fromEither (Right y) = M.replicate cmp (Sz m) y

    alg (Var ix) = do tape <- M.newMArray (Sz2 m p) 0
                      tape' <- UMA.unsafeFreeze cmp tape
                      pure (Left $ (xss <! ix), tape')

    alg (Const c) = do tape <- M.newMArray (Sz2 m p) 0
                       tape' <- UMA.unsafeFreeze cmp tape
                       pure (Right c, tape')
    alg (Param ix) = do tape <- M.makeMArrayS (Sz2 m p) (\(i :. j) -> pure $ if j==ix then 1 else 0)
                        tape' <- UMA.unsafeFreeze cmp tape
                        pure (Right (theta ! ix), tape')

    alg (Uni f (t, tape')) = do let y = computeAs S . fromEither $ applyDer f t
                                tape <- UMA.unsafeThaw tape'
                                forM_ [0 .. m-1] $ \i -> do
                                    let yi = y ! i
                                    forM_ [0 .. p-1] $ \j -> do
                                        v <- UMA.unsafeRead tape (i :. j)
                                        UMA.unsafeWrite tape (i :. j) (yi * v)
                                tapeF <- UMA.unsafeFreeze cmp tape
                                pure (applyUni f t, tapeF)
    alg (Bin op (l, tl') (r, tr')) = do
        tl <- UMA.unsafeThaw tl'
        tr <- UMA.unsafeThaw tr'
        let l' = case l of
                   Left y -> Left $ computeAs S y
                   Right v -> Right v
            r' = case r of
                   Left y -> Left $ computeAs S y
                   Right v -> Right v
        forM_ [0 .. m-1] $ \i -> do 
            let li = l' !?? i
                ri = r' !?? i
            forM_ [0 .. p-1] $ \j -> do 
                vl <- UMA.unsafeRead tl (i :. j)
                vr <- UMA.unsafeRead tr (i :. j)
                case op of 
                  Add -> UMA.unsafeWrite tl (i :. j) (vl+vr)
                  Sub -> UMA.unsafeWrite tl (i :. j) (vl-vr)
                  Mul -> UMA.unsafeWrite tl (i :. j) (vl * ri + vr * li)
                  Div -> UMA.unsafeWrite tl (i :. j) ((vl * ri - vr * li) / ri^2)
                  Power -> UMA.unsafeWrite tl (i :. j) (li ** (ri - 1) * (ri * vl + li * log li * vr))
        tlF <- UMA.unsafeFreeze cmp tl
        pure (applyBin op l r, tlF)


    lToR (Var ix) = pure (Var ix)
    lToR (Param ix) = pure (Param ix)
    lToR (Const c) = pure (Const c)
    lToR (Uni f mt) = Uni f <$> mt
    lToR (Bin op ml mr) = Bin op <$> ml <*> mr

-- | The function `forwardModeUnique` calculates the numerical gradient of the tree and evaluates the tree at the same time. It assumes that each parameter has a unique occurrence in the expression. This should be significantly faster than `forwardMode`.
forwardModeUnique  :: SRMatrix -> PVector -> SRVector -> Fix SRTree -> (SRVector, Array S Ix1 Double)
forwardModeUnique xss theta err = second (toGrad . DL.toList) . cata alg
  where
      (Sz n) = M.size theta
      one    = replicateAs xss 1
      toGrad grad = M.fromList (getComp xss) [g !.! err | g <- grad]

      alg (Var ix)        = (xss <! ix, DL.empty)
      alg (Param ix)      = (replicateAs xss $ theta ! ix, DL.singleton one)
      alg (Const c)       = (replicateAs xss c, DL.empty)
      alg (Uni f (v, gs)) = let v' = evalFun f v
                                dv = derivative f v
                             in (v', DL.map (*dv) gs)
      alg (Bin Add (v1, l) (v2, r)) = (v1+v2, DL.append l r)
      alg (Bin Sub (v1, l) (v2, r)) = (v1-v2, DL.append l (DL.map negate r))
      alg (Bin Mul (v1, l) (v2, r)) = (v1*v2, DL.append (DL.map (*v2) l) (DL.map (*v1) r))
      alg (Bin Div (v1, l) (v2, r)) = let dv = ((-v1)/(v2*v2)) 
                                       in (v1/v2, DL.append (DL.map (/v2) l) (DL.map (*dv) r))
      alg (Bin Power (v1, l) (v2, r)) = let dv1 = v1 ** (v2 - one)
                                            dv2 = v1 * log v1
                                         in (v1 ** v2, DL.map (*dv1) (DL.append (DL.map (*v2) l) (DL.map (*dv2) r)))
    
data TupleF a b = Single a | T a b | Branch a b b deriving Functor -- hi, I'm a tree
type Tuple a = Fix (TupleF a)

-- | Same as above, but using reverse mode, that is much faster.
reverseModeUnique :: SRMatrix
                  -> PVector
                  -> SRVector
                  -> (SRVector -> SRVector)
                  -> Fix SRTree
                  -> (Array D Ix1 Double, Array S Ix1 Double)
reverseModeUnique xss theta ys f t = unsafePerformIO $
                                          do jacob <- M.newMArray (Sz p) 0
                                             let !_ = accu reverse (combine jacob) t ((Right 1), fwdMode)
                                             j <- freezeS jacob
                                             pure (v, j)
  where
      fwdMode = cata forward t
      v       = fromEither $ getTop fwdMode
      err     = f v - ys
      (Sz2 m _)            = M.size xss
      p = countParams t
      fromEither (Left x)  = x
      fromEither (Right x) = M.replicate (getComp xss) (Sz1 m) x

      oneTpl x     = Fix $ Single x
      tuple x y    = Fix $ T x y
      branch x y z = Fix $ Branch x y z

      getTop (Fix (Single x))          = x
      getTop (Fix (T x y))             = x
      getTop (Fix (Branch x y z))      = x

      unCons (Fix (T x y))             = y
      getBranches (Fix (Branch x y z)) = (y,z)

      -- forward just creates a new tree with the partial
      -- evaluation of the nodes
      forward (Var ix)     = oneTpl (Left $ xss <! ix)
      forward (Param ix)   = oneTpl (Right $ theta ! ix)
      forward (Const c)    = oneTpl (Right c)
      forward (Uni g t)    = let v = getTop t
                             in tuple (applyUni g v) t
      forward (Bin op l r) = let vl = getTop l
                                 vr = getTop r
                              in branch (applyBin op vl vr) l r



      -- reverse walks from the root to the leaf calculating the
      -- partial derivative with respect to an arbitrary variable
      -- up to that point
      reverse (Var ix)     (dx,   _)         = Var ix
      reverse (Param ix)   (dx,   _)         = Param ix
      reverse (Const v)    (dx,   _)         = Const v
      reverse (Uni f t)    (dx, unCons -> v) =
          let g' = applyDer f (getTop v)
          in Uni f (t, ( applyBin Mul dx g', v ))
      reverse (Bin op l r) (dx, getBranches -> (vl, vr)) =
          let (dxl, dxr) = diff op dx (getTop vl) (getTop vr)
           in Bin op (l, (dxl, vl)) (r, (dxr, vr))

      -- dx is the current derivative so far
      -- fx is the evaluation of the left branch
      -- gx is the evaluation of the right branch
      diff Add dx fx gy = (dx, dx)
      diff Sub dx fx gy = (dx, negate' dx)
      diff Mul dx fx gy = (applyBin Mul dx gy, applyBin Mul dx fx)
      diff Div dx fx gy = (applyBin Div dx gy, applyBin Mul dx (applyBin Div (negate' fx) (applyBin Mul gy gy)))
      diff Power dx fx gy = let dxl = applyBin Mul dx (applyBin Power fx (applyBin Sub gy (Right 1)))
                                dv2 = applyBin Mul fx (applyUni Log fx)
                            in (applyBin Mul dxl gy, applyBin Mul dxl dv2)


      -- once we reach a leaf with a parameter, we return a singleton
      -- with that derivative upwards until the root
      --combine :: (forall s . MArray (PrimState (ST s)) S Int Double) -> SRTree () -> (Either SRVector Double, a) -> ()
      combine j (Var ix) s = 0
      combine j (Const _) s = 0
      combine j (Param ix) s = unsafePerformIO $ do
                                 case fst s of
                                   Left v  -> do v' <- dotM v err
                                                 UMA.unsafeWrite j ix v'
                                   Right v -> UMA.unsafeWrite j ix $ M.foldrS (\x acc -> x*v + acc) 0 err
                                 UMA.unsafeRead j ix
      combine j (Uni f gs) s = gs
      combine j (Bin op l r) s = l+r


-- | The function `forwardModeUnique` calculates the numerical gradient of the tree and evaluates the tree at the same time. It assumes that each parameter has a unique occurrence in the expression. This should be significantly faster than `forwardMode`.
forwardModeUniqueJac  :: SRMatrix -> PVector -> Fix SRTree -> [PVector]
forwardModeUniqueJac xss theta = snd . second (map (M.computeAs M.S) . DL.toList) . cata alg
  where
      (Sz n) = M.size theta
      one    = replicateAs xss 1

      alg (Var ix)        = (xss <! ix, DL.empty)
      alg (Param ix)      = (replicateAs xss $ theta ! ix, DL.singleton one)
      alg (Const c)       = (replicateAs xss c, DL.empty)
      alg (Uni f (v, gs)) = let v' = evalFun f v
                                dv = derivative f v
                             in (v', DL.map (*dv) gs)
      alg (Bin Add (v1, l) (v2, r)) = (v1+v2, DL.append l r)
      alg (Bin Sub (v1, l) (v2, r)) = (v1-v2, DL.append l (DL.map negate r))
      alg (Bin Mul (v1, l) (v2, r)) = (v1*v2, DL.append (DL.map (*v2) l) (DL.map (*v1) r))
      alg (Bin Div (v1, l) (v2, r)) = let dv = ((-v1)/(v2*v2))
                                       in (v1/v2, DL.append (DL.map (/v2) l) (DL.map (*dv) r))
      alg (Bin Power (v1, l) (v2, r)) = let dv1 = v1 ** (v2 - one)
                                            dv2 = v1 * log v1
                                         in (v1 ** v2, DL.map (*dv1) (DL.append (DL.map (*v2) l) (DL.map (*dv2) r)))
