{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
{-# language FlexibleContexts #-}
{-# language BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.AD 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
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

import Control.Monad (forM_)
import Control.Monad.ST ( runST )
import Data.Bifunctor (bimap, first, second)
import qualified Data.DList as DL
import Data.Massiv.Array hiding (forM_, map, replicate, zipWith)
import qualified Data.Massiv.Array as M
import qualified Data.Massiv.Array.Unsafe as UMA
import Data.Massiv.Core.Operations (unsafeLiftArray)
import Data.SRTree.Derivative ( derivative )
import Data.SRTree.Eval
    ( SRVector, evalFun, evalOp, SRMatrix, PVector, replicateAs )
import Data.SRTree.Internal
import Data.SRTree.Print (showExpr)
import Data.SRTree.Recursion ( cataM, cata, accu )
import qualified Data.Vector as V
import Debug.Trace (trace, traceShow)
import GHC.IO (unsafePerformIO)

applyUni :: (Index ix, Source r e, Floating e, Floating b) => Function -> Either (Array r ix e) b -> Either (Array D ix e) b
applyUni f (Left t)  =
    Left $ M.map (evalFun f) t
applyUni f (Right t) =
    Right $ evalFun f t
{-# INLINE applyUni #-}

applyDer :: (Index ix, Source r e, Floating e, Floating b) => Function -> Either (Array r ix e) b -> Either (Array D ix e) b
applyDer f (Left t)  =
    Left $ M.map (derivative f) t
applyDer f (Right t) =
    Right $ derivative f t
{-# INLINE applyDer #-}

negate' :: (Index ix, Source r e, Num e, Num b) => Either (Array r ix e) b -> Either (Array D ix e) b
negate' (Left t) = Left $ M.map negate t
negate' (Right t) = Right $ negate t
{-# INLINE negate' #-}

applyBin :: (Index ix, Floating b) => Op -> Either (Array D ix b) b -> Either (Array D ix b) b -> Either (Array D ix b) b
applyBin op (Left ly) (Left ry) =
    Left $ case op of
             Add -> ly !+! ry
             Sub -> ly !-! ry
             Mul -> ly !*! ry
             Div -> ly !/! ry
             Power -> ly .** ry
             PowerAbs -> M.map abs (ly .** ry)
             AQ -> ly !/! (M.map sqrt (M.map (+1) (ry !*! ry)))

applyBin op (Left ly) (Right ry)  =
    Left $ unsafeLiftArray (\ x -> evalOp op x ry) ly
applyBin op (Right ly) (Left ry)  =
    Left $ unsafeLiftArray (\ x -> evalOp op ly x) ry
applyBin op (Right ly) (Right ry) =
    Right $ evalOp op ly ry
{-# INLINE applyBin #-}

-- | get the value of a certain index if it is an array (Left) 
-- or returns the value itself if it is a scalar.
(!??) :: (Manifest r e, Index ix) => Either (Array r ix e) e -> ix -> e
(Left y) !?? ix  = y ! ix
(Right y) !?? ix = y
{-# INLINE (!??) #-}

-- | Calculates the results of the error vector multiplied by the Jacobian of an expression using forward mode
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
    -- | if the tree does not use a variable 
    -- it will return a single scalar, fromEither fixes this
    fromEither (Left y)  = y
    fromEither (Right y) = M.replicate cmp (Sz m) y

    -- if it is a variable, returns the value of that variable and an array of zeros (Jacobian)
    alg (Var ix) = do tape  <- M.newMArray (Sz2 m p) 0 
                                 >>= UMA.unsafeFreeze cmp
                      pure (Left (xss <! ix), tape)

    -- if it is a constant, returns the value of the constant and array of zeros 
    alg (Const c) = do tape <- M.newMArray (Sz2 m p) 0
                                 >>= UMA.unsafeFreeze cmp
                       pure (Right c, tape)

    -- if it is a parameter, returns the value of the parameter and the jacobian with a one in the corresponding column
    alg (Param ix) = do tape <- M.makeMArrayS (Sz2 m p) (\(i :. j) -> pure $ if j==ix then 1 else 0)
                                 >>= UMA.unsafeFreeze cmp
                        pure (Right (theta ! ix), tape)

    -- 1. applies the derivative of f in the evaluated child 
    -- 2. replaces the value of the Jacobian at (i, j) with yi * J[i, j]
    alg (Uni f (t, tape')) = do let y = computeAs S . fromEither $ applyDer f t
                                tape <- UMA.unsafeThaw tape'
                                forM_ [0 .. m-1] $ \i -> do
                                    let yi = y ! i
                                    forM_ [0 .. p-1] $ \j -> do
                                        v <- UMA.unsafeRead tape (i :. j)
                                        UMA.unsafeWrite tape (i :. j) (yi * v)
                                tapeF <- UMA.unsafeFreeze cmp tape
                                pure (applyUni f t, tapeF)
    -- li, ri are the corresponding values of the evaluated left and right children 
    -- vl, vr are the corresponding value of the Jacobian at (i, j) 
    -- applies the corresponding derivative of each binary operator 
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
                UMA.unsafeWrite tl (i :. j) $ case op of
                  Add      -> (vl+vr)
                  Sub      -> (vl-vr)
                  Mul      -> (vl * ri + vr * li)
                  Div      -> ((vl * ri - vr * li) / ri^2)
                  Power    -> (li ** (ri - 1) * (ri * vl + li * log li * vr))
                  PowerAbs -> (abs li ** ri) * (vr * log (abs li) + ri * vl / li)
                  AQ       -> ((1 + ri*ri) * vl - li * ri * vr) / (1 + ri*ri) ** 1.5
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
      alg (Bin PowerAbs (v1, l) (v2, r)) = let dv1 = abs v1 ** v2
                                               dv2 = DL.map (* (log (abs v1))) r
                                               dv3 = DL.map (*(v2 / v1)) l
                                           in (abs v1 ** v2, DL.map (*dv1) (DL.append dv2 dv3))
      alg (Bin AQ (v1, l) (v2, r)) = let dv1 = DL.map (*(1 + v2*v2)) l
                                         dv2 = DL.map (*(-v1*v2)) r
                                     in (v1/sqrt(1 + v2*v2), DL.map (/(1 + v2*v2)**1.5) $ DL.append dv1 dv2)

data TupleF a b = Single a | T a b | Branch a b b deriving Functor -- hi, I'm a tree
type Tuple a = Fix (TupleF a)

-- | Same as above, but using reverse mode, that is even faster.
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
      --
      -- this should return a tuple, where the left element is
      -- dx * d op(f(x), g(x)) / d f(x) and
      -- the right branch dx * d op (f(x), g(x)) / d g(x)
      diff Add dx fx gy = (dx, dx)
      diff Sub dx fx gy = (dx, negate' dx)
      diff Mul dx fx gy = (applyBin Mul dx gy, applyBin Mul dx fx)
      diff Div dx fx gy = (applyBin Div dx gy, applyBin Mul dx (applyBin Div (negate' fx) (applyBin Mul gy gy)))
      diff Power dx fx gy = let dxl = applyBin Mul dx (applyBin Power fx (applyBin Sub gy (Right 1)))
                                dv2 = applyBin Mul fx (applyUni Log fx)
                            in (applyBin Mul dxl gy, applyBin Mul dxl dv2)
      diff PowerAbs dx fx gy = let dxl = applyBin Mul (applyBin Mul gy fx) (applyBin PowerAbs fx (applyBin Sub gy (Right 2)))
                                   dxr = applyBin Mul (applyUni LogAbs fx) (applyBin PowerAbs fx gy)
                               in (applyBin Mul dxl dx, applyBin Mul dxr dx)
      diff AQ dx fx gy = let dxl = applyUni Recip (applyUni Sqrt (applyBin Add (applyUni Square gy) (Right 1)))
                             dxy = applyBin Div (applyBin Mul fx gy) (applyUni Cube (applyUni Sqrt (applyBin Add (applyUni Square gy) (Right 1))))
                         in (applyBin Mul dxl dx, applyBin Mul dxy dx)


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
      alg (Bin PowerAbs (v1, l) (v2, r)) = let dv1 = abs v1 ** v2
                                               dv2 = DL.map (* (log (abs v1))) r
                                               dv3 = DL.map (*(v2 / v1)) l
                                           in (abs v1 ** v2, DL.map (*dv1) (DL.append dv2 dv3))
      alg (Bin AQ (v1, l) (v2, r)) = let dv1 = DL.map (*(1 + v2*v2)) l
                                         dv2 = DL.map (*(-v1*v2)) r
                                     in (v1/sqrt(1 + v2*v2), DL.map (/(1 + v2*v2)**1.5) $ DL.append dv1 dv2)
