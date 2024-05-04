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
         , forwardModeIO
         , forwardModeUnique
         , reverseModeUnique
         , reverseModeUniqueV2
         , reverseModeUniqueV3
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
import Debug.Trace ( traceShow ) 
import GHC.IO (unsafePerformIO)
import Control.Monad.ST
import Algorithm.SRTree.NonlinearOpt

-- | Calculates the numerical derivative of a tree using forward mode
-- provided a vector of variable values `xss`, a vector of parameter values `theta` and
-- a function that changes a Double value to the type of the variable values.
-- uses unsafe operations to use mutable array instead of a tape
forwardMode :: Array S Ix2 Double -> Array S Ix1 Double -> SRVector -> Fix SRTree -> (Array S Ix1 Double, Array S Ix1 Double)
forwardMode xss theta err tree = let (yhat, jacob) = runST $ cataM lToR alg tree
                                 in (yhat, computeAs S err ><! jacob)
  where 
    (Sz p)         = M.size theta
    (Sz (m :. n))  = M.size xss
    cmp            = getComp xss
    f              = M.replicate cmp (Sz m)

    alg (Var ix) = do tape <- M.newMArray (Sz2 m p) 0
                      tape' <- UMA.unsafeFreeze cmp tape
                      pure (computeAs S (xss <! ix), tape')

    alg (Const c) = do tape <- M.makeMArrayS (Sz2 m p) (\_ -> pure 0)
                       tape' <- UMA.unsafeFreeze cmp tape
                       pure (f c, tape')
    alg (Param ix) = do tape <- M.makeMArrayS (Sz2 m p) (\_ -> pure 0)
                        forM_ [0 .. m-1] $ \i -> UMA.unsafeWrite tape (i :. ix) 1
                        tape' <- UMA.unsafeFreeze cmp tape
                        pure (f (theta ! ix), tape')

    alg (Uni f (t, tape')) = do let y = computeAs S $ M.map (derivative f) t
                                tape <- UMA.unsafeThaw tape'
                                forM_ [0 .. m-1] $ \i -> do
                                    let yi = y ! i
                                    forM_ [0 .. p-1] $ \j -> do
                                        v <- UMA.unsafeRead tape (i :. j)
                                        UMA.unsafeWrite tape (i :. j) (yi * v)
                                tapeF <- UMA.unsafeFreeze cmp tape
                                pure (computeAs S $ M.map (evalFun f) $ delay t, tapeF)
    alg (Bin op (l, tl') (r, tr')) = do
        let y = computeAs S $ evalOp op (delay l) (delay r) 
        tl <- UMA.unsafeThaw tl'
        tr <- UMA.unsafeThaw tr'
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
        tlF <- UMA.unsafeFreeze cmp tl
        pure (y, tlF)


    lToR (Var ix) = pure (Var ix)
    lToR (Param ix) = pure (Param ix)
    lToR (Const c) = pure (Const c)
    lToR (Uni f mt) = Uni f <$> mt
    lToR (Bin op ml mr) = Bin op <$> ml <*> mr

data DLJacob = Zero | Jacob (Array D Ix2 Double)

--forwardModeIO :: Array S Ix2 Double -> Array S Ix1 Double -> Fix SRTree -> IO (Array S Ix1 Double, Array S Ix2 Double)
--forwardModeIO :: Array S Ix2 Double -> Array S Ix1 Double -> Fix SRTree -> Array D Ix1 Double
forwardModeIO xss theta tree = fromLeft $ cata alg tree
  where
    fromLeft (Right x, Jacob y) = (makeArray cmp (Sz m) (const 0), y)
    fromLeft (Left x, Jacob y) = (x <! 0, y)
    (Sz p)         = M.size theta
    (Sz (m :. n))  = M.size xss
    cmp            = getComp xss
    getFromX ix    = makeArray cmp (Sz2 m p) (\ (i:.j) -> xss ! (i :. ix) )
    getFromT ix    = makeArray cmp (Sz2 m p) (\ (i:.j) -> if j==ix then 1 else 0)

    {-
     - der f (t, t')  = derivative f t * t'
     -  t' == Zero    = Zero
     -  t' == One ix  =
     -  t' == Jacob j = derivative f t * j
     - 1 x m  * m x p  ===> m x p
     -}
    alg (Var ix) = (Left (getFromX ix), Zero)
    alg (Const c) = (Right c, Zero)
    alg (Param ix) = (Right (theta ! ix), Jacob $ getFromT ix)
    alg (Uni f (yhat, jacob)) = (applyUni f yhat, derUni f yhat jacob)
    alg (Bin op (ly, lj) (ry, rj)) = (applyBin op ly ry, derBin op ly ry lj rj)

    applyUni f (Left t)  = Left $ M.map (evalFun f) t
    applyUni f (Right t) = Right $ evalFun f t

    applyBin op (Left ly) (Left ry) = Left $ case op of
                                               Add -> ly !+! ry
                                               Sub -> ly !-! ry
                                               Mul -> ly !*! ry
                                               Div -> ly !/! ry
                                               Power -> ly .** ry
    applyBin op (Left ly) (Right ry) = Left $ unsafeLiftArray (\ x -> evalOp op x ry) ly
    applyBin op (Right ly) (Left ry) = Left $ unsafeLiftArray (\ x -> evalOp op ly x) ry
    applyBin op (Right ly) (Right ry) = Right $ evalOp op ly ry

    derUni f _         Zero      = Zero
    derUni f (Left y)  (Jacob j) = Jacob $ derivative f y * j
    derUni f (Right y) (Jacob j) = Jacob $ derivative f y *. j

    derBin _ _ _ Zero Zero = Zero

    derBin Add _ _ lj Zero = lj
    derBin Add _ _ Zero rj = rj
    derBin Add _ _ (Jacob l) (Jacob r) = Jacob $ l+r

    derBin Sub _ _ lj Zero = lj
    derBin Sub _ _ Zero (Jacob r) = Jacob $ negate r
    derBin Sub _ _ (Jacob l) (Jacob r) = Jacob $ l-r

    derBin Mul _ rv (Jacob l) Zero = let (Left v) = applyBin Mul rv (Left l) in Jacob v
    derBin Mul lv _ Zero (Jacob r) = let (Left v) = applyBin Mul lv (Left r) in Jacob v
    derBin Mul lv rv (Jacob l) (Jacob r) = let (Left v1) = applyBin Mul rv (Left l)
                                               (Left v2) = applyBin Mul lv (Left r)
                                           in Jacob (v1 + v2)

    derBin Div _ rv (Jacob l) Zero = let v = applyBin Mul rv (Left l)
                                         (Left res) = applyBin Div v (applyBin Mul rv rv)
                                     in Jacob res
    derBin Div lv rv Zero (Jacob r) = let v = applyBin Mul lv (Left r)
                                          (Left res) = applyBin Div v (applyBin Mul rv rv)
                                      in Jacob (negate res)
    derBin Div lv rv (Jacob l) (Jacob r) = let v1 = applyBin Mul rv (Left l)
                                               v2 = applyBin Mul lv (Left r)
                                               v3 = applyBin Sub v1 v2
                                               v4 = applyBin Mul rv rv
                                               (Left v5) = applyBin Div v3 v4
                                           in Jacob v5
    -- (lv ** (rv - 1) * ((rv - l) + lv * log lv * r))
    -- lv ^ (rv-1) * (rv-l)
    derBin Power lv rv (Jacob l) Zero = let rv1 = applyBin Sub rv (Right 1)
                                            lvr = applyBin Power lv rv1
                                            rvl = applyBin Sub rv (Left l)
                                            (Left v) = applyBin Mul lvr rvl
                                        in Jacob v
    -- lvr * (rv + lv * log lv * r)
    derBin Power lv rv Zero (Jacob r) = let rv1 = applyBin Sub rv (Right 1)
                                            lvr = applyBin Power lv rv1
                                            lvl = applyBin Mul lv (applyBin Mul (applyUni Log lv) (Left r))
                                            rvl = applyBin Add rv lvl
                                            (Left v) = applyBin Mul lvr rvl
                                        in Jacob v
    derBin Power lv rv (Jacob l) (Jacob r) = let rv1 = applyBin Sub rv (Right 1)
                                                 lvr = applyBin Power lv rv1
                                                 lvl = applyBin Mul lv (applyBin Mul (applyUni Log lv) (Left r))
                                                 rvl = applyBin Add (applyBin Sub rv (Left l)) lvl
                                                 (Left v) = applyBin Mul lvr rvl
                                             in Jacob v
                                           {-}
    alg (Var ix) = Left (xss <! ix)
    alg (Const c) = Right $ c
    alg (Param ix) = Right $ theta ! ix
    alg (Uni f (Left t)) = Left $ M.map (evalFun f) t
    alg (Uni f (Right t)) = Right $ evalFun f t
    alg (Bin op l r) = case l of
                         Right cl -> case r of
                                       Right cr -> Right $ evalOp op cl cr
                                       Left  vr -> Left $ M.map (evalOp op cl) vr
                         Left  vl -> case r of
                                       Right cr -> Left $ M.map (\c -> evalOp op c cr) vl
                                       Left  vr -> Left $ evalOp op vl vr
                                       -}
-- | The function `forwardModeUnique` calculates the numerical gradient of the tree and evaluates the tree at the same time. It assumes that each parameter has a unique occurrence in the expression. This should be significantly faster than `forwardMode`.
forwardModeUnique  :: SRMatrix -> PVector -> Fix SRTree -> (SRVector, [Array D Ix1 Double])
forwardModeUnique xss theta = second (DL.toList) . cata alg
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

    
data TupleF a b = Single a | T a b | Branch a b b deriving Functor -- hi, I'm a tree
type Tuple a = Fix (TupleF a)

-- | Same as above, but using reverse mode, that is much faster.
reverseModeUnique  :: SRMatrix -> PVector -> Fix SRTree -> (Array D Ix1 Double, [Array D Ix1 Double])
reverseModeUnique xss theta t = (getTop fwdMode, DL.toList g)
  where
      fwdMode = cata forward t
      g       = accu reverse (combine) t (one, fwdMode)
      one     = replicateAs xss 1
      (Sz2 m _) = M.size xss
      (Sz p)  = M.size theta
      --jacob   = M.replicate (getComp xss) (Sz2 m p) 0

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
      diff Div dx fx gy = (dx / gy, dx * ((-fx)/(gy*gy)))
      diff Power dx fx gy = let dxl = dx * fx ** (gy - one)
                                dv2 = fx * log fx
                             in (dxl * gy, dxl * dv2)


      -- once we reach a leaf with a parameter, we return a singleton
      -- with that derivative upwards until the root
      combine (Var ix)     s = DL.empty
      combine (Param ix)   s = DL.singleton $ fst s
      combine (Const c)    s = DL.empty
      combine (Uni _ gs)   s = gs
      combine (Bin op l r) s = DL.append l r

reverseModeUniqueV2 :: SRMatrix -> PVector -> Fix SRTree -> (Array D Ix1 Double, Array S Ix2 Double)
reverseModeUniqueV2 xss theta t = unsafePerformIO $ do
                                     mutJacob <- M.newMArray (Sz2 m p) 0
                                     let v = fromLeft $ getTop fwdMode
                                         d = accu reverse (combine mutJacob) t ((Right 1), fwdMode)
                                     jacob <- M.freeze (getComp xss) mutJacob
                                     pure (v, jacob)


  where
      fwdMode = cata forward t
      (Sz2 m _) = M.size xss
      (Sz p)  = M.size theta
      fromLeft (Left x) = x
      fromLeft (Right x) = M.replicate (getComp xss) (Sz1 m) x

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
      forward (Var ix)     = oneTpl (Left $ xss <! ix)
      forward (Param ix)   = oneTpl (Right $ theta ! ix)
      forward (Const c)    = oneTpl (Right c)
      forward (Uni g t)    = let v = getTop t
                             in tuple (applyUni g v) t
      forward (Bin op l r) = let vl = getTop l
                                 vr = getTop r
                              in branch (applyBin op vl vr) l r

      applyUni f (Left t)  = Left $ M.map (evalFun f) t
      applyUni f (Right t) = Right $ evalFun f t
      applyDer f (Left t)  = Left $ M.map (derivative f) t
      applyDer f (Right t) = Right $ derivative f t
      negate' (Left t) = Left $ M.map negate t
      negate' (Right t) = Right $ negate t

      applyBin op (Left ly) (Left ry) = Left $ case op of
                                               Add -> ly !+! ry
                                               Sub -> ly !-! ry
                                               Mul -> ly !*! ry
                                               Div -> ly !/! ry
                                               Power -> ly .** ry
      applyBin op (Left ly) (Right ry) = Left $ unsafeLiftArray (\ x -> evalOp op x ry) ly
      applyBin op (Right ly) (Left ry) = Left $ unsafeLiftArray (\ x -> evalOp op ly x) ry
      applyBin op (Right ly) (Right ry) = Right $ evalOp op ly ry

      -- reverse walks from the root to the leaf calculating the
      -- partial derivative with respect to an arbitrary variable
      -- up to that point
      reverse (Var ix)     (dx,   _)        = Var ix
      reverse (Param ix)   (dx,   _)        = Param ix
      reverse (Const v)    (dx,   _)        = Const v
      reverse (Uni f t)    (dx, unCons -> v) =
          let g'  = applyDer f (getTop v)
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
      combine :: MArray RealWorld S Ix2 Double -> SRTree val -> (Either (Array D Int Double) Double, b) -> ()
      combine j (Param ix)   s = unsafePerformIO $ do
                                                   case fst s of
                                                        Left v -> do
                                                                  let v' = computeAs S v
                                                                  forM_ [0 .. m-1] $ \i -> do

                                                                    let vi = v' ! i
                                                                    UMA.unsafeWrite j (i :. ix) vi
                                                        Right v -> forM_ [0 .. m-1] $ \i -> do
                                                                     UMA.unsafeWrite j (i :. ix) v
                                                   pure ()
      combine j _   s = ()

reverseModeUniqueV3 :: SRMatrix -> PVector -> SRVector -> Fix SRTree -> (Array D Ix1 Double, Array S Ix1 Double)
reverseModeUniqueV3 xss theta err t =  let jacob = M.replicate (getComp xss) (Sz1 m) 0
                                           v = fromLeft $ getTop fwdMode
                                           _ = accu reverse (combine jacob) t ((Right 1), fwdMode)
                                       in (v, jacob)
  where
      fwdMode = cata forward t
      (Sz2 m _) = M.size xss
      (Sz p)  = M.size theta
      fromLeft (Left x) = x
      fromLeft (Right x) = M.replicate (getComp xss) (Sz1 m) x
      --jacob = accu reverse combine t ((Right 1), fwdMode)

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
      forward (Var ix)     = oneTpl (Left $ xss <! ix)
      forward (Param ix)   = oneTpl (Right $ theta ! ix)
      forward (Const c)    = oneTpl (Right c)
      forward (Uni g t)    = let v = getTop t
                             in tuple (applyUni g v) t
      forward (Bin op l r) = let vl = getTop l
                                 vr = getTop r
                              in branch (applyBin op vl vr) l r

      applyUni f (Left t)  = Left $ M.map (evalFun f) t
      applyUni f (Right t) = Right $ evalFun f t
      applyDer f (Left t)  = Left $ M.map (derivative f) t
      applyDer f (Right t) = Right $ derivative f t
      negate' (Left t) = Left $ M.map negate t
      negate' (Right t) = Right $ negate t

      applyBin op (Left ly) (Left ry) = Left $ case op of
                                               Add -> ly !+! ry
                                               Sub -> ly !-! ry
                                               Mul -> ly !*! ry
                                               Div -> ly !/! ry
                                               Power -> ly .** ry
      applyBin op (Left ly) (Right ry) = Left $ unsafeLiftArray (\ x -> evalOp op x ry) ly
      applyBin op (Right ly) (Left ry) = Left $ unsafeLiftArray (\ x -> evalOp op ly x) ry
      applyBin op (Right ly) (Right ry) = Right $ evalOp op ly ry

      -- reverse walks from the root to the leaf calculating the
      -- partial derivative with respect to an arbitrary variable
      -- up to that point
      reverse (Var ix)     (dx,   _)        = Var ix
      reverse (Param ix)   (dx,   _)        = Param ix
      reverse (Const v)    (dx,   _)        = Const v
      reverse (Uni f t)    (dx, unCons -> v) =
          let g'  = applyDer f (getTop v)
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
      --combine :: SRTree val -> (Either (Array D Int Double) Double, b) -> DL.DList Double
      combine j (Param ix) s = runST $ do
                                 j' <- UMA.unsafeThaw j
                                 case fst s of
                                   Left v  -> do v' <- dotM v err
                                                 UMA.unsafeWrite j' ix v'
                                   Right v -> UMA.unsafeWrite j' ix $ M.foldrS (\x acc -> x*v + acc) 0 err
                                 pure ()
      combine _ _ _ = ()
