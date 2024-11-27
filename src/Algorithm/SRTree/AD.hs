{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
{-# language FlexibleContexts #-}
{-# language BangPatterns #-}
{-# language TypeApplications #-}

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
         ( reverseModeArr
         , forwardModeUniqueJac
         ) where

import Control.Monad (forM_, foldM, when)
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
import qualified Data.IntMap.Strict as IntMap
import Data.List ( foldl' )
import qualified Data.Vector.Storable as VS
import Control.Scheduler 
import Data.Maybe ( fromJust )
--import UnliftIO.Async

-- | Same as above, but using reverse mode with the tree encoded as an array, that is even faster.
reverseModeArr :: SRMatrix
                  -> PVector
                  -> Maybe PVector
                  -> VS.Vector Double -- PVector
                  -> [(Int, (Int, Int, Int, Double))] -- arity, opcode, ix, const val
                  -> IntMap.IntMap Int
                  -> (Array D Ix1 Double, Array S Ix1 Double)
reverseModeArr xss ys mYErr theta t j2ix =
      unsafePerformIO $ do
            fwd     <- M.newMArray (Sz2 n m) 0
            partial <- M.newMArray (Sz2 n m) 0
            jacob   <- M.newMArray (Sz p) 0
            val     <- M.newMArray (Sz m) 0
            let
                stps = 4
                delta = m `div` stps
                rngs  = [(i*delta, min m $ (i+1)*delta) | i <- [0..stps] ]
                (a, b) = (0, m)

            forward (a, b) fwd
            calculateYHat (a, b) fwd val
            reverseMode (a, b) fwd partial
            combine (a, b) partial jacob
            j <- UMA.unsafeFreeze (getComp xss) jacob
            v <- UMA.unsafeFreeze (getComp xss) val
            pure (delay v, j)

  where
      (Sz2 m _) = M.size xss
      p         = VS.length theta
      n         = length t
      toLin i j = i*m + j
      yErr      = fromJust mYErr

      myForM_ [] _ = pure ()
      myForM_ (!x:xs) f = do f x
                             myForM_ xs f
      {-# INLINE myForM_ #-}

      calculateYHat :: (Int, Int) -> MArray (PrimState IO) S Ix2 Double -> MArray (PrimState IO) S Ix1 Double -> IO ()
      calculateYHat (a, b) fwd yhat = myForM_ [a..b-1] $ \i -> do
          vi <- UMA.unsafeRead fwd (0 :. i)
          UMA.unsafeWrite yhat i vi
      {-# INLINE calculateYHat #-}

      forward :: (Int, Int) -> MArray (PrimState IO) S Ix2 Double -> IO ()
      forward (a, b) fwd = do
          let t' = Prelude.reverse t
          myForM_ t' makeFwd
         where
          makeFwd (j, (0, 0, ix, _)) =
              do let j' = j2ix IntMap.! j
                 myForM_ [a..b-1] $ \i -> do
                 --let val = xss M.! (i :. ix)
                     UMA.unsafeWrite fwd (j' :. i) $ case ix of
                                                        (-1) -> ys M.! i
                                                        (-2) -> yErr M.! i
                                                        _    -> xss M.! (i :. ix)
          makeFwd (j, (0, 1, ix, _))     = do let j' = j2ix IntMap.! j
                                                  v  = theta VS.! ix
                                              myForM_ [a..b-1] $ \i -> do
                                                  UMA.unsafeWrite fwd (j' :. i) v
          makeFwd (j, (0, 2, _, x))      = do let j' = j2ix IntMap.! j
                                              myForM_ [a..b-1] $ \i -> do
                                                  UMA.unsafeWrite fwd (j' :. i) x
          makeFwd (j, (1, f, _, _))      = do let j' = j2ix IntMap.! j
                                                  j2 = j2ix IntMap.! (2*j + 1)
                                              myForM_ [a..b-1] $ \i -> do
                                                v <- UMA.unsafeRead fwd (j2 :. i)
                                                UMA.unsafeWrite fwd (j' :. i) (evalFun (toEnum f) v)
          makeFwd (j, (2, op, _, _))     = do let j' = j2ix IntMap.! j
                                                  j2 = j2ix IntMap.! (2*j + 1)
                                                  j3 = j2ix IntMap.! (2*j + 2)
                                              myForM_ [a..b-1] $ \i -> do
                                                l <- UMA.unsafeRead fwd (j2 :. i)
                                                r <- UMA.unsafeRead fwd (j3 :. i)
                                                UMA.unsafeWrite fwd (j' :. i) (evalOp (toEnum op) l r)
          makeFwd _ = pure ()
          {-# INLINE makeFwd #-}
      {-# INLINE forward #-}

      reverseMode :: (Int, Int) -> MArray (PrimState IO) S Ix2 Double -> MArray (PrimState IO) S Ix2 Double -> IO ()
      reverseMode (a, b) fwd partial =
          do myForM_ [a..b-1] $ \i -> UMA.unsafeWrite partial (0 :. i) 1
             myForM_ t makeRev
        where
          makeRev (j, (1, f, _, _)) = do let dxj = j2ix IntMap.! j
                                             vj  = j2ix IntMap.! (2*j + 1)
                                         myForM_ [a..b-1] $ \i -> do
                                           v <- UMA.unsafeRead fwd (vj :. i)
                                           dx <- UMA.unsafeRead partial  (dxj :. i)
                                           --let val = dx * derivative (toEnum f) v
                                           UMA.unsafeWrite partial (vj :. i) (dx * derivative (toEnum f) v)
          makeRev (j, (2, op, _, _)) = do let dxj = j2ix IntMap.! j
                                              lj  = j2ix IntMap.! (2*j + 1)
                                              rj  = j2ix IntMap.! (2*j + 2)
                                          myForM_ [a..b-1] $ \i -> do
                                            l <- UMA.unsafeRead fwd (lj :. i)
                                            r <- UMA.unsafeRead fwd (rj :. i)
                                            dx <- UMA.unsafeRead partial  (dxj :. i)
                                            let (dxl, dxr) = diff (toEnum op) dx l r
                                            UMA.unsafeWrite partial (lj :. i) dxl
                                            UMA.unsafeWrite partial (rj :. i) dxr
          makeRev _ = pure ()
          {-# INLINE makeRev  #-}
      {-# INLINE reverseMode #-}

      diff :: Op -> Double -> Double -> Double -> (Double, Double)
      diff Add dx fx gy = (dx, dx)
      diff Sub dx fx gy = (dx, negate dx)
      diff Mul dx fx gy = (dx * gy, dx * fx)
      diff Div dx fx gy = (dx / gy, dx * (negate fx / (gy * gy)))
      diff Power dx fx gy = let dxl = dx * (fx ** (gy-1))
                                dv2 = fx * log fx
                            in (dxl * gy, dxl * dv2)
      diff PowerAbs dx fx gy = let dxl = (gy * fx) * (abs fx ** (gy - 2))
                                   dxr = (log (abs fx)) * (abs fx ** gy)
                               in (dxl * dx, dxr * dx)
      diff AQ dx fx gy = let dxl = recip ((sqrt . (+1)) (gy * gy))
                             dxy = fx * gy * (dxl^3) -- / (sqrt (gy*gy + 1))
                         in (dxl * dx, dxy * dx)
      {-# INLINE diff #-}

      combine ::  (Int, Int) -> MArray (PrimState IO) S Ix2 Double -> MArray (PrimState IO) S Ix1 Double -> IO ()
      combine (lo, hi) partial jacob  = myForM_ t makeJacob
        where
            makeJacob (j, (0, 1, ix, _)) = do val <- UMA.unsafeRead jacob ix
                                              let j' = j2ix IntMap.! j
                                                  addI a b acc = do v2 <- UMA.unsafeRead partial (b :. a)
                                                                    pure (v2 + acc)
                                              acc <- foldM (\a i -> addI i j' a) val [lo..hi-1]
                                              UMA.unsafeWrite jacob ix acc
            makeJacob _ = pure ()
      {-# INLINE combine #-}

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
