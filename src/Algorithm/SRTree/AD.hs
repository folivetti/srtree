{-# language FlexibleInstances, DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
{-# language FlexibleContexts #-}
{-# language BangPatterns #-}
{-# language TypeApplications #-}
{-# language MultiWayIf #-}

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
         , reverseModeEGraph
         , reverseModeGraph
         , forwardModeUniqueJac
         , evalCache
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
import Data.Maybe ( fromJust, isJust )
import Algorithm.EqSat.Egraph

import Control.Monad.State.Strict
import Control.Monad.Identity

--import UnliftIO.Async

import qualified Data.Map.Strict as Map

evalCache :: SRMatrix -> EGraph -> ECache -> EClassId -> VS.Vector Double -> ECache
evalCache xss egraph cache root' theta = cache'
    where
        (Sz2 _ m') = M.size xss
        m    = Sz1 m'
        root = canon root'
        p    = VS.length theta
        comp = M.getComp xss
        one :: Array S Ix1 Double
        one  = M.replicate comp m 1

        canon rt = case _canonicalMap egraph IntMap.!? rt of
                     Nothing -> error "wrong canon"
                     Just rt' -> if rt == rt' then rt else canon rt'

        getNode rt' = let rt  = canon rt'
                          cls = _eClass egraph IntMap.! rt
                      in (_best . _info) cls

        getId n' = let n = runIdentity $ canonize n' `evalStateT` egraph
                   in traceShow (n, n `Map.member` _eNodeToEClass egraph ) $ _eNodeToEClass egraph Map.! n

        ((cache', localcache), _) = evalCached root `execState` ((cache, IntMap.empty), Map.empty)
           where
            evalCached :: EClassId -> State ((ECache, ECache), Map.Map ENode PVector) (PVector, Bool)
            evalCached rt = insertKey rt

        insertKey :: EClassId -> State ((ECache, ECache), Map.Map ENode PVector) (PVector, Bool)
        insertKey key = do
            isCachedGlobal <- gets ((key `IntMap.member`) . fst . fst)
            isCachedLocal  <- gets ((key `IntMap.member`) . snd . fst)
            when (not isCachedLocal && not isCachedGlobal) $ do
                let node = getNode key
                (ev, toLocal) <- evalKey node
                modify' (insKey node ev toLocal)
            getVal key

        evalKey :: ENode -> State ((ECache, ECache), Map.Map ENode PVector) (PVector, Bool)
        evalKey (Var ix)     = pure $ (M.computeAs S $ xss <! ix, False)
        evalKey (Const v)    = pure $ (M.replicate comp m v, False)
        evalKey (Param ix)   = pure $ (M.replicate comp m (theta VS.! ix), True)
        evalKey (Uni f t)    = do (v, b) <- getVal t
                                  pure $ (M.computeAs S . M.map (evalFun f) $ v, b)
        evalKey (Bin op l r) = do (vl, bl) <- getVal l
                                  (vr, br) <- getVal r
                                  pure $ (M.computeAs S $ M.zipWith (evalOp op) vl vr, bl || br)

        insKey (Var   _) _ _       s = s
        insKey (Const _) _ _       s = s
        insKey (Param _) _ _       s = s
        insKey node      v toLocal ((global,local), s) =
            let k = getId node
            in if toLocal
                  then ((global, IntMap.insert k v local), s)
                  else ((IntMap.insert k v global, local), s)

        insertLocal k v = do (c1, c2) <- get
                             put (c1, IntMap.insert k v c2)
        insertGlobal k v = do (c1, c2) <- get
                              put (IntMap.insert k v c1, c2)
        getVal rt' = do let rt = canon rt'
                            n  = getNode rt
                        case n of
                          Var ix   -> evalKey n
                          Const v  -> evalKey n
                          Param ix -> evalKey n
                          _        -> getFromCache rt
        getFromCache rt = do
            global <- gets ((IntMap.!? rt) . fst . fst)
            local  <- gets ((IntMap.!? rt) . snd . fst)
            if | isJust global -> pure (fromJust global, False)
               | isJust local  -> pure (fromJust local, True)
               | otherwise     -> insertKey rt

-- reverse mode applied directly on an e-graph. Supports caching.
-- assumes root points to the loss function, so for an expression
-- f(x) and the loss (y - (f(x))^2), root will point to "^"
reverseModeEGraph :: SRMatrix -> PVector -> Maybe PVector -> EGraph -> ECache -> EClassId -> VS.Vector Double -> (Array D Ix1 Double, VS.Vector Double)
reverseModeEGraph xss ys mYErr egraph cache root' theta = traceShow (IntMap.keys cache, Map.keys cachedGrad, p) $
    (delay $ rootVal
    , VS.fromList [M.sum $ cachedGrad Map.! (Param ix) | ix <- [0..p-1]]
    )
    where
        rootVal = extractCache (cache'' IntMap.!? root', localcache' IntMap.!? root')
        root = canon root'
        yErr = fromJust mYErr
        m    = M.size ys
        p    = VS.length theta
        comp = M.getComp xss
        one :: Array S Ix1 Double
        one  = M.replicate comp m 1

        canon rt = case _canonicalMap egraph IntMap.!? rt of
                     Nothing -> error "wrong canon"
                     Just rt' -> if rt == rt' then rt else canon rt'

        getNode rt' = let rt  = canon rt'
                          cls = _eClass egraph IntMap.! rt
                      in (_best . _info) cls

        getId n' = let n = runIdentity $ canonize n' `evalStateT` egraph
                   in _eNodeToEClass egraph Map.! n

        ((cache', localcache), _) = evalCached root `execState` ((cache, IntMap.empty), Map.empty)
           where
            evalCached :: EClassId -> State ((ECache, ECache), Map.Map ENode PVector) (PVector, Bool)
            evalCached rt = insertKey rt

        insertKey :: EClassId -> State ((ECache, ECache), Map.Map ENode PVector) (PVector, Bool)
        insertKey key = do
            isCachedGlobal <- gets ((key `IntMap.member`) . fst . fst)
            isCachedLocal  <- gets ((key `IntMap.member`) . snd . fst)
            when (not isCachedLocal && not isCachedGlobal) $ do
                let node = getNode key
                (ev, toLocal) <- evalKey node
                modify' (insKey node ev toLocal)
            getVal key

        evalKey :: ENode -> State ((ECache, ECache), Map.Map ENode PVector) (PVector, Bool)
        evalKey (Var ix)     = pure $ if | ix == -1  -> (ys, False)
                                         | ix == -2  -> (yErr, False)
                                         | otherwise -> (M.computeAs S $ xss <! ix, False)
        evalKey (Const v)    = pure $ (M.replicate comp m v, False)
        evalKey (Param ix)   = pure $ (M.replicate comp m (theta VS.! ix), True)
        evalKey (Uni f t)    = do (v, b) <- getVal t
                                  pure $ (M.computeAs S . M.map (evalFun f) $ v, b)
        evalKey (Bin op l r) = do (vl, bl) <- getVal l
                                  (vr, br) <- getVal r
                                  pure $ (M.computeAs S $ M.zipWith (evalOp op) vl vr, bl || br)

        insKey (Var   _) _ _       s = s
        insKey (Const _) _ _       s = s
        insKey (Param _) _ _       s = s
        insKey node      v toLocal ((global,local), s) =
            let k = getId node
            in if toLocal
                  then ((global, IntMap.insert k v local), s)
                  else ((IntMap.insert k v global, local), s)

        insertLocal k v = do (c1, c2) <- get
                             put (c1, IntMap.insert k v c2)
        insertGlobal k v = do (c1, c2) <- get
                              put (IntMap.insert k v c1, c2)
        getVal rt' = do let rt = canon rt'
                            n  = getNode rt
                        case n of
                          Var ix   -> evalKey n
                          Const v  -> evalKey n
                          Param ix -> evalKey n
                          _        -> getFromCache rt
        getFromCache rt = do
            global <- gets ((IntMap.!? rt) . fst . fst)
            local  <- gets ((IntMap.!? rt) . snd . fst)
            if | isJust global -> pure (fromJust global, False)
               | isJust local  -> pure (fromJust local, True)
               | otherwise     -> insertKey rt

        extractCache (Nothing, Nothing) = error "no root info"
        extractCache (Just r, _) = r
        extractCache (_, Just r) = r

        ((cache'', localcache'), cachedGrad) = calcGrad root one `execState` ((cache', localcache), Map.empty)

        calcGrad :: Int -> Array S Ix1 Double -> State ((IntMap.IntMap (Array S Ix1 Double), IntMap.IntMap (Array S Ix1 Double)), Map.Map (SRTree Int) (Array S Ix1 Double)) ()
        calcGrad rt v = do let node = getNode rt
                           case node of
                              Bin op l r -> do xl <- fst <$> getVal l
                                               xr <- fst <$> getVal r
                                               (dl, dr) <- diff op v xl xr l r
                                               calcGrad l dl
                                               calcGrad r dr
                              Uni f  t   -> do x <- fst <$> getVal t
                                               calcGrad t (M.computeAs S $ M.zipWith (*) v (M.map (derivative f) x))
                              Param ix   -> modify' (insertGrad v (Param ix))
                              _          -> pure ()
          where
            insertGrad v k ((a, b), g) = ((a, b), Map.insertWith (\v1 v2 -> M.computeAs S $ M.zipWith (+) v1 v2) k v g)

        --diff :: Op -> Array S Ix1 Double -> Array S Ix1 Double -> Array S Ix1 Double -> (Array S Ix1 Double, Array S Ix1 Double)
        diff Add dx fx gy l r   = pure (dx, dx)
        diff Sub dx fx gy l r   = pure (dx, M.computeAs S $ M.map negate dx)
        diff Mul dx fx gy l r   = pure (M.computeAs S $ M.zipWith (*) dx gy, M.computeAs S $ M.zipWith (*) dx fx)
        diff Div dx fx gy l r   = do
            let k = getId (Bin Div l r)
            v <- fst <$> getVal k
            pure (M.computeAs S $ M.zipWith (/) dx gy
                 , M.computeAs S $ M.zipWith (*) dx (M.zipWith (\l r -> negate l/r) v gy))
        diff Power dx fx gy l r = do
            let k = getId (Bin Power l r)
            v <- fst <$> getVal k
            pure ( M.computeAs S $ M.zipWith4 (\d f g vi -> fixNaN $ d * g * vi / f) dx fx gy v
                 , M.computeAs S $ M.zipWith3 (\d f vi -> fixNaN $ d * vi * log f) dx fx v)

        diff PowerAbs dx fx gy l r = do
            let k = getId (Bin PowerAbs l r)
            v <- fst <$> getVal k
            let v2 = M.map abs fx
                v3 = M.computeAs S $ M.zipWith (*) fx gy
            pure ( M.computeAs S $ M.zipWith4 (\d v3i vi v2i -> fixNaN $ d * v3i * vi / (v2i^2)) dx v3 v v2
                 , M.computeAs S $ M.zipWith3 (\d f vi -> fixNaN $ d * vi * log f) dx v2 v)

        diff AQ dx fx gy l r = let dxl = M.zipWith (\g d -> d * (recip . sqrt . (+1) . (^2)) g) gy dx
                                   dxy = M.zipWith3 (\f g dl -> f * g * dl^3) fx gy dxl
                           in pure (M.computeAs S $ dxl, M.computeAs S $ dxy)

        fixNaN x = if isNaN x then 0 else x


reverseModeGraph :: SRMatrix -> PVector -> Maybe PVector -> VS.Vector Double -> Fix SRTree -> (Array D Ix1 Double, VS.Vector Double)
reverseModeGraph xss ys mYErr theta tree = (delay $ cachedVal' IntMap.! root
                                            , VS.fromList [M.sum $ cachedGrad Map.! (Param ix) | ix <- [0..p-1]])
    where
        yErr = fromJust mYErr
        --ys   = delay ys'
        m    = M.size ys
        p    = VS.length theta
        comp = M.getComp xss
        one :: Array S Ix1 Double
        one  = M.replicate comp m 1
        (key2int, int2key, cachedVal, (subtract 1) -> root) = cataM leftToRight alg tree `execState` (Map.empty, IntMap.empty, IntMap.empty, 0)
        (key2int', int2key', cachedVal', cachedGrad) = calcGrad root one `execState` (key2int, int2key, cachedVal, Map.empty)

        calcGrad :: Int -> Array S Ix1 Double -> State (Map.Map (SRTree Int) Int, IntMap.IntMap (SRTree Int), IntMap.IntMap (Array S Ix1 Double), Map.Map (SRTree Int) (Array S Ix1 Double)) ()
        calcGrad key v = do node <- gets ((IntMap.! key) . _int2key)
                            case node of
                              Bin op l r -> do xl <- gets (getVal l)
                                               xr <- gets (getVal r)
                                               (dl, dr) <- diff op v xl xr l r
                                               calcGrad l dl
                                               calcGrad r dr
                              Uni f  t   -> do x <- gets (getVal t)
                                               calcGrad t (M.computeAs S $ M.zipWith (*) v (M.map (derivative f) x))
                              Param ix   -> modify' (insertGrad v (Param ix))
                              _          -> pure ()
          where
            _int2key (_, b, _, _) = b
            insertGrad v k (a, b, c, g) = (a, b, c, Map.insertWith (\v1 v2 -> M.computeAs S $ M.zipWith (+) v1 v2) k v g)

        graph (a, _, _, _) = a
        insKey key ev (a, b, c, d) = (Map.insert key d a, IntMap.insert d key b, IntMap.insert d ev c, d+1)
        -- get the values from the cache
        getVal key (a, b, c, d)    = c IntMap.! key
        -- maps the the struct to an integer key
        getKey key (a, b, c, d)    = a Map.! key

        -- this tells the order in which we traverse the tree
        leftToRight (Uni f mt)    = Uni f <$> mt;
        leftToRight (Bin f ml mr) = Bin f <$> ml <*> mr
        leftToRight (Var ix)      = pure (Var ix)
        leftToRight (Param ix)    = pure (Param ix)
        leftToRight (Const c)     = pure (Const c)

        evalKey (Var ix) = pure $ if ix == -1
                                    then ys
                                    else if ix == -2
                                            then yErr
                                            else M.computeAs S $ xss <! ix
        evalKey (Const v)  = pure $ M.replicate comp m v
        evalKey (Param ix) = pure $ M.replicate comp m (theta VS.! ix)
        evalKey (Uni f t)  = M.computeAs S . M.map (evalFun f) <$> gets (getVal t)
        evalKey (Bin op l r) = M.computeAs S <$> (M.zipWith (evalOp op) <$> gets (getVal l) <*> gets (getVal r))

        alg (Var ix) = insertKey (Var ix)
        alg (Param ix) = insertKey (Param ix)
        alg (Const v) = insertKey (Const v)
        alg (Uni f t) = insertKey (Uni f t)
        alg (Bin op l r) = insertKey (Bin op l r)

        --diff :: Op -> Array S Ix1 Double -> Array S Ix1 Double -> Array S Ix1 Double -> (Array S Ix1 Double, Array S Ix1 Double)
        diff Add dx fx gy l r   = pure (dx, dx)
        diff Sub dx fx gy l r   = pure (dx, M.computeAs S $ M.map negate dx)
        diff Mul dx fx gy l r   = pure (M.computeAs S $ M.zipWith (*) dx gy, M.computeAs S $ M.zipWith (*) dx fx)
        diff Div dx fx gy l r   = do
            k <- gets (getKey (Bin Div l r))
            v <- gets (getVal k)
            pure (M.computeAs S $ M.zipWith (/) dx gy
                 , M.computeAs S $ M.zipWith (*) dx (M.zipWith (\l r -> negate l/r) v gy))
        diff Power dx fx gy l r = do
            k <- gets (getKey (Bin Power l r))
            v <- gets (getVal k)
            pure ( M.computeAs S $ M.zipWith4 (\d f g vi -> fixNaN $ d * g * vi / f) dx fx gy v
                 , M.computeAs S $ M.zipWith3 (\d f vi -> fixNaN $ d * vi * log f) dx fx v)

        diff PowerAbs dx fx gy l r = do
            k <- gets (getKey (Bin PowerAbs l r))
            v <- gets (getVal k)
            let v2 = M.map abs fx
                v3 = M.computeAs S $ M.zipWith (*) fx gy
            pure ( M.computeAs S $ M.zipWith4 (\d v3i vi v2i -> fixNaN $ d * v3i * vi / (v2i^2)) dx v3 v v2
                 , M.computeAs S $ M.zipWith3 (\d f vi -> fixNaN $ d * vi * log f) dx v2 v)

        diff AQ dx fx gy l r = let dxl = M.zipWith (\g d -> d * (recip . sqrt . (+1) . (^2)) g) gy dx
                                   dxy = M.zipWith3 (\f g dl -> f * g * dl^3) fx gy dxl
                           in pure (M.computeAs S $ dxl, M.computeAs S $ dxy)

        fixNaN x = if isNaN x then 0 else x

        insertKey key = do
            isCached <- gets ((key `Map.member`) . graph)
            when (not isCached) $ do
                ev <- evalKey key
                modify' (insKey key ev)
            gets (getKey key)

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
                stps = 2
                --delta = m `div` stps
                --rngs  = [(i*delta, min m $ (i+1)*delta) | i <- [0..stps] ]
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
      eps       = 1e-8

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

      --f(x)^g(x)
      --d f(x)^g(x) / d f(x) = f(x)^(g(x)-1)
      -- f(x) + g(x) = 1, 1
      -- f(x) - g(x) = 1, -1
      -- f(x) * g(x) = g(x), f(x)
      -- f(x) / g(x) = 1/g(x), -f(x)/g(x)^2
      -- f(x) ^ g(x) = g(x) * f(x) ^ (g(x) - 1), f(x) ^ g(x) * log f(x)
      -- |f(x)| ^ g(x) = g(x) * |f(x)| ^ (g(x) - 2) * f(x), |f(x)| ^ g(x) * log |f(x)|

      -- |f(x)| ^ g(x) = exp (log |f(x)| * g(x))
      --       => |f(x)| ^ (g(x) - 1) * g(x)
      --       => |f(x)| ^ g(x) * log |f(x)| * 1

      fixNaN x | isNaN x = 0
               | otherwise = x

      diff :: Op -> Double -> Double -> Double -> (Double, Double)
      diff Add dx fx gy   = (dx, dx)
      diff Sub dx fx gy   = (dx, negate dx)
      diff Mul dx fx gy   = (dx * gy, dx * fx)
      diff Div dx fx gy   = (dx / gy, dx * (negate fx / (gy * gy)))
      --diff Power dx fx gy = (fixNaN $ dx * ((fx+eps)**gy - fx**gy)/eps, fixNaN $ dx * (fx**(gy+eps) - fx**gy)/eps)
      --diff PowerAbs dx fx gy = (fixNaN $ dx * (abs (fx+eps)**gy - abs fx**gy)/eps, fixNaN $ dx * (abs fx**(gy+eps) - abs fx**gy)/eps)
      {--}
      diff Power 0 _ _    = (0, 0)
      diff Power dx 0  0  = (0, 0)
      diff Power dx fx 0  = (0, fixNaN $ dx * log fx)
      diff Power dx 0 gy  = (fixNaN $ dx * gy * if gy < 1 then eps ** (gy - 1) else 0
                            , 0) --dx * fx ** gy * log fx)
      diff Power dx fx gy = (fixNaN $ dx * gy * fx ** (gy - 1), fixNaN $ dx * fx ** gy * log fx)

      diff PowerAbs 0 fx gy  = (0, 0)
      diff PowerAbs 0  0  0  = (0, 0)
      diff PowerAbs dx fx 0  = (0, fixNaN $ dx * log (abs fx))
      diff PowerAbs dx 0 gy  = (0, fixNaN $ dx * if gy < 0 then eps ** gy else 0)
      diff PowerAbs dx fx gy = (fixNaN $ dx * gy * fx * abs fx ** (gy - 2), fixNaN $ dx * abs fx ** gy * log (abs fx))
      {--}
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
