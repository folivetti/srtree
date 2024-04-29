{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleContexts #-}
module Algorithm.SRTree.NonlinearOpt where 

import qualified Data.Massiv.Array as MA
import qualified Data.Massiv.Array.Unsafe as UMA
import qualified Data.Massiv.Array.Mutable as MMA
import Data.Massiv.Array ( Array, S, Ix2(..), Ix1, dotM, (*.), (.*), (!.!), (!><), (.+.), (.-.), (.><.) )
import qualified Data.Massiv.Array.Unsafe as MA
import qualified Data.Massiv.Core.Operations as UMA
import Control.Monad ( forM_, when )
import Data.SRTree.Eval ( SRMatrix, PVector ) 
import Control.Monad.State 
import qualified Data.Map as M
import Debug.Trace ( traceShow )
import System.IO.Unsafe ( unsafePerformIO )

type MMassArray m = MMA.MArray (MA.PrimState m) S Ix2 Double

rangedLinearDotProd :: MA.PrimMonad m => Int -> Int -> Int -> MMassArray m -> m Double
rangedLinearDotProd r1 r2 len arr = go 0 0
  where
    go !acc k
      | k < len   = do x <- UMA.unsafeLinearRead arr (r1 + k)
                       y <- UMA.unsafeLinearRead arr (r2 + k)
                       go (acc + x*y) (k + 1)
      | otherwise = pure acc
{-# INLINE rangedLinearDotProd #-}

outer :: (MA.MonadThrow m)
  => PVector
  -> PVector
  -> m SRMatrix
outer arr1 arr2
  | MA.isEmpty arr1 || MA.isEmpty arr2 = pure $ MA.setComp comp MA.empty
  | otherwise =
      pure $ MA.makeArray comp (MA.Sz2 m1 m2) $ \(i :. j) ->
          UMA.unsafeIndex arr1 i * UMA.unsafeIndex arr2 j
  where
      comp = MA.getComp arr1 <> MA.getComp arr2
      MA.Sz1 m1 = MA.size arr1
      MA.Sz1 m2 = MA.size arr2
{-# INLINE outer #-}

cholesky :: (MA.PrimMonad m, MA.MonadThrow m)
  => SRMatrix
  -> m SRMatrix
cholesky arr
  | m /= n          = MA.throwM $ MA.SizeMismatchException (MA.size arr) (MA.size arr)
  | MA.isEmpty arr  = pure $ MA.setComp comp MA.empty
  | otherwise       = MMA.createArrayS_ (MA.size arr) create
  where
    comp         = MA.getComp arr
    (MA.Sz2 m n) = MA.size arr
    create l     = mapM_ (update l) [i :. j | i <- [0..m], j <- [0..m]]

    update l ix@(i :. j)
      | i < j     = UMA.unsafeWrite l ix 0
      | otherwise = do let cur  = UMA.unsafeIndex arr ix
                           rowI = i*m
                           rowJ = j*m
                       xjj <- UMA.unsafeLinearRead l (rowJ + j)
                       tot <- rangedLinearDotProd rowI rowJ j l
                       if i == j
                          then UMA.unsafeLinearWrite l (rowI + j) (sqrt (cur - tot))
                          else UMA.unsafeLinearWrite l (rowI + j) ((cur - tot) / xjj)
{-# INLINE cholesky #-}
invChol :: (MA.PrimMonad m, MA.MonadThrow m) => SRMatrix -> m SRMatrix
invChol arr = do l <- cholesky arr -- lower diag
                 mtx <- MA.thawS l
                 forM_ [0 .. m-1] $ \i -> do
                     lII <- UMA.unsafeRead mtx (i :. i)
                     UMA.unsafeWrite mtx (i :. i) (1 / lII)
                     forM_ [0 .. i-1] $ \j -> do
                         tot <- rangedLinearDotProd (i*m + j) (j*m + j) (i-j) mtx
                         UMA.unsafeWrite mtx (j :. i) ((-tot)/lII)
                         UMA.unsafeWrite mtx (i :. j) 0
                 mm <- MA.newMArray (MA.Sz2 m m) 0
                 forM_ [0 .. m-1] $ \i -> do
                     dii <- rangedLinearDotProd (i*m + i) (i*m + i) (m - i) mtx
                     UMA.unsafeWrite mm (i :. i) dii
                     forM_ [i+1 .. m-1] $ \j -> do
                          dij <- rangedLinearDotProd (i*m + j) (j*m + j) (m - j) mtx
                          UMA.unsafeWrite mm (i :. j) dij
                          UMA.unsafeWrite mm (j :. i) dij
                 MA.freezeS mm

  where
    MA.Sz2 m _ = MA.size arr
{-# INLINE invChol #-}


data LSData = LSData
    { _alpha :: Double
    , _phi   :: Double
    , _phi'  :: Double
    } deriving (Ord, Eq, Show)

type MSTLS m a = StateT (M.Map Double LSData) m a

getPhi :: Monad m => Double -> MSTLS m Double
getPhi a = gets (_phi . (!. a))
{-# INLINE getPhi #-}

getPhi' :: Monad m => Double -> MSTLS m Double
getPhi' a = gets (_phi' . (!. a))
{-# INLINE getPhi' #-}

m !. x = if isNaN x then LSData x x x else if M.member x m then m M.! x else error $ "not found: " <> show (m, x)

minimizeBFGS :: (MA.PrimMonad m, MA.MonadThrow m)
             => (PVector -> (Double, PVector))
             -> (PVector -> SRMatrix)
             -> Int
             -> Double 
             -> PVector
             -> m (PVector, Int)
minimizeBFGS funAndGrad hessian nIters tol theta0 =
    do -- h <- invChol (hessian theta0)
       let h = MA.computeAs MA.S $ MA.identityMatrix (MA.Sz p) -- hessian theta0
       go theta0 fk0 dfk0 h a0 nIters
  where
    (fk0, dfk0)  = funAndGrad theta0
    a0         = 1.0
    (MA.Sz p) = MA.size theta0
    i_mtx      = MA.computeAs MA.S $ MA.identityMatrix (MA.size theta0)
    m !>.< v   = MA.computeAs MA.S $ m !>< v
    runLS f    = f `evalStateT` M.empty

    go theta _  _   _ _ 0   = pure (theta, nIters)
    go theta fk dfk h a it 
      | isNaN a || isNaN fk = pure (theta, nIters - it)
      | otherwise = do
        gnorm <- dotM dfk dfk
        if gnorm < tol
           then pure (theta, nIters - it)
           else do let pk = MA.negateA h !>.< dfk
                   ak      <- runLS $ lineSearchWolfe funAndGrad theta pk 0.01 0.1 a 10 -- adjust parameters
                   theta_k <- theta .+. (ak *. pk)
                   let (fk_nxt, dfk_nxt) = funAndGrad theta_k
                   if abs (fk_nxt - fk) < tol
                      then pure (theta_k, nIters - it)
                      else do yk <- dfk_nxt .-. dfk
                              let sk   = ak *. pk
                                  ysk  = UMA.unsafeDotProduct yk sk
                                  rhok = 1 / max 10000 ysk 
                              sy    <- outer sk yk
                              ys    <- outer yk sk
                              ss    <- outer sk sk
                              a1    <- i_mtx .-. (sy .* rhok)
                              a2    <- i_mtx .-. (ys .* rhok)
                              ha2   <- h .><. a2
                              a1ha2 <- a1 .><. ha2
                              h_nxt <-  a1ha2 .+. (rhok *. ss)
                              go theta_k fk_nxt dfk_nxt h_nxt 1.0 (it-1)

minimizeCG :: (MA.PrimMonad m, MA.MonadThrow m)
           => (PVector -> (Double, PVector)) 
           -> Int 
           -> Double
           -> PVector 
           -> m (PVector, Int)
minimizeCG funAndGrad nIters tol theta0 = go theta0 pk0 fk0 dfk0 a0 nIters
  where
    (fk0, dfk0) = funAndGrad theta0
    pk0       = MA.negateA dfk0
    a0        = 1.0
    almost0   = MA.all (\d -> abs d <= tol)
    runLS f   = f `evalStateT` M.empty

    go !theta _  _  _   _ 0  = pure (theta, nIters)
    go !theta pk fk dfk a it
      | isNaN a || isNaN fk = pure (theta, nIters - it) 
      | otherwise = do
        if almost0 dfk
           then pure (theta, nIters - it)
           else do ak      <- runLS $ lineSearchWolfe funAndGrad theta pk 0.01 0.1 a 100 -- adjust parameters
                   theta_k <- theta .+. (ak *. pk)
                   let (fk_nxt, dfk_nxt) = funAndGrad theta_k
                       beta              = max 0 $ MA.sum $ MA.zipWith (\dk dkn -> dkn * (dkn - dk) / (dk * dk)) dfk dfk_nxt
                   pk_nxt <- beta *. pk .-. dfk_nxt
                   let dfkpk  = UMA.unsafeDotProduct dfk_nxt pk_nxt
                       a_nxt' = min 1 $ abs $ 2.02 * (fk - fk_nxt) / dfkpk
                       a_nxt  = if a_nxt' <= 0 then 1 else a_nxt'
                   if abs (fk - fk_nxt) < tol
                      then pure (theta, nIters - it)
                      else go theta_k pk_nxt fk_nxt dfk_nxt a_nxt (it-1)

-- line_search_wolfe2 based on https://github.com/scipy/scipy/blob/main/scipy/optimize/_linesearch.py
lineSearchWolfe :: MA.PrimMonad m
                => (PVector -> (Double, PVector))
                -> PVector
                -> PVector
                -> Double
                -> Double
                -> Double
                -> Int
                -> MSTLS m Double
lineSearchWolfe funAndGrad x0 p0 c1 c2 alpha nIter = do
    insertIfMissing 0
    insertIfMissing alpha
    (LSData _ phi_0 derphi_0) <- gets (!. 0)
    let wolfe alpha_i phi_i = phi_i > phi_0 + c1 * alpha_i * derphi_0
        curvature derphi_i  = abs derphi_i <= -c2 * derphi_0
    go nIter alpha 0 wolfe curvature
  where
    insertAlpha a     = do (phi_i, phi_i') <- phi a
                           modify (M.insert a (LSData a phi_i phi_i'))
    insertIfMissing a = do hasNoA <- gets (not . M.member a)
                           when hasNoA (insertAlpha a)

    go 0 !alpha_cur _ _ _                       = pure alpha_cur
    go it !alpha_cur alpha_prev wolfe curvature = do
        insertIfMissing alpha_cur
        insertIfMissing alpha_prev
        phi_cur  <- getPhi alpha_cur
        phi_prev <- getPhi alpha_prev
        phi_cur' <- getPhi' alpha_cur
        if | wolfe alpha_cur phi_cur           -> zoom alpha_prev alpha_cur phi wolfe curvature nIter
           | phi_cur >= phi_prev && it < nIter -> zoom alpha_prev alpha_cur phi wolfe curvature nIter
           | curvature phi_cur'                -> pure alpha_cur
           | phi_cur' >= 0                     -> zoom alpha_cur alpha_prev phi wolfe curvature nIter
           | otherwise                         -> insertIfMissing (2*alpha_cur) >> go (it-1) (2*alpha_cur) alpha_cur wolfe curvature


    phi  alpha_k = do let xap       = MA.computeAs MA.S $ MA.zipWith (\xj pj -> xj + alpha_k * pj) x0 p0
                          (fk, fk') = funAndGrad xap
                          fp        = fk' !.! p0
                      pure (fk, fp)
{-# INLINE lineSearchWolfe #-}

zoom :: (MA.PrimMonad m)
     => Double
     -> Double
     -> (Double -> m (Double, Double))
     -> (Double -> Double -> Bool)
     -> (Double -> Bool)
     -> Int
     -> MSTLS m Double
zoom aLo aHi phi wolfe curvature nIter = go nIter aLo aHi 0
  where
    getAlpha dflt ma chck = case ma of
                              Nothing -> dflt
                              Just a  -> if chck a then dflt else a


    go 0 !alphaLo _ _ = pure alphaLo
    go it !alphaLo !alphaHi alphaRec 
      | alphaLo > alphaHi  = go it alphaHi alphaLo alphaRec
      | alphaLo == alphaHi = pure alphaLo
      | otherwise          = do
        phiLo  <- getPhi alphaLo
        phiLo' <- getPhi' alphaLo
        phiHi  <- getPhi alphaHi
        phiRec <- getPhi alphaRec
        let alpha_dflt  = alphaLo + 0.5 * (alphaHi - alphaLo)
            alpha_cubic = cubicMin alphaLo phiLo phiLo' alphaHi phiHi alphaRec phiRec
            alpha_quad  = quadMin alphaLo phiLo phiLo' alphaHi phiHi
            delta       = alphaHi - alphaLo
            cchk a      = it < nIter && (a > alphaHi - 0.2 * delta || a < alphaLo + 0.2 * delta)
            qchk a      = a > alphaHi - 0.1 * delta || a < alphaLo + 0.1 * delta
            alpha_i     = getAlpha (getAlpha alpha_dflt alpha_quad qchk) alpha_cubic cchk
        (phi_i, phi_i') <- lift $ phi alpha_i
        modify (M.insert alpha_i (LSData alpha_i phi_i phi_i'))
        if | wolfe alpha_i phi_i || phi_i >= phiLo -> go (it-1) alphaLo alpha_i alphaHi
           | curvature phi_i'                      -> pure alpha_i
           | phi_i' * (alphaHi - alphaLo) >= 0     -> go (it-1) alpha_i alphaLo alphaHi
           | otherwise                             -> go (it-1) alpha_i alphaHi alphaLo
{-# INLINE zoom #-}


cubicMin :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Maybe Double
cubicMin a fa fa' b fb c fc
  | a' == 0 || isNaN cubic || isInfinite cubic = Nothing
  | otherwise   = Just cubic
  where
    cubic  = a + (sqrt radical - b') / (3 * a')
    deltaB = b - a
    deltaC = c - a
    denom  = (deltaBC2 * deltaB) * (deltaB - deltaC)
    deltaBC = deltaC * deltaB
    deltaBC2 = deltaBC * deltaC
    a' = ((fb - fa - fa' * deltaB) * deltaC * deltaC - (fc - fa - fa' * deltaC) * deltaB * deltaB) / denom
    b' = -((fb - fa - fa' * deltaB) * deltaC * deltaC * deltaC + (fc - fa - fa' * deltaC) * deltaB * deltaB * deltaB) / denom
    radical = b' ^ (2 :: Int) - 3 * a' * fa'
{-# INLINE cubicMin #-}

quadMin :: Double -> Double -> Double -> Double -> Double -> Maybe Double
quadMin a fa fa' b fb
  | b' ==0 || isNaN quad || isInfinite quad = Nothing
  | otherwise                     = Just quad
  where
    quad   = a - fa' / (2 * b')
    deltaB = b - a
    b' = (fb - fa - fa' * deltaB) / (deltaB ^ (2 :: Int))
{-# INLINE quadMin #-}

