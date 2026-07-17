{-# LANGUAGE LambdaCase, BangPatterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Eval 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables
--
-- Evaluation of SRTree expressions
--
-----------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
module Data.SRTree.Eval
        ( evalOp
        , evalFun
        , cbrt
        , inverseFunc
        , invertibles
        , evalInverse
        , invright
        , invleft
        , replicateAs
        , Target, Theta, Columns
        , compile
        , compileLoss
        )
        where

import Data.SRTree.Internal
import Data.SRTree.Recursion (Fix (..), cata)
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as V
import Control.Monad.ST (runST)
import qualified Data.Vector as VB        -- Boxed vector for instructions
import qualified Data.Vector.Unboxed.Mutable as VM
import Control.Concurrent.Async (forConcurrently_)
import System.IO.Unsafe (unsafePerformIO)
import Control.Concurrent (getNumCapabilities)
import Data.Maybe (fromJust)

-- | Vector of target values 
type Target  = Vector Double
-- | Vector of parameter values. Needs to be strict to be readily accesible.
type Theta   = Vector Double
-- | Matrix of features values 
type Columns = [Vector Double]

-- A multi-threaded replacement for V.sum
sumParallel :: Int -> (Int -> Double) -> Double
sumParallel n f = unsafePerformIO $ do
    numThreads <- getNumCapabilities
    let chunkSize  = n `quot` numThreads

    -- 1. Allocate a single block of unboxed memory EXACTLY ONCE
    out <- VM.unsafeNew numThreads

    -- 2. Spawn threads. Each thread gets a unique ID and a slice of memory.
    forConcurrently_ [0 .. numThreads - 1] $ \tId -> do
        let !start = tId * chunkSize
            -- The last thread cleans up the remainder
            !end   = if tId == numThreads - 1 then n else start + chunkSize

        -- 3. The inner thread loop. Strict, unboxed, and bounds-check free.
        let loop !i !acc
              | i >= end  = return acc
              | otherwise = loop (i + 1) (acc + f i)

        total <- loop start 0.0
        VM.unsafeWrite out tId total

    -- 4. Instantly cast the mutable memory to an immutable Vector (O(1) cost)
    totals <- V.unsafeFreeze out
    return (V.sum totals)
{-# NOINLINE sumParallel #-}

-- Improve quality of life with Num and Floating instances for our matrices 
instance Num Target where
    (+) = V.zipWith (+)
    (-) = V.zipWith (-)
    (*) = V.zipWith (*)
    abs = V.map abs
    signum = V.map signum
    fromInteger = V.singleton . fromInteger
    negate = V.map negate

instance Floating Target where
    pi = V.singleton pi
    exp = V.map exp
    log = V.map log
    sqrt = V.map sqrt
    sin = V.map sin
    cos = V.map cos
    tan = V.map tan
    asin = V.map asin
    acos = V.map acos
    atan = V.map atan
    sinh = V.map sinh
    cosh = V.map cosh
    tanh = V.map tanh
    asinh = V.map asinh
    acosh = V.map acosh
    atanh = V.map atanh
    (**) = V.zipWith (**)
instance Fractional Target where
    fromRational = V.singleton . fromRational
    (/) = V.zipWith (/)
    recip = V.map recip

-- We change the Dynamic type to evaluate a single scalar at a specific row index (Int)
data Staged =
    Scl Double
  | Static (Vector Double)
  | Dynamic (Vector Double -> Int -> Double) -- (Theta -> RowIndex -> Result)

-- A multi-threaded replacement for V.generate
generateParallel :: Int -> (Int -> Double) -> V.Vector Double
generateParallel n f = unsafePerformIO $ do
    numThreads <- getNumCapabilities
    let chunkSize  = n `quot` numThreads

    -- 1. Allocate a single block of unboxed memory EXACTLY ONCE
    out <- VM.unsafeNew n

    -- 2. Spawn threads. Each thread gets a unique ID and a slice of memory.
    forConcurrently_ [0 .. numThreads - 1] $ \tId -> do
        let !start = tId * chunkSize
            -- The last thread cleans up the remainder
            !end   = if tId == numThreads - 1 then n else start + chunkSize

        -- 3. The inner thread loop. Strict, unboxed, and bounds-check free.
        let loop !i
              | i >= end  = return ()
              | otherwise = do
                  -- Write directly to the shared memory pointer
                  VM.unsafeWrite out i (f i)
                  loop (i + 1)

        loop start

    -- 4. Instantly cast the mutable memory to an immutable Vector (O(1) cost)
    V.unsafeFreeze out
{-# NOINLINE generateParallel #-}

compileLoss :: [Vector Double] -> Fix SRTree -> Target -> Maybe Target -> (Vector Double -> Double)
compileLoss dataset tree y mYerr =
    case cata alg tree of
        Scl c     -> \_  -> V.sum $ V.replicate n c
        Static v  -> \_  -> V.sum v
        -- We only allocate memory EXACTLY ONCE here at the top level
        --Dynamic f -> \th -> V.generate n (f th)
        Dynamic f -> \th -> sumParallel n (f th)
  where
    n    = V.length (head dataset)
    yErr = fromJust mYerr

    alg :: SRTree Staged -> Staged

    -- 1. Base Cases
    alg (Const c)  = Scl c
    alg (Var i)    = Static (dataset !! i)
    alg (Param i)  = Dynamic (\th !idx -> th `V.unsafeIndex` i)
    alg (Var (-1)) = Static y
    alg (Var (-2)) = Static yErr

    -- 2. Univariate Functions
    alg (Uni f (Scl c))     = Scl (evalFun f c)
    alg (Uni f (Static v))  = Static (V.map (evalFun f) v)

    -- We map the function over the scalar result of the inner closure
    alg (Uni f (Dynamic g)) = let !rawFun = evalFun f in Dynamic (\th !i -> rawFun (g th i))

    -- 3. Binary Functions
    alg (Bin op (Scl c1) (Scl c2))       = Scl (evalOp op c1 c2)
    alg (Bin op (Scl c) (Static v))      = Static (V.map (evalOp op c) v)
    alg (Bin op (Static v) (Scl c))      = Static (V.map (\c2 -> evalOp op c2 c) v)
    alg (Bin op (Static v1) (Static v2)) = Static (V.zipWith (evalOp op) v1 v2)

    -- 4. Dynamic Combinations (The Core Optimization)

    alg (Bin op (Scl c) (Dynamic g)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp c (g th i))

    alg (Bin op (Dynamic g) (Scl c)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp (g th i) c)

    -- When combining a Static array with a Dynamic closure,
    -- we use unsafeIndex to fetch the static value at row 'i' directly.
    alg (Bin op (Static v) (Dynamic g)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp (v `V.unsafeIndex` i) (g th i))

    alg (Bin op (Dynamic g) (Static v)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp (g th i) (v `V.unsafeIndex` i))

    alg (Bin op (Dynamic g1) (Dynamic g2)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp (g1 th i) (g2 th i))


compile :: [Vector Double] -> Fix SRTree -> (Vector Double -> Vector Double)
compile dataset tree =
    case cata alg tree of
        Scl c     -> \_  -> V.replicate n c
        Static v  -> \_  -> v
        -- We only allocate memory EXACTLY ONCE here at the top level
        --Dynamic f -> \th -> V.generate n (f th)
        Dynamic f -> \th -> generateParallel n (f th)
  where
    n = V.length (head dataset)

    alg :: SRTree Staged -> Staged

    -- 1. Base Cases
    alg (Const c) = Scl c
    alg (Var i)   = Static (dataset !! i)
    -- Look at this! No more V.replicate. It just fetches the scalar directly.
    alg (Param i) = Dynamic (\th !idx -> th `V.unsafeIndex` i)
    alg (Y i)     = undefined -- this shouldn't be called

    -- 2. Univariate Functions
    alg (Uni f (Scl c))     = Scl (evalFun f c)
    alg (Uni f (Static v))  = Static (V.map (evalFun f) v)

    -- We map the function over the scalar result of the inner closure
    alg (Uni f (Dynamic g)) = let !rawFun = evalFun f in Dynamic (\th !i -> rawFun (g th i))

    -- 3. Binary Functions
    alg (Bin op (Scl c1) (Scl c2))       = Scl (evalOp op c1 c2)
    alg (Bin op (Scl c) (Static v))      = Static (V.map (evalOp op c) v)
    alg (Bin op (Static v) (Scl c))      = Static (V.map (\c2 -> evalOp op c2 c) v)
    alg (Bin op (Static v1) (Static v2)) = Static (V.zipWith (evalOp op) v1 v2)

    -- 4. Dynamic Combinations (The Core Optimization)

    alg (Bin op (Scl c) (Dynamic g)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp c (g th i))

    alg (Bin op (Dynamic g) (Scl c)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp (g th i) c)

    -- When combining a Static array with a Dynamic closure,
    -- we use unsafeIndex to fetch the static value at row 'i' directly.
    alg (Bin op (Static v) (Dynamic g)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp (v `V.unsafeIndex` i) (g th i))

    alg (Bin op (Dynamic g) (Static v)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp (g th i) (v `V.unsafeIndex` i))

    alg (Bin op (Dynamic g1) (Dynamic g2)) =
        let !rawOp = evalOp op in Dynamic (\th !i -> rawOp (g1 th i) (g2 th i))


-- returns a vector with the same number of rows as xss and containing a single repeated value.
replicateAs :: Columns -> Double -> Target
replicateAs xss c = let m = V.length (head xss) in V.replicate m c
{-# INLINE replicateAs #-}

-- | Evaluates the tree given a vector of variable values, a vector of parameter values and a function that takes a Double and change to whatever type the variables have. This is useful when working with datasets of many values per variables.
evalTree :: Columns -> Theta -> Fix SRTree -> Target
evalTree xss params = cata $ 
    \case 
       Var ix     -> xss !! ix
       Param ix   -> replicateAs xss $ params V.! ix
       Const c    -> replicateAs xss c
       Y _        -> undefined
       Uni g t    -> evalFun g t
       Bin op l r -> evalOp op l r
{-# INLINE evalTree #-}

-- evaluates an operator 
evalOp :: Floating a => Op -> a -> a -> a
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mul = (*)
evalOp Div = (/)
evalOp Power = (**)
evalOp PowerAbs = \l r -> abs l ** r
evalOp AQ = \l r -> l / sqrt(1 + r*r)
{-# INLINE evalOp #-}

-- evaluates a function 
evalFun :: Floating a => Function -> a -> a
evalFun Id = id
evalFun Abs = abs
evalFun Sin = sin
evalFun Cos = cos
evalFun Tan = tan
evalFun Sinh = sinh
evalFun Cosh = cosh
evalFun Tanh = tanh
evalFun ASin = asin
evalFun ACos = acos
evalFun ATan = atan
evalFun ASinh = asinh
evalFun ACosh = acosh
evalFun ATanh = atanh
evalFun Sqrt = sqrt
evalFun SqrtAbs = sqrt . abs
evalFun Cbrt = cbrt
evalFun Square = (^2)
evalFun Log = log
evalFun LogAbs = log . abs
evalFun Exp = exp
evalFun Recip = recip
evalFun Cube = (^3)
{-# INLINE evalFun #-}

-- Cubic root
cbrt :: Floating a => a -> a
cbrt x = signum x * abs x ** (1/3)
{-# INLINE cbrt #-}

-- | Returns the inverse of a function. This is a partial function.
inverseFunc :: Function -> Function
inverseFunc Id     = Id
inverseFunc Sin    = ASin
inverseFunc Cos    = ACos
inverseFunc Tan    = ATan
inverseFunc Sinh   = ASinh
inverseFunc Cosh   = ACosh
inverseFunc Tanh   = ATanh
inverseFunc ASin   = Sin
inverseFunc ACos   = Cos
inverseFunc ATan   = Tan
inverseFunc ASinh  = Sinh
inverseFunc ACosh  = Cosh
inverseFunc ATanh  = Tanh
inverseFunc Sqrt   = Square
inverseFunc Square = Sqrt
-- inverseFunc Cbrt   = (^3)
inverseFunc Log    = Exp
inverseFunc Exp    = Log
inverseFunc Recip  = Recip
-- inverseFunc Abs    = Abs -- we assume abs(x) = sqrt(x^2) so y = sqrt(x^2) => x^2 = y^2 => x = sqrt(y^2) = x = abs(y)
inverseFunc x      = error $ show x ++ " has no support for inverse function"
{-# INLINE inverseFunc #-}

-- | evals the inverse of a function
evalInverse :: Floating a => Function -> a -> a
evalInverse Id     = id
evalInverse Sin    = asin
evalInverse Cos    = acos
evalInverse Tan    = atan
evalInverse Sinh   = asinh
evalInverse Cosh   = acosh
evalInverse Tanh   = atanh
evalInverse ASin   = sin
evalInverse ACos   = cos
evalInverse ATan   = tan
evalInverse ASinh  = sinh
evalInverse ACosh  = cosh
evalInverse ATanh  = tanh
evalInverse Sqrt   = (^2)
evalInverse SqrtAbs = (^2)
evalInverse Square = sqrt
evalInverse Cbrt   = (^3)
evalInverse Log    = exp
evalInverse LogAbs = exp
evalInverse Exp    = log
evalInverse Abs    = abs -- we assume abs(x) = sqrt(x^2) so y = sqrt(x^2) => x^2 = y^2 => x = sqrt(y^2) = x = abs(y)
evalInverse Recip  = recip
evalInverse Cube   = cbrt
{-# INLINE evalInverse #-}

-- | evals the right inverse of an operator 
invright :: Floating a => Op -> a -> (a -> a)
invright Add v   = subtract v
invright Sub v   = (+v)
invright Mul v   = (/v)
invright Div v   = (*v)
invright Power v = (**(1/v))
invright PowerAbs v = (**(1/v))
invright AQ v = (* sqrt (1 + v*v))
{-# INLINE invright #-}

-- | evals the left inverse of an operator 
invleft :: Floating a => Op -> a -> (a -> a)
invleft Add v   = subtract v
invleft Sub v   = (+v) . negate -- y = v - r => r = v - y
invleft Mul v   = (/v)
invleft Div v   = (v/) -- y = v / r => r = v/y
invleft Power v = logBase v -- (/(log v)) . log -- y = v ^ r  log y = r log v r = log y / log v
invleft PowerAbs v = logBase v . abs
invleft AQ v = (v/)
{-# INLINE invleft #-}

-- | List of invertible functions
invertibles :: [Function]
invertibles = [Id, Sin, Cos, Tan, Tanh, ASin, ACos, ATan, ATanh, Sqrt, Square, Log, Exp, Recip]
{-# INLINE invertibles #-}
