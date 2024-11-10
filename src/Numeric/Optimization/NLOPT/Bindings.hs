{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{- |
Module      :  Numeric.Optimization.NLOPT.Bindings
Copyright   :  (c) Matthew Peddie 2017
License     :  BSD3
Maintainer  :  Matthew Peddie <mpeddie@gmail.com>
Stability   :  provisional
Portability :  GHC

Low-level interface to the NLOPT library.  Please see
<http://ab-initio.mit.edu/wiki/index.php/NLopt_Reference the NLOPT reference manual>
for detailed information; the Haskell functions in this module closely
follow the interface to the C library in @nlopt.h@.

Differences between this module and the C interface are documented
here; functions with identical interfaces are not.  In general:

  ['Opt'] corresponds to an @nlopt_opt@ object

  ['Result'] corresponds to @nlopt_result@

  ['V.Vector' 'Double'] corresponds to a @const double *@ input or a
  @double *@ output

  ['ScalarFunction'] corresponds to @nlopt_func@

  ['VectorFunction'] corresponds to @nlopt_mfunc@

  ['PreconditionerFunction'] corresponds to @nlopt_precond@

User data that is handled by @void *@ in the C bindings can be any
Haskell value.

-}

module Numeric.Optimization.NLOPT.Bindings (
  -- * C enums
  Algorithm(..)
  , algorithm_name
  , Result(..)
  , isSuccess
  -- * Optimizer object
  , Opt
  , create
  , destroy
  , copy
  -- * Random number generator seeding
  , srand
  , srand_time
  -- * Metadata
  , Version(..)
  , version
  , get_algorithm
  , get_dimension
  -- * Callbacks
  , ScalarFunction
  , VectorFunction
  , PreconditionerFunction
  -- * Running the optimizer
  , Output(..)
  , optimize
  -- * Objective function configuration
  , set_min_objective
  , set_max_objective
  , set_precond_min_objective
  , set_precond_max_objective
  -- * Bound configuration
  , set_lower_bounds
  , set_lower_bounds1
  , get_lower_bounds
  , set_upper_bounds
  , set_upper_bounds1
  , get_upper_bounds
  -- * Constraint configuration
  , remove_inequality_constraints
  , add_inequality_constraint
  , add_precond_inequality_constraint
  , add_inequality_mconstraint
  , remove_equality_constraints
  , add_equality_constraint
  , add_precond_equality_constraint
  , add_equality_mconstraint
  -- * Stopping criterion configuration
  , set_stopval
  , get_stopval
  , set_ftol_rel
  , get_ftol_rel
  , set_ftol_abs
  , get_ftol_abs
  , set_xtol_rel
  , get_xtol_rel
  , set_xtol_abs1
  , set_xtol_abs
  , get_xtol_abs
  , set_maxeval
  , get_maxeval
  , set_maxtime
  , get_maxtime
  , force_stop
  , set_force_stop
  , get_force_stop
  -- * Algorithm-specific configuration
  , set_local_optimizer
  , set_population
  , get_population
  , set_vector_storage
  , get_vector_storage
  , set_default_initial_step
  , set_initial_step
  , set_initial_step1
  , get_initial_step
  ) where

import Foreign hiding (void)
import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent as CFP

import qualified Data.Vector.Storable.Mutable as MV
import qualified Data.Vector.Storable as V

{- C enums -}

-- | The NLOPT algorithm names, apart from the names of the actual
-- optimization methods, follow this scheme:
--
--   [@G@] means a global method
--   [@L@] means a local method
--   [@D@] means a method that requires the derivative
--   [@N@] means a method that does not require the derivative
--   [@*_RAND@] means the algorithm involves some randomization.
--   [@*_NOSCAL@] means the algorithm is *not* scaled to a unit
--   hypercube (i.e. it is sensitive to the units of x)
data Algorithm
  = GN_DIRECT                  -- ^ DIviding RECTangles
  | GN_DIRECT_L                -- ^ DIviding RECTangles,
                               -- locally-biased variant
  | GN_DIRECT_L_RAND           -- ^ DIviding RECTangles, "slightly
                               -- randomized"
  | GN_DIRECT_NOSCAL           -- ^ DIviding RECTangles, unscaled version
  | GN_DIRECT_L_NOSCAL         -- ^ DIviding RECTangles,
                               -- locally-biased and unscaled
  | GN_DIRECT_L_RAND_NOSCAL    -- ^ DIviding RECTangles, locally-biased,
                               -- unscaled and "slightly randomized"
  | GN_ORIG_DIRECT             -- ^ DIviding RECTangles, original FORTRAN
                               -- implementation
  | GN_ORIG_DIRECT_L           -- ^ DIviding RECTangles,
                               -- locally-biased, original FORTRAN
                               -- implementation
  | GD_STOGO                   -- ^ Stochastic Global Optimization
  | GD_STOGO_RAND              -- ^ Stochastic Global Optimization,
                               -- randomized variant
  | LD_LBFGS_NOCEDAL           -- ^ Limited-memory BFGS
  | LD_LBFGS                   -- ^ Limited-memory BFGS
  | LN_PRAXIS                  -- ^ PRincipal AXIS gradient-free local
                               -- optimization
  | LD_VAR2                    -- ^ Shifted limited-memory
                               -- variable-metric, rank-2
  | LD_VAR1                    -- ^ Shifted limited-memory
                               -- variable-metric, rank-1
  | LD_TNEWTON                 -- ^ Truncated Newton's method
  | LD_TNEWTON_RESTART         -- ^ Truncated Newton's method with
                               -- automatic restarting
  | LD_TNEWTON_PRECOND         -- ^ Preconditioned truncated Newton's
                               -- method
  | LD_TNEWTON_PRECOND_RESTART -- ^ Preconditioned truncated Newton's
                               -- method with automatic restarting
  | GN_CRS2_LM                 -- ^ Controlled Random Search with
                               -- Local Mutation
  | GN_MLSL                    -- ^ Original Multi-Level
                               -- Single-Linkage
  | GD_MLSL                    -- ^ Original Multi-Level
                               -- Single-Linkage, user-provided
                               -- derivative
  | GN_MLSL_LDS                -- ^ Multi-Level Single-Linkage with
                               -- Sobol Low-Discrepancy Sequence for
                               -- starting points
  | GD_MLSL_LDS                -- ^ Multi-Level Single-Linkage with
                               -- Sobol Low-Discrepancy Sequence for
                               -- starting points, user-provided
                               -- derivative
  | LD_MMA                     -- ^ Method of moving averages
  | LN_COBYLA                  -- ^ Constrained Optimization BY Linear
                               -- Approximations
  | LN_NEWUOA                  -- ^ Powell's NEWUOA algorithm
  | LN_NEWUOA_BOUND            -- ^ Powell's NEWUOA algorithm with
                               -- bounds by SGJ
  | LN_NELDERMEAD              -- ^ Nelder-Mead Simplex gradient-free
                               -- method
  | LN_SBPLX                   -- ^ NLOPT implementation of Rowan's
                               -- Subplex algorithm
  | LN_AUGLAG                  -- ^ AUGmented LAGrangian
  | LD_AUGLAG                  -- ^ AUGmented LAGrangian,
                               -- user-provided derivative
  | LN_AUGLAG_EQ               -- ^ AUGmented LAGrangian with penalty
                               -- functions only for equality
                               -- constraints
  | LD_AUGLAG_EQ               -- ^ AUGmented LAGrangian with
                               -- penalty functions only for equality
                               -- constraints, user-provided
                               -- derivative
  | LN_BOBYQA                  -- ^ Bounded Optimization BY Quadratic
                               -- Approximations
  | GN_ISRES                   -- ^ Improved Stochastic Ranking
                               -- Evolution Strategy

  | AUGLAG                     -- ^ AUGmented LAGrangian, requires
                               -- local_optimizer to be set
  | AUGLAG_EQ                  -- ^ AUGmented LAGrangian with penalty
                               -- functions only for equality
                               -- constraints, requires
                               -- local_optimizer to be set
  | G_MLSL                     -- ^ Original Multi-Level
                               -- Single-Linkage, user-provided
                               -- derivative, requires local_optimizer
                               -- to be set
  | G_MLSL_LDS                 -- ^ Multi-Level Single-Linkage with
                               -- Sobol Low-Discrepancy Sequence for
                               -- starting points, requires
                               -- local_optimizer to be set
  | LD_SLSQP                   -- ^ Sequential Least-SQuares Programming
  | LD_CCSAQ                   -- ^ Conservative Convex Separable
                               -- Approximation
  | GN_ESCH                    -- ^ Evolutionary Algorithm
  deriving (Eq, Show, Read, Bounded)

instance Enum Algorithm where
  fromEnum GN_DIRECT                  = 0
  fromEnum GN_DIRECT_L                = 1
  fromEnum GN_DIRECT_L_RAND           = 2
  fromEnum GN_DIRECT_NOSCAL           = 3
  fromEnum GN_DIRECT_L_NOSCAL         = 4
  fromEnum GN_DIRECT_L_RAND_NOSCAL    = 5
  fromEnum GN_ORIG_DIRECT             = 6
  fromEnum GN_ORIG_DIRECT_L           = 7
  fromEnum GD_STOGO                   = 8
  fromEnum GD_STOGO_RAND              = 9
  fromEnum LD_LBFGS_NOCEDAL           = 10
  fromEnum LD_LBFGS                   = 11
  fromEnum LN_PRAXIS                  = 12
  fromEnum LD_VAR2                    = 13
  fromEnum LD_VAR1                    = 14
  fromEnum LD_TNEWTON                 = 15
  fromEnum LD_TNEWTON_RESTART         = 16
  fromEnum LD_TNEWTON_PRECOND         = 17
  fromEnum LD_TNEWTON_PRECOND_RESTART = 18
  fromEnum GN_CRS2_LM                 = 19
  fromEnum GN_MLSL                    = 20
  fromEnum GD_MLSL                    = 21
  fromEnum GN_MLSL_LDS                = 22
  fromEnum GD_MLSL_LDS                = 23
  fromEnum LD_MMA                     = 24
  fromEnum LN_COBYLA                  = 25
  fromEnum LN_NEWUOA                  = 26
  fromEnum LN_NEWUOA_BOUND            = 27
  fromEnum LN_NELDERMEAD              = 28
  fromEnum LN_SBPLX                   = 29
  fromEnum LN_AUGLAG                  = 30
  fromEnum LD_AUGLAG                  = 31
  fromEnum LN_AUGLAG_EQ               = 32
  fromEnum LD_AUGLAG_EQ               = 33
  fromEnum LN_BOBYQA                  = 34
  fromEnum GN_ISRES                   = 35
  fromEnum AUGLAG                     = 36
  fromEnum AUGLAG_EQ                  = 37
  fromEnum G_MLSL                     = 38
  fromEnum G_MLSL_LDS                 = 39
  fromEnum LD_SLSQP                   = 40
  fromEnum LD_CCSAQ                   = 41
  fromEnum GN_ESCH                    = 42
  toEnum 0 = GN_DIRECT
  toEnum 1 = GN_DIRECT_L
  toEnum 2 = GN_DIRECT_L_RAND
  toEnum 3 = GN_DIRECT_NOSCAL
  toEnum 4 = GN_DIRECT_L_NOSCAL
  toEnum 5 = GN_DIRECT_L_RAND_NOSCAL
  toEnum 6 = GN_ORIG_DIRECT
  toEnum 7 = GN_ORIG_DIRECT_L
  toEnum 8 = GD_STOGO
  toEnum 9 = GD_STOGO_RAND
  toEnum 10 = LD_LBFGS_NOCEDAL
  toEnum 11 = LD_LBFGS
  toEnum 12 = LN_PRAXIS
  toEnum 13 = LD_VAR2
  toEnum 14 = LD_VAR1
  toEnum 15 = LD_TNEWTON
  toEnum 16 = LD_TNEWTON_RESTART
  toEnum 17 = LD_TNEWTON_PRECOND
  toEnum 18 = LD_TNEWTON_PRECOND_RESTART
  toEnum 19 = GN_CRS2_LM
  toEnum 20 = GN_MLSL
  toEnum 21 = GD_MLSL
  toEnum 22 = GN_MLSL_LDS
  toEnum 23 = GD_MLSL_LDS
  toEnum 24 = LD_MMA
  toEnum 25 = LN_COBYLA
  toEnum 26 = LN_NEWUOA
  toEnum 27 = LN_NEWUOA_BOUND
  toEnum 28 = LN_NELDERMEAD
  toEnum 29 = LN_SBPLX
  toEnum 30 = LN_AUGLAG
  toEnum 31 = LD_AUGLAG
  toEnum 32 = LN_AUGLAG_EQ
  toEnum 33 = LD_AUGLAG_EQ
  toEnum 34 = LN_BOBYQA
  toEnum 35 = GN_ISRES
  toEnum 36 = AUGLAG
  toEnum 37 = AUGLAG_EQ
  toEnum 38 = G_MLSL
  toEnum 39 = G_MLSL_LDS
  toEnum 40 = LD_SLSQP
  toEnum 41 = LD_CCSAQ
  toEnum 42 = GN_ESCH
  toEnum e = error $
             "Algorithm.toEnum: invalid C value '" ++ show e ++ "' received."

foreign import ccall "nlopt.h nlopt_algorithm_name"
  nlopt_algorithm_name :: CInt -> CString

algorithm_name :: Algorithm -> IO String
algorithm_name = peekCString . nlopt_algorithm_name . fromIntegral . fromEnum

-- | Mostly self-explanatory.
data Result
  = FAILURE  -- ^ Generic failure code
  | INVALID_ARGS
  | OUT_OF_MEMORY
  | ROUNDOFF_LIMITED
  | FORCED_STOP
  | SUCCESS  -- ^ Generic success code
  | STOPVAL_REACHED
  | FTOL_REACHED
  | XTOL_REACHED
  | MAXEVAL_REACHED
  | MAXTIME_REACHED
  deriving (Eq, Read, Show, Bounded)

instance Enum Result where
  fromEnum FAILURE = -1
  fromEnum INVALID_ARGS = -2
  fromEnum OUT_OF_MEMORY = -3
  fromEnum ROUNDOFF_LIMITED = -4
  fromEnum FORCED_STOP = -5
  fromEnum SUCCESS = 1
  fromEnum STOPVAL_REACHED = 2
  fromEnum FTOL_REACHED = 3
  fromEnum XTOL_REACHED = 4
  fromEnum MAXEVAL_REACHED = 5
  fromEnum MAXTIME_REACHED = 6
  toEnum (-1) = FAILURE
  toEnum (-2) = INVALID_ARGS
  toEnum (-3) = OUT_OF_MEMORY
  toEnum (-4) = ROUNDOFF_LIMITED
  toEnum (-5) = FORCED_STOP
  toEnum 1 = SUCCESS
  toEnum 2 = STOPVAL_REACHED
  toEnum 3 = FTOL_REACHED
  toEnum 4 = XTOL_REACHED
  toEnum 5 = MAXEVAL_REACHED
  toEnum 6 = MAXTIME_REACHED
  toEnum e = error $
             "Result.toEnum: invalid C value '" ++ show e ++ "' received."

isSuccess :: Result -> Bool
isSuccess SUCCESS         = True
isSuccess STOPVAL_REACHED = True
isSuccess FTOL_REACHED    = True
isSuccess XTOL_REACHED    = True
isSuccess MAXEVAL_REACHED = True
isSuccess MAXTIME_REACHED = True
isSuccess _               = False

parseEnum :: (Integral a, Enum b) => a -> b
parseEnum = toEnum . fromIntegral

{- NLOPT optimizer object -}

type NloptOpt = Ptr ()

-- | An optimizer object which must be created, configured and then
-- passed to 'optimize' to solve a problem
newtype Opt = Opt { pointerFromOpt :: ForeignPtr () }

withOpt :: Opt -> (NloptOpt -> IO a) -> IO a
withOpt (Opt p) f = do
  ret <- withForeignPtr p f
  touchForeignPtr p  -- This is critical!  Otherwise the GC might
                     -- think it's done with everything in the middle
                     -- of the problem.
  return ret

useOpt :: (NloptOpt -> IO a) -> Opt -> IO a
useOpt = flip withOpt

-- Every time we make a "wrapper" call, the runtime allocates a new
-- function pointer and won't release it until we explicitly tell it
-- to.  This doesn't mesh well with NLOPT's "object-oriented" design,
-- wherein we have to allocate an object and make a bunch of setup
-- calls before we run the problem, so what we do is add a finalizer
-- to the 'Opt' object's 'ForeignPtr' every time we need to create a
-- function pointer for C to use.
addFunPtrFinalizer :: Opt -> FunPtr a -> IO ()
addFunPtrFinalizer (Opt p) funptr =
  CFP.addForeignPtrFinalizer p (freeHaskellFunPtr funptr)

foreign import ccall "nlopt.h nlopt_create"
  nlopt_create :: CInt -> CUInt -> IO (NloptOpt)

-- | Create a new 'Opt' object
create :: Algorithm -- ^ Choice of algorithm
       -> Word  -- ^ Parameter vector dimension
       -> IO (Maybe Opt)  -- ^ Optimizer object
create alg dimension = do
  outp <- nlopt_create (fromIntegral $ fromEnum alg) (fromIntegral dimension)
  if (outp == nullPtr)
    then return Nothing
    else Just . Opt <$> CFP.newForeignPtr outp (nlopt_destroy outp)

foreign import ccall "nlopt.h nlopt_destroy"
  nlopt_destroy :: NloptOpt -> IO ()

-- It shouldn't be strictly necessary to call this by hand since we've
-- already put a call to 'nlopt_destroy' into the 'ForeignPtr', but
-- it's available in the C interface.
destroy :: Opt -> IO ()
destroy = finalizeForeignPtr . pointerFromOpt

foreign import ccall "nlopt.h nlopt_copy"
  nlopt_copy :: NloptOpt -> IO (NloptOpt)

copy :: Opt -> IO Opt
copy = useOpt $ \inp -> do
  outp <- nlopt_copy inp
  Opt <$> CFP.newForeignPtr outp (nlopt_destroy outp)

{- Random seeding functions -}

foreign import ccall "nlopt.h nlopt_srand"
  nlopt_srand :: CUInt -> IO ()

srand :: Integral a => a -> IO ()
srand = nlopt_srand . fromIntegral

foreign import ccall "nlopt.h nlopt_srand_time"
  nlopt_srand_time :: IO ()

srand_time :: IO ()
srand_time = nlopt_srand_time

{- Metadata -}

foreign import ccall "nlopt.h nlopt_version"
  nlopt_version :: Ptr CInt -> Ptr CInt -> Ptr CInt -> IO ()

-- | NLOPT library version, e.g. @2.4.2@
data Version = Version
  { major :: Int
  , minor :: Int
  , bugfix :: Int
  } deriving (Eq, Ord, Read, Show)

version :: IO Version
version =
  alloca $ \majptr ->
  alloca $ \minptr ->
  alloca $ \bfptr -> do
  nlopt_version majptr minptr bfptr
  Version <$> pk majptr <*> pk minptr <*> pk bfptr
  where
    pk = fmap fromIntegral . peek

foreign import ccall "nlopt.h nlopt_get_algorithm"
  nlopt_get_algorithm :: NloptOpt -> IO CInt

get_algorithm :: Opt -> IO Algorithm
get_algorithm = useOpt $ fmap parseEnum . nlopt_get_algorithm

foreign import ccall "nlopt.h nlopt_get_dimension"
  nlopt_get_dimension :: NloptOpt -> IO CUInt

get_dimension :: Opt -> IO Word
get_dimension = useOpt $ fmap fromIntegral . nlopt_get_dimension

{- Callback functions -}

asMVector :: CUInt -> Ptr CDouble -> IO (MV.IOVector Double)
asMVector dim ptr =
  MV.unsafeCast . flip MV.unsafeFromForeignPtr0 (fromIntegral dim) <$>
  newForeignPtr_ ptr

asVector :: CUInt -> Ptr CDouble -> IO (V.Vector Double)
asVector dim ptr =
  V.unsafeCast . flip V.unsafeFromForeignPtr0 (fromIntegral dim) <$>
  newForeignPtr_ ptr

type CFunc a = CUInt -> Ptr CDouble -> Ptr CDouble -> StablePtr a -> IO CDouble

-- | This function type corresponds to @nlopt_func@ in C and is used
-- for scalar functions of the parameter vector.  You may pass data of
-- any type @a@ to the functions in this module that take a
-- 'ScalarFunction' as an argument; this data will be supplied to your
-- your function when it is called.
type ScalarFunction a
  = V.Vector Double            -- ^ Parameter vector
 -> Maybe (MV.IOVector Double) -- ^ Gradient vector to be filled in
 -> a                          -- ^ User data
 -> IO Double                  -- ^ Scalar result

-- | This function type corresponds to @nlopt_mfunc@ in C and is used
-- for vector functions of the parameter vector.  You may pass data of
-- any type @a@ to the functions in this module that take a
-- 'VectorFunction' as an argument; this data will be supplied to your
-- function when it is called.
type VectorFunction a
  = V.Vector Double            -- ^ Parameter vector
 -> MV.IOVector Double         -- ^ Output vector to be filled in
 -> Maybe (MV.IOVector Double) -- ^ Gradient vector to be filled in
 -> a                          -- ^ User data
 -> IO ()

-- | This function type corresponds to @nlopt_precond@ in C and is
-- used for functions that precondition a vector at a given point in
-- the parameter space.  You may pass data of any type @a@ to the
-- functions in this module that take a 'PreconditionerFunction' as an
-- argument; this data will be supplied to your function when it is
-- called.
type PreconditionerFunction a
  = V.Vector Double    -- ^ Parameter vector
 -> V.Vector Double    -- ^ Vector @v@ to precondition
 -> MV.IOVector Double -- ^ Output vector @vpre@ to be filled in
 -> a                  -- ^ User data
 -> IO ()

wrapCFunction :: ScalarFunction a -> CFunc a
wrapCFunction cfunc dim stateptr gradientptr userptr = do
  nloptgradient <- asMVector dim gradientptr
  statevec <- asVector dim stateptr
  userdata <- deRefStablePtr userptr
  let
    gradptr = if gradientptr /= nullPtr
      then Just nloptgradient
      else Nothing
  realToFrac <$> cfunc statevec gradptr userdata

foreign import ccall safe "wrapper"
  mkCFunction :: CFunc a -> IO (FunPtr (CFunc a))

type CMFunc a = CUInt -> Ptr CDouble -> CUInt -> Ptr CDouble
             -> Ptr CDouble -> StablePtr a -> IO ()

wrapMFunction :: VectorFunction a -> CMFunc a
wrapMFunction mfunc constrdim constrptr dim stateptr gradientptr userptr
  = do
  nloptgradient <- asMVector (dim * constrdim) gradientptr
  nloptconstraint <- asMVector constrdim constrptr
  statevec <- asVector dim stateptr
  userdata <- deRefStablePtr userptr
  let
    gradptr = if gradientptr /= nullPtr
      then Just nloptgradient
      else Nothing
  mfunc statevec nloptconstraint gradptr userdata

foreign import ccall safe "wrapper"
  mkMFunction :: CMFunc a -> IO (FunPtr (CMFunc a))

type CPrecond a = CUInt -> Ptr CDouble -> Ptr CDouble
               -> Ptr CDouble -> StablePtr a -> IO ()

wrapPreconditioner :: PreconditionerFunction a -> CPrecond a
wrapPreconditioner prec dim stateptr vptr preptr userptr = do
  nloptpre <- asMVector dim preptr
  statevec <- asVector dim stateptr
  vvec <- asVector dim vptr
  userdata <- deRefStablePtr userptr
  prec statevec vvec nloptpre userdata

foreign import ccall safe "wrapper"
  mkPreconditionerFunction :: CPrecond a -> IO (FunPtr (CPrecond a))

-- We have to do the same silly dance with our user-data 'StablePtr's
-- as we do with function pointer wrappers: because NLOPT expects
-- these pointers before the actual optimization run, we have to
-- attach finalizers for them to the 'Opt' object so that they get
-- cleaned up properly.
addStablePtrFinalizer :: Opt -> StablePtr a -> IO ()
addStablePtrFinalizer (Opt p) sp =
  CFP.addForeignPtrFinalizer p (freeStablePtr sp)

getStablePtr :: Opt -> a -> IO (StablePtr a)
getStablePtr opt a = do
  aptr <- newStablePtr a
  addStablePtrFinalizer opt aptr
  return aptr

exportFunPtr :: (t1 -> IO (FunPtr a)) -> (t -> t1) -> t -> Opt -> IO (FunPtr a)
exportFunPtr mk wrap fun opt = do
  funptr <- mk $ wrap fun
  addFunPtrFinalizer opt funptr
  return funptr

{- Invoking the optimizer -}

-- | The output of an NLOPT optimizer run.
data Output = Output
  { resultCode :: Result                -- ^ Return code
  , resultCost :: Double                -- ^ Minimum of the objective
                                        -- function if optimization
                                        -- succeeded
  , resultParameters :: V.Vector Double -- ^ Parameters corresponding
                                        -- to the minimum if
                                        -- optimization succeeded
  }

foreign import ccall "nlopt.h nlopt_optimize"
  nlopt_optimize :: NloptOpt -> Ptr CDouble -> Ptr CDouble -> IO CInt

-- | This function is very similar to the C function @nlopt_optimize@,
-- but it does not use mutable vectors and returns an 'Output'
-- structure.
optimize :: Opt  -- ^ Optimizer object set up to solve the problem
         -> V.Vector Double  -- ^ Initial-guess parameter vector
         -> IO Output  -- ^ Results of the optimization run
optimize optimizer x0 = withOpt optimizer $ \opt -> do
  vmut <- V.thaw $ V.unsafeCast x0
  alloca $ \costPtr -> do
    result <- MV.unsafeWith vmut $ \xptr ->
      parseEnum <$> nlopt_optimize opt xptr costPtr
    outputCost <- peek . castPtr $ costPtr
    iceout <- V.unsafeFreeze (MV.unsafeCast vmut)
    return $ Output result outputCost iceout

{- Objective function setup -}

foreign import ccall "nlopt.h nlopt_set_min_objective"
  nlopt_set_min_objective :: NloptOpt -> FunPtr (CFunc a)
                          -> StablePtr a -> IO CInt

foreign import ccall "nlopt.h nlopt_set_max_objective"
  nlopt_set_max_objective :: NloptOpt -> FunPtr (CFunc a)
                          -> StablePtr a -> IO CInt

set_min_objective :: Opt -> ScalarFunction a -> a -> IO Result
set_min_objective opt objf userdata = do
  objfunptr <- exportFunPtr mkCFunction wrapCFunction objf opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o ->
    parseEnum <$>
    nlopt_set_min_objective o objfunptr userptr

set_max_objective :: Opt -> ScalarFunction a -> a -> IO Result
set_max_objective opt objf userdata = do
  objfunptr <- exportFunPtr mkCFunction wrapCFunction objf opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o ->
    parseEnum <$> nlopt_set_max_objective o objfunptr userptr

foreign import ccall "nlopt.h nlopt_set_precond_min_objective"
  nlopt_set_precond_min_objective :: NloptOpt
                                  -> FunPtr (CFunc a)
                                  -> FunPtr (CPrecond a)
                                  -> StablePtr a
                                  -> IO CInt

foreign import ccall "nlopt.h nlopt_set_precond_max_objective"
  nlopt_set_precond_max_objective :: NloptOpt
                                  -> FunPtr (CFunc a)
                                  -> FunPtr (CPrecond a)
                                  -> StablePtr a
                                  -> IO CInt

set_precond_min_objective :: Opt
                          -> ScalarFunction a
                          -> PreconditionerFunction a
                          -> a
                          -> IO Result
set_precond_min_objective opt objf pref userdata = do
  objfunptr <- exportFunPtr mkCFunction wrapCFunction objf opt
  prefunptr <- exportFunPtr mkPreconditionerFunction wrapPreconditioner pref opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o -> parseEnum <$>
    nlopt_set_precond_min_objective o objfunptr prefunptr userptr

set_precond_max_objective :: Opt
                          -> ScalarFunction a
                          -> PreconditionerFunction a
                          -> a
                          -> IO Result
set_precond_max_objective opt objf pref userdata = do
  objfunptr <- exportFunPtr mkCFunction wrapCFunction objf opt
  prefunptr <- exportFunPtr mkPreconditionerFunction wrapPreconditioner pref opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o -> parseEnum <$>
    nlopt_set_precond_max_objective o objfunptr prefunptr userptr

{- Working with bounds -}

foreign import ccall "nlopt.h nlopt_set_lower_bounds"
  nlopt_set_lower_bounds :: NloptOpt -> Ptr CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_set_lower_bounds1"
  nlopt_set_lower_bounds1 :: NloptOpt -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_lower_bounds"
  nlopt_get_lower_bounds :: NloptOpt -> Ptr CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_set_upper_bounds"
  nlopt_set_upper_bounds :: NloptOpt -> Ptr CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_set_upper_bounds1"
  nlopt_set_upper_bounds1 :: NloptOpt -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_upper_bounds"
  nlopt_get_upper_bounds :: NloptOpt -> Ptr CDouble -> IO CInt

set_lower_bounds :: Opt -> V.Vector Double -> IO Result
set_lower_bounds opt bounds =
  withForeignPtr (fst . V.unsafeToForeignPtr0 . V.unsafeCast $ bounds) $
    \bptr -> withOpt opt $ \o ->
      parseEnum <$> nlopt_set_lower_bounds o bptr

set_lower_bounds1 :: Opt -> Double -> IO Result
set_lower_bounds1 opt bound =
  withOpt opt $ \o ->
    parseEnum <$> nlopt_set_lower_bounds1 o (realToFrac bound)

get_lower_bounds :: Opt -> IO (V.Vector Double, Result)
get_lower_bounds opt = do
  v <- get_dimension opt >>= MV.new . fromIntegral
  MV.unsafeWith (MV.unsafeCast v) $ \vptr -> withOpt opt $ \o -> do
    result <- parseEnum <$> nlopt_get_lower_bounds o vptr
    retv <- V.unsafeFreeze v
    return (retv, result)

set_upper_bounds :: Opt -> V.Vector Double -> IO Result
set_upper_bounds opt bounds =
  withForeignPtr (fst . V.unsafeToForeignPtr0 . V.unsafeCast $ bounds) $
    \bptr -> withOpt opt $ \o ->
      parseEnum <$> nlopt_set_upper_bounds o bptr

set_upper_bounds1 :: Opt -> Double -> IO Result
set_upper_bounds1 opt bound =
  withOpt opt $ \o ->
    parseEnum <$> nlopt_set_upper_bounds1 o (realToFrac bound)

get_upper_bounds :: Opt -> IO (V.Vector Double, Result)
get_upper_bounds opt = do
  v <- get_dimension opt >>= MV.new . fromIntegral
  MV.unsafeWith (MV.unsafeCast v) $ \vptr -> withOpt opt $ \o -> do
    result <- parseEnum <$> nlopt_get_upper_bounds o vptr
    retv <- V.unsafeFreeze v
    return (retv, result)

{- Working with constraints -}

foreign import ccall "nlopt.h nlopt_remove_inequality_constraints"
  nlopt_remove_inequality_constraints :: NloptOpt -> IO CInt

foreign import ccall "nlopt.h nlopt_add_inequality_constraint"
  nlopt_add_inequality_constraint :: NloptOpt -> FunPtr (CFunc a)
                                  -> StablePtr a -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_add_precond_inequality_constraint"
  nlopt_add_precond_inequality_constraint :: NloptOpt -> FunPtr (CFunc a)
                                  -> FunPtr (CPrecond a) -> StablePtr a
                                  -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_add_inequality_mconstraint"
  nlopt_add_inequality_mconstraint :: NloptOpt -> CUInt -> FunPtr (CMFunc a)
                                  -> StablePtr a -> CDouble -> IO CInt

remove_inequality_constraints :: Opt -> IO Result
remove_inequality_constraints =
  useOpt $ fmap parseEnum . nlopt_remove_inequality_constraints

add_inequality_constraint :: Opt -> ScalarFunction a
                          -> a -> Double -> IO Result
add_inequality_constraint opt objfun userdata tol = do
  objfunptr <- exportFunPtr mkCFunction wrapCFunction objfun opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o ->
      parseEnum <$>
      nlopt_add_inequality_constraint o objfunptr userptr (realToFrac tol)

add_precond_inequality_constraint :: Opt -> ScalarFunction a
                                  -> PreconditionerFunction a -> a -> Double
                                  -> IO Result
add_precond_inequality_constraint opt objfun precfun userdata tol = do
  objfunptr <- exportFunPtr mkCFunction wrapCFunction objfun opt
  precfunptr <-
    exportFunPtr mkPreconditionerFunction wrapPreconditioner precfun opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o ->
      parseEnum <$>
      nlopt_add_precond_inequality_constraint o objfunptr
        precfunptr userptr (realToFrac tol)

add_inequality_mconstraint :: Opt -> Word -> VectorFunction a -> a
                           -> Double -> IO Result
add_inequality_mconstraint opt constraintsize constrfun userdata tol = do
  constrfunptr <- exportFunPtr mkMFunction wrapMFunction constrfun opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o ->
      parseEnum <$>
      nlopt_add_inequality_mconstraint o (fromIntegral constraintsize)
      constrfunptr userptr (realToFrac tol)

foreign import ccall "nlopt.h nlopt_remove_equality_constraints"
  nlopt_remove_equality_constraints :: NloptOpt -> IO CInt

foreign import ccall "nlopt.h nlopt_add_equality_constraint"
  nlopt_add_equality_constraint :: NloptOpt -> FunPtr (CFunc a)
                                -> StablePtr a -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_add_precond_equality_constraint"
  nlopt_add_precond_equality_constraint :: NloptOpt -> FunPtr (CFunc a)
                                        -> FunPtr (CPrecond a) -> StablePtr a
                                        -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_add_equality_mconstraint"
  nlopt_add_equality_mconstraint :: NloptOpt -> CUInt -> FunPtr (CMFunc a)
                                 -> StablePtr a -> CDouble -> IO CInt

remove_equality_constraints :: Opt -> IO Result
remove_equality_constraints =
  useOpt $ fmap parseEnum . nlopt_remove_equality_constraints

add_equality_constraint :: Opt -> ScalarFunction a
                        -> a -> Double -> IO Result
add_equality_constraint opt objfun userdata tol = do
  objfunptr <- exportFunPtr mkCFunction wrapCFunction objfun opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o ->
      parseEnum <$>
      nlopt_add_equality_constraint o objfunptr userptr (realToFrac tol)

add_precond_equality_constraint :: Opt -> ScalarFunction a
                                  -> PreconditionerFunction a -> a -> Double
                                  -> IO Result
add_precond_equality_constraint opt objfun precfun userdata tol = do
  objfunptr <- exportFunPtr mkCFunction wrapCFunction objfun opt
  precfunptr <-
    exportFunPtr mkPreconditionerFunction wrapPreconditioner precfun opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o ->
      parseEnum <$>
      nlopt_add_precond_equality_constraint o objfunptr
        precfunptr userptr (realToFrac tol)

add_equality_mconstraint :: Opt -> Word -> VectorFunction a -> a
                           -> Double -> IO Result
add_equality_mconstraint opt constraintsize constrfun userdata tol = do
  constrfunptr <- exportFunPtr mkMFunction wrapMFunction constrfun opt
  userptr <- getStablePtr opt userdata
  withOpt opt $ \o ->
      parseEnum <$>
      nlopt_add_equality_mconstraint o (fromIntegral constraintsize)
      constrfunptr userptr (realToFrac tol)

{- Stopping criteria -}

withInputVector :: (Storable c, Storable a)
                => V.Vector c -> (Ptr a -> IO b) -> IO b
withInputVector = withForeignPtr . fst . V.unsafeToForeignPtr0 . V.unsafeCast
withOutputVector :: (Storable c, Storable a)
                 => V.MVector s c -> (Ptr a -> IO b) -> IO b
withOutputVector = withForeignPtr . fst . MV.unsafeToForeignPtr0 . MV.unsafeCast

setScalar :: (Enum a, Integral b) => (NloptOpt -> t1 -> IO b)
          -> (t -> t1) -> Opt -> t -> IO a
setScalar setter conv opt val = withOpt opt $ \o ->
  parseEnum <$> setter o (conv val)

getScalar :: (NloptOpt -> IO b) -> (b -> a) -> Opt -> IO a
getScalar getter conv = useOpt $ fmap conv . getter

foreign import ccall "nlopt.h nlopt_set_stopval"
  nlopt_set_stopval :: NloptOpt -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_stopval"
  nlopt_get_stopval :: NloptOpt -> IO CDouble

set_stopval :: Opt -> Double -> IO Result
set_stopval = setScalar nlopt_set_stopval realToFrac

get_stopval :: Opt -> IO Double
get_stopval = getScalar nlopt_get_stopval realToFrac

foreign import ccall "nlopt.h nlopt_set_ftol_rel"
  nlopt_set_ftol_rel :: NloptOpt -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_ftol_rel"
  nlopt_get_ftol_rel :: NloptOpt -> IO CDouble

set_ftol_rel :: Opt -> Double -> IO Result
set_ftol_rel = setScalar nlopt_set_ftol_rel realToFrac

get_ftol_rel :: Opt -> IO Double
get_ftol_rel = getScalar nlopt_get_ftol_rel realToFrac

foreign import ccall "nlopt.h nlopt_set_ftol_abs"
  nlopt_set_ftol_abs :: NloptOpt -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_ftol_abs"
  nlopt_get_ftol_abs :: NloptOpt -> IO CDouble

set_ftol_abs :: Opt -> Double -> IO Result
set_ftol_abs = setScalar nlopt_set_ftol_abs realToFrac

get_ftol_abs :: Opt -> IO Double
get_ftol_abs = getScalar nlopt_get_ftol_abs realToFrac

foreign import ccall "nlopt.h nlopt_set_xtol_rel"
  nlopt_set_xtol_rel :: NloptOpt -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_xtol_rel"
  nlopt_get_xtol_rel :: NloptOpt -> IO CDouble

set_xtol_rel :: Opt -> Double -> IO Result
set_xtol_rel = setScalar nlopt_set_xtol_rel realToFrac

get_xtol_rel :: Opt -> IO Double
get_xtol_rel = getScalar nlopt_get_xtol_rel realToFrac

foreign import ccall "nlopt.h nlopt_set_xtol_abs1"
  nlopt_set_xtol_abs1 :: NloptOpt -> CDouble -> IO CInt

set_xtol_abs1 :: Opt -> Double -> IO Result
set_xtol_abs1 = setScalar nlopt_set_xtol_abs1 realToFrac

foreign import ccall "nlopt.h nlopt_set_xtol_abs"
  nlopt_set_xtol_abs :: NloptOpt -> Ptr CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_xtol_abs"
  nlopt_get_xtol_abs :: NloptOpt -> Ptr CDouble -> IO CInt

set_xtol_abs :: Opt -> V.Vector Double -> IO Result
set_xtol_abs opt tolvec =
  withInputVector tolvec $ \tolptr ->
  withOpt opt $ \o -> parseEnum <$> nlopt_set_xtol_abs o tolptr

get_xtol_abs :: Opt -> IO (Result, V.Vector Double)
get_xtol_abs opt = do
  mutv <- get_dimension opt >>= MV.new . fromIntegral
  withOutputVector mutv $ \vecptr ->
    withOpt opt $ \o -> do
    result <- parseEnum <$> nlopt_get_xtol_abs o vecptr
    outvec <- V.unsafeFreeze mutv
    return (result, outvec)

foreign import ccall "nlopt.h nlopt_set_maxeval"
  nlopt_set_maxeval :: NloptOpt -> CInt -> IO CInt

foreign import ccall "nlopt.h nlopt_get_maxeval"
  nlopt_get_maxeval :: NloptOpt -> IO CInt

set_maxeval :: Opt -> Word -> IO Result
set_maxeval = setScalar nlopt_set_maxeval fromIntegral

get_maxeval :: Opt -> IO Word
get_maxeval = getScalar nlopt_get_maxeval fromIntegral

foreign import ccall "nlopt.h nlopt_set_maxtime"
  nlopt_set_maxtime :: NloptOpt -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_maxtime"
  nlopt_get_maxtime :: NloptOpt -> IO CDouble

set_maxtime :: Opt -> Double -> IO Result
set_maxtime = setScalar nlopt_set_maxtime realToFrac

get_maxtime :: Opt -> IO Double
get_maxtime = getScalar nlopt_get_maxtime realToFrac

foreign import ccall "nlopt.h nlopt_force_stop"
  nlopt_force_stop :: NloptOpt -> IO CInt

force_stop :: Opt -> IO Result
force_stop = useOpt $ fmap parseEnum . nlopt_force_stop

foreign import ccall "nlopt.h nlopt_set_force_stop"
  nlopt_set_force_stop :: NloptOpt -> CInt -> IO CInt

foreign import ccall "nlopt.h nlopt_get_force_stop"
  nlopt_get_force_stop :: NloptOpt -> IO CInt

set_force_stop :: Opt -> Word -> IO Result
set_force_stop = setScalar nlopt_set_force_stop fromIntegral

get_force_stop :: Opt -> IO Word
get_force_stop = getScalar nlopt_get_force_stop fromIntegral

{- Algorithm-specific configuration -}

foreign import ccall "nlopt.h nlopt_set_local_optimizer"
  nlopt_set_local_optimizer :: NloptOpt -> NloptOpt -> IO CInt

set_local_optimizer :: Opt -- ^ Primary optimizer
                    -> Opt -- ^ Subsidiary (local) optimizer
                    -> IO Result
set_local_optimizer p s =
  withOpt p $ \primary -> withOpt s $ \secondary ->
    parseEnum <$> nlopt_set_local_optimizer primary secondary

foreign import ccall "nlopt.h nlopt_set_population"
  nlopt_set_population :: NloptOpt -> Word -> IO CInt

foreign import ccall "nlopt.h nlopt_get_population"
  nlopt_get_population :: NloptOpt -> IO Word

set_population :: Opt -> Word -> IO Result
set_population = setScalar nlopt_set_population fromIntegral

get_population :: Opt -> IO Word
get_population = getScalar nlopt_get_population fromIntegral

foreign import ccall "nlopt.h nlopt_set_vector_storage"
  nlopt_set_vector_storage :: NloptOpt -> Word -> IO CInt

foreign import ccall "nlopt.h nlopt_get_vector_storage"
  nlopt_get_vector_storage :: NloptOpt -> IO Word

set_vector_storage :: Opt -> Word -> IO Result
set_vector_storage = setScalar nlopt_set_vector_storage fromIntegral

get_vector_storage :: Opt -> IO Word
get_vector_storage = getScalar nlopt_get_vector_storage fromIntegral

foreign import ccall "nlopt.h nlopt_set_default_initial_step"
  nlopt_set_default_initial_step :: NloptOpt -> Ptr CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_set_initial_step"
  nlopt_set_initial_step :: NloptOpt -> Ptr CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_set_initial_step1"
  nlopt_set_initial_step1 :: NloptOpt -> CDouble -> IO CInt

foreign import ccall "nlopt.h nlopt_get_initial_step"
  nlopt_get_initial_step :: NloptOpt -> Ptr CDouble -> Ptr CDouble -> IO CInt

set_default_initial_step :: Opt -> V.Vector Double -> IO Result
set_default_initial_step opt stepvec =
  withInputVector stepvec $ \stepptr ->
  withOpt opt $ \o -> parseEnum <$> nlopt_set_default_initial_step o stepptr

set_initial_step :: Opt -> V.Vector Double -> IO Result
set_initial_step opt stepvec =
  withInputVector stepvec $ \stepptr ->
  withOpt opt $ \o -> parseEnum <$> nlopt_set_initial_step o stepptr

set_initial_step1 :: Opt -> Double -> IO Result
set_initial_step1 = setScalar nlopt_set_initial_step1 realToFrac

get_initial_step :: Opt -> V.Vector Double -> IO (Result, V.Vector Double)
get_initial_step opt xvec = do
  mutv <- get_dimension opt >>= MV.new . fromIntegral
  withOutputVector mutv $ \outptr ->
    withInputVector xvec $ \inptr ->
    withOpt opt $ \o -> do
    result <- parseEnum <$> nlopt_get_initial_step o inptr outptr
    outvec <- V.unsafeFreeze mutv
    return (result, outvec)
