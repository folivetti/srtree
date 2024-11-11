{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}

{- |
Module      :  Numeric.NLOPT
Copyright   :  (c) Matthew Peddie 2017
License     :  BSD3
Maintainer  :  Matthew Peddie <mpeddie@gmail.com>
Stability   :  provisional
Portability :  GHC

This module provides a high-level, @hmatrix@-compatible interface to
the <http://ab-initio.mit.edu/wiki/index.php/NLopt NLOPT> library by
Steven G. Johnson.

NOTE: This is an adaptation from https://hackage.haskell.org/package/hmatrix-nlopt-0.2.0.0
that removes the dependency to hmatrix and support any Vector Storage.

= Documentation

Most non-numerical details are documented, but for specific
information on what the optimization methods do, how constraints are
handled, etc., you should consult:

  * The <http://ab-initio.mit.edu/wiki/index.php/NLopt_Introduction NLOPT introduction>

  * The <http://ab-initio.mit.edu/wiki/index.php/NLopt_Reference NLOPT reference manual>

  * The <http://ab-initio.mit.edu/wiki/index.php/NLopt_Algorithms NLOPT algorithm manual>

= Example program

The following interactive session example uses the Nelder-Mead simplex
algorithm, a derivative-free local optimizer, to minimize a trivial
function with a minimum of 22.0 at @(0, 0)@.

>>> import Numeric.LinearAlgebra ( dot, fromList )
>>> let objf x = x `dot` x + 22                         -- define objective
>>> let stop = ObjectiveRelativeTolerance 1e-6 :| []    -- define stopping criterion
>>> let algorithm = NELDERMEAD objf [] Nothing          -- specify algorithm
>>> let problem = LocalProblem 2 stop algorithm         -- specify problem
>>> let x0 = fromList [5, 10]                           -- specify initial guess
>>> minimizeLocal problem x0
Right (Solution {solutionCost = 22.0, solutionParams = [0.0,0.0], solutionResult = FTOL_REACHED})

-}

module Algorithm.SRTree.NonlinearOpt (
  -- * Specifying the objective function
  Objective
  , ObjectiveD
  , Preconditioner
  -- * Specifying the constraints
  -- ** Bound constraints
  , Bounds(..)
  -- ** Nonlinear constraints
  --
  -- $nonlinearconstraints

  -- *** Constraint functions
  , ScalarConstraint
  , ScalarConstraintD
  , VectorConstraint
  , VectorConstraintD
  -- *** Constraint types
  , Constraint(..)
  , EqualityConstraint(..)
  , InequalityConstraint(..)
  -- *** Collections of constraints
  , EqualityConstraints
  , EqualityConstraintsD
  , InequalityConstraints
  , InequalityConstraintsD
  -- * Stopping conditions
  --
  -- $nonempty
  , StoppingCondition(..)
  , NonEmpty(..)
  -- * Additional configuration
  , RandomSeed(..)
  , Population(..)
  , VectorStorage(..)
  , InitialStep(..)
  -- * Minimization problems
  -- ** Local minimization
  , LocalAlgorithm(..)
  , LocalProblem(..)
  , minimizeLocal
  -- ** Global minimization
  , GlobalAlgorithm(..)
  , GlobalProblem(..)
  , minimizeGlobal
  -- ** Minimization by augmented Lagrangian
  , AugLagAlgorithm(..)
  , AugLagProblem(..)
  , minimizeAugLag
  -- ** Results
  , Solution(..)
  , N.Result(..)
  ) where

import qualified Numeric.Optimization.NLOPT.Bindings as N

import Data.List.NonEmpty (NonEmpty(..))

import qualified Data.Vector.Storable as V
import Data.Vector.Storable ( Vector )

import Control.Exception ( Exception )
import qualified Control.Exception as Ex
import Data.Typeable ( Typeable )
import Data.Foldable ( traverse_ )

import System.IO.Unsafe ( unsafePerformIO )

-- each element i contains a row vec 
type Matrix a = [Vector a]

flatten :: V.Storable a => Matrix a -> Vector a 
flatten = V.concat
{-# INLINE flatten #-}

{- Function wrapping for the immutable HMatrix interface -}
wrapScalarFunction :: (Vector Double -> Double) -> N.ScalarFunction ()
wrapScalarFunction f params _ _ = return $ f params

wrapScalarFunctionD :: (Vector Double -> (Double, Vector Double))
                    -> N.ScalarFunction ()
wrapScalarFunctionD f params grad _ = do
  case grad of
    Nothing -> return ()
    Just g  -> V.copy g usergrad
  return result
  where
    (result, usergrad) = f params

wrapVectorFunction :: (Vector Double -> Word -> Vector Double)
                   -> Word -> N.VectorFunction ()
wrapVectorFunction f n params vout _ _ = V.copy vout $ f params n

wrapVectorFunctionD :: (Vector Double -> Word -> (Vector Double, Matrix Double))
                    -> Word -> N.VectorFunction ()
wrapVectorFunctionD f n params vout jac _ = do
  V.copy vout result
  case jac of
    Nothing -> return ()
    Just j -> V.copy j (flatten userjac)
  where
    (result, userjac) = f params n

wrapPreconditionerFunction :: (Vector Double -> Vector Double -> Vector Double)
                           -> N.PreconditionerFunction ()
wrapPreconditionerFunction f params v vpre _ = V.copy vpre (f params v)

{- Objective functions -}
-- | An objective function that calculates the objective value at the
-- given parameter vector.
type Objective
  = Vector Double  -- ^ Parameter vector
 -> Double  -- ^ Objective function value

-- | An objective function that calculates both the objective value
-- and the gradient of the objective with respect to the input
-- parameter vector, at the given parameter vector.
type ObjectiveD
  = Vector Double -- ^ Parameter vector
 -> (Double, Vector Double)  -- ^ (Objective function value, gradient)

-- | A preconditioner function, which computes @vpre = H(x) v@, where
-- @H@ is the Hessian matrix: the positive semi-definite second
-- derivative at the given parameter vector @x@, or an approximation
-- thereof.
type Preconditioner
  = Vector Double  -- ^ Parameter vector @x@
 -> Vector Double  -- ^ Vector @v@ to precondition at @x@
 -> Vector Double  -- ^ Preconditioned vector @vpre@

data ObjectiveFunction f
 = MinimumObjective f
 | PreconditionedMinimumObjective Preconditioner f

applyObjective :: N.Opt -> ObjectiveFunction Objective -> IO N.Result
applyObjective opt (MinimumObjective f) =
  N.set_min_objective opt (wrapScalarFunction f) ()
applyObjective opt (PreconditionedMinimumObjective p f) =
  N.set_precond_min_objective opt (wrapScalarFunction f)
  (wrapPreconditionerFunction p) ()

applyObjectiveD :: N.Opt -> ObjectiveFunction ObjectiveD -> IO N.Result
applyObjectiveD opt (MinimumObjective f) =
  N.set_min_objective opt (wrapScalarFunctionD f) ()
applyObjectiveD opt (PreconditionedMinimumObjective p f) =
  N.set_precond_min_objective opt (wrapScalarFunctionD f)
  (wrapPreconditionerFunction p) ()

{- Constraint functions -}
-- | A constraint function which returns @c(x)@ given the parameter
-- vector @x@.  The constraint will enforce that @c(x) == 0@ (equality
-- constraint) or @c(x) <= 0@ (inequality constraint).
type ScalarConstraint
  = Vector Double  -- ^ Parameter vector @x@
 -> Double  -- ^ Constraint violation (deviation from 0)

-- | A constraint function which returns @c(x)@ given the parameter
-- vector @x@ along with the gradient of @c(x)@ with respect to @x@ at
-- that point.  The constraint will enforce that @c(x) == 0@ (equality
-- constraint) or @c(x) <= 0@ (inequality constraint).
type ScalarConstraintD
  = Vector Double  -- ^ Parameter vector
 -> (Double, Vector Double)  -- ^ (Constraint violation, constraint gradient)

-- | A constraint function which returns a vector @c(x)@ given the
-- parameter vector @x@.  The constraint will enforce that @c(x) == 0@
-- (equality constraint) or @c(x) <= 0@ (inequality constraint).
type VectorConstraint
  = Vector Double  -- ^ Parameter vector
  -> Word           -- ^ Constraint Vectorize
  -> Vector Double  -- ^ Constraint violation vector

-- | A constraint function which returns @c(x)@ given the parameter
-- vector @x@ along with the Jacobian (first derivative) matrix of
-- @c(x)@ with respect to @x@ at that point.  The constraint will
-- enforce that @c(x) == 0@ (equality constraint) or @c(x) <= 0@
-- (inequality constraint).
type VectorConstraintD
  = Vector Double  -- ^ Parameter vector
  -> Word  -- ^ Constraint Vectorize
  -> (Vector Double, Matrix Double)  -- ^ (Constraint violation vector,
                                     -- constraint Jacobian)

-- $nonlinearconstraints
--
-- Note that most NLOPT algorithms do not support nonlinear
-- constraints natively; if you need to enforce nonlinear constraints,
-- you may want to use the 'AugLagAlgorithm' family of solvers, which
-- can add nonlinear constraints to some algorithm that does not
-- support them by a principled modification of the objective
-- function.
--
-- == Example program
--
-- The following interactive session example enforces a scalar
-- constraint on the problem given in the beginning of the module: the
-- parameters must always sum to 1.  The minimizer finds a constrained
-- minimum of 22.5 at @(0.5, 0.5)@.
--
-- >>> import Numeric.LinearAlgebra ( dot, fromList, toList )
-- >>> let objf x = x `dot` x + 22
-- >>> let stop = ObjectiveRelativeTolerance 1e-9 :| []
-- >>>          -- define constraint function:
-- >>> let constraintf x = sum (toList x) - 1.0
-- >>>          -- define constraint object to pass to the algorithm:
-- >>> let constraint = EqualityConstraint (Scalar constraintf) 1e-6
-- >>> let algorithm = COBYLA objf [] [] [constraint] Nothing
-- >>> let problem = LocalProblem 2 stop algorithm
-- >>> let x0 = fromList [5, 10]
-- >>> minimizeLocal problem x0
-- Right (Solution {solutionCost = 22.500000000013028, solutionParams = [0.5000025521533521,0.49999744784664796], solutionResult = FTOL_REACHED})


data Constraint s v
  -- | A scalar constraint.
  = Scalar s
  -- | A vector constraint.
  | Vector Word v
  -- | A scalar constraint with an attached preconditioning function.
  | Preconditioned Preconditioner s

-- | An equality constraint, comprised of both the constraint function
-- (or functions, if a preconditioner is used) along with the desired
-- tolerance.
data EqualityConstraint s v = EqualityConstraint
  { eqConstraintFunctions :: Constraint s v
  , eqConstraintTolerance :: Double
  }

-- | An inequality constraint, comprised of both the constraint
-- function (or functions, if a preconditioner is used) along with the
-- desired tolerance.
data InequalityConstraint s v = InequalityConstraint
  { ineqConstraintFunctions :: Constraint s v
  , ineqConstraintTolerance :: Double
  }

-- | A collection of equality constraints that do not supply
-- constraint derivatives.
type EqualityConstraints =
  [EqualityConstraint ScalarConstraint VectorConstraint]

-- | A collection of inequality constraints that do not supply
-- constraint derivatives.
type InequalityConstraints =
  [InequalityConstraint ScalarConstraint VectorConstraint]

-- | A collection of equality constraints that supply constraint
-- derivatives.
type EqualityConstraintsD = [EqualityConstraint ScalarConstraintD VectorConstraintD]

-- | A collection of inequality constraints that supply constraint
-- derivatives.
type InequalityConstraintsD = [InequalityConstraint ScalarConstraintD VectorConstraintD]

class ApplyConstraint constraint where
  applyConstraint :: N.Opt -> constraint -> IO N.Result

instance ApplyConstraint (EqualityConstraint ScalarConstraint VectorConstraint) where
  applyConstraint opt (EqualityConstraint ty tol) = case ty of
    Scalar s           ->
      N.add_equality_constraint opt (wrapScalarFunction s) () tol
    Vector n v         ->
      N.add_equality_mconstraint opt n (wrapVectorFunction v n) () tol
    Preconditioned p s ->
      N.add_precond_equality_constraint opt (wrapScalarFunction s)
      (wrapPreconditionerFunction p) () tol

instance ApplyConstraint (InequalityConstraint ScalarConstraint VectorConstraint) where
  applyConstraint opt (InequalityConstraint ty tol) = case ty of
    Scalar s           ->
      N.add_inequality_constraint opt (wrapScalarFunction s) () tol
    Vector n v         ->
      N.add_inequality_mconstraint opt n (wrapVectorFunction v n) () tol
    Preconditioned p s ->
      N.add_precond_inequality_constraint opt (wrapScalarFunction s)
      (wrapPreconditionerFunction p) () tol

instance ApplyConstraint (EqualityConstraint ScalarConstraintD VectorConstraintD) where
  applyConstraint opt (EqualityConstraint ty tol) = case ty of
    Scalar s           ->
      N.add_equality_constraint opt (wrapScalarFunctionD s) () tol
    Vector n v         ->
      N.add_equality_mconstraint opt n (wrapVectorFunctionD v n) () tol
    Preconditioned p s ->
      N.add_precond_equality_constraint opt (wrapScalarFunctionD s)
      (wrapPreconditionerFunction p) () tol

instance ApplyConstraint (InequalityConstraint ScalarConstraintD VectorConstraintD) where
  applyConstraint opt (InequalityConstraint ty tol) = case ty of
    Scalar s           ->
      N.add_inequality_constraint opt (wrapScalarFunctionD s) () tol
    Vector n v         ->
      N.add_inequality_mconstraint opt n (wrapVectorFunctionD v n) () tol
    Preconditioned p s ->
      N.add_precond_inequality_constraint opt (wrapScalarFunctionD s)
      (wrapPreconditionerFunction p) () tol

{- Bounds -}

-- | Bound constraints are specified by vectors of the same dimension
-- as the parameter space.
--
-- == Example program
--
-- The following interactive session example enforces lower bounds on
-- the example from the beginning of the module.  This prevents the
-- optimizer from locating the true minimum at @(0, 0)@; a slightly
-- higher constrained minimum at @(1, 1)@ is found.  Note that the
-- optimizer returns 'N.XTOL_REACHED' rather than 'N.FTOL_REACHED',
-- because the bound constraint is active at the final minimum.
--
-- >>> import Numeric.LinearAlgebra ( dot, fromList )
-- >>> let objf x = x `dot` x + 22                           -- define objective
-- >>> let stop = ObjectiveRelativeTolerance 1e-6 :| []      -- define stopping criterion
-- >>> let lowerbound = LowerBounds $ fromList [1, 1]        -- specify bounds
-- >>> let algorithm = NELDERMEAD objf [lowerbound] Nothing  -- specify algorithm
-- >>> let problem = LocalProblem 2 stop algorithm           -- specify problem
-- >>> let x0 = fromList [5, 10]                             -- specify initial guess
-- >>> minimizeLocal problem x0
-- Right (Solution {solutionCost = 24.0, solutionParams = [1.0,1.0], solutionResult = XTOL_REACHED})
data Bounds
  -- | Lower bound vector @v@ means we want @x >= v@.
 = LowerBounds (Vector Double)
 -- | Upper bound vector @u@ means we want @x <= u@.
 | UpperBounds (Vector Double)
 deriving (Eq, Show, Read)

applyBounds :: N.Opt -> Bounds -> IO N.Result
applyBounds opt (LowerBounds lbvec) = N.set_lower_bounds opt lbvec
applyBounds opt (UpperBounds ubvec) = N.set_upper_bounds opt ubvec

{- Stopping conditions -}

-- | A 'StoppingCondition' tells NLOPT when to stop working on a
-- minimization problem.  When multiple 'StoppingCondition's are
-- provided, the problem will stop when any one condition is met.
data StoppingCondition
  -- | Stop minimizing when an objective value @J@ less than or equal
  -- to the provided value is found.
  = MinimumValue Double
  -- | Stop minimizing when an optimization step changes the objective
  -- value @J@ by less than the provided tolerance multiplied by @|J|@.
  | ObjectiveRelativeTolerance Double
  -- | Stop minimizing when an optimization step changes the objective
  -- value by less than the provided tolerance.
  | ObjectiveAbsoluteTolerance Double
  -- | Stop when an optimization step changes /every element/ of the
  -- parameter vector @x@ by less than @x@ scaled by the provided
  -- tolerance.
  | ParameterRelativeTolerance Double
  -- | Stop when an optimization step changes /every element/ of the
  -- parameter vector @x@ by less than the corresponding element in
  -- the provided vector of tolerances values.
  | ParameterAbsoluteTolerance (Vector Double)
  -- | Stop when the number of evaluations of the objective function
  -- exceeds the provided count.
  | MaximumEvaluations Word
  -- | Stop when the optimization time exceeds the provided time (in
  -- seconds).  This is not a precise limit.
  | MaximumTime Double
  deriving (Eq, Show, Read)

-- $nonempty
--
-- The 'NonEmpty' data type from 'Data.List.NonEmpty' is re-exported
-- here, because it is used to ensure that you always specify at least
-- one stopping condition.

applyStoppingCondition :: N.Opt -> StoppingCondition -> IO N.Result
applyStoppingCondition opt (MinimumValue x) = N.set_stopval opt x
applyStoppingCondition opt (ObjectiveRelativeTolerance x) = N.set_ftol_rel opt x
applyStoppingCondition opt (ObjectiveAbsoluteTolerance x) = N.set_ftol_abs opt x
applyStoppingCondition opt (ParameterRelativeTolerance x) = N.set_xtol_rel opt x
applyStoppingCondition opt (ParameterAbsoluteTolerance v) = N.set_xtol_abs opt v
applyStoppingCondition opt (MaximumEvaluations n) = N.set_maxeval opt n
applyStoppingCondition opt (MaximumTime deltat) = N.set_maxtime opt deltat

{- Random seed control -}

-- | This specifies how to initialize the random number generator for
-- stochastic algorithms.
data RandomSeed
  -- | Seed the RNG with the provided value.
  = SeedValue Word
  -- | Seed the RNG using the system clock.
  | SeedFromTime
  -- | Don't perform any explicit initialization of the RNG.
  | Don'tSeed
  deriving (Eq, Show, Read)

applyRandomSeed :: RandomSeed -> IO ()
applyRandomSeed Don'tSeed = return ()
applyRandomSeed (SeedValue n) = N.srand n
applyRandomSeed SeedFromTime = N.srand_time

{- Random stuff -}

-- | This specifies the population size for algorithms that use a pool
-- of solutions.
newtype Population = Population Word deriving (Eq, Show, Read)

applyPopulation :: N.Opt -> Population -> IO N.Result
applyPopulation opt (Population n) = N.set_population opt n

-- | This specifies the memory size to be used by algorithms like
-- 'LBFGS' which store approximate Hessian or Jacobian matrices.
newtype VectorStorage = VectorStorage Word deriving (Eq, Show, Read)

applyVectorStorage :: N.Opt -> VectorStorage -> IO N.Result
applyVectorStorage opt (VectorStorage n) = N.set_vector_storage opt n

-- | This vector with the same dimension as the parameter vector @x@
-- specifies the initial step for the optimizer to take.  (This
-- applies to local gradient-free algorithms, which cannot use
-- gradients to estimate how big a step to take.)
newtype InitialStep = InitialStep (Vector Double) deriving (Eq, Show, Read)

applyInitialStep :: N.Opt -> InitialStep -> IO N.Result
applyInitialStep opt (InitialStep v) = N.set_initial_step opt v

{- Algorithms -}

data GlobalProblem = GlobalProblem
  { lowerBounds :: Vector Double        -- ^ Lower bounds for @x@
  , upperBounds :: Vector Double        -- ^ Upper bounds for @x@
  , gstop :: NonEmpty StoppingCondition -- ^ At least one stopping
                                        -- condition
  , galgorithm :: GlobalAlgorithm       -- ^ Algorithm specification
  }

-- | These are the global minimization algorithms provided by NLOPT.  Please see
-- <http://ab-initio.mit.edu/wiki/index.php/NLopt_Algorithms the NLOPT algorithm manual>
-- for more details on how the methods work and how they relate to one another.
--
-- Optional parameters are wrapped in a 'Maybe'; for example, if you
-- see 'Maybe' 'Population', you can simply specify 'Nothing' to use
-- the default behavior.
data GlobalAlgorithm
    -- | DIviding RECTangles
  = DIRECT Objective
    -- | DIviding RECTangles, locally-biased variant
  | DIRECT_L Objective
    -- | DIviding RECTangles, "slightly randomized"
  | DIRECT_L_RAND Objective RandomSeed
    -- | DIviding RECTangles, unscaled version
  | DIRECT_NOSCAL Objective
    -- | DIviding RECTangles, locally-biased and unscaled
  | DIRECT_L_NOSCAL Objective
    -- | DIviding RECTangles, locally-biased, unscaled and "slightly
    -- randomized"
  | DIRECT_L_RAND_NOSCAL Objective RandomSeed
    -- | DIviding RECTangles, original FORTRAN implementation
  | ORIG_DIRECT Objective InequalityConstraints
    -- | DIviding RECTangles, locally-biased, original FORTRAN
    -- implementation
  | ORIG_DIRECT_L Objective InequalityConstraints
    -- | Stochastic Global Optimization.
    -- __This algorithm is only available if you have linked with @libnlopt_cxx@.__
  | STOGO ObjectiveD
    -- | Stochastic Global Optimization, randomized variant.
    -- __This algorithm is only available if you have linked with @libnlopt_cxx@.__
  | STOGO_RAND ObjectiveD RandomSeed
    -- | Controlled Random Search with Local Mutation
  | CRS2_LM Objective RandomSeed (Maybe Population)
    -- | Improved Stochastic Ranking Evolution Strategy
  | ISRES Objective InequalityConstraints EqualityConstraints RandomSeed (Maybe Population)
    -- | Evolutionary Algorithm
  | ESCH Objective
    -- | Original Multi-Level Single-Linkage
  | MLSL Objective LocalProblem (Maybe Population)
    -- | Multi-Level Single-Linkage with Sobol Low-Discrepancy
    -- Sequence for starting points
  | MLSL_LDS Objective LocalProblem (Maybe Population)

algorithmEnumOfGlobal :: GlobalAlgorithm -> N.Algorithm
algorithmEnumOfGlobal (DIRECT _)                 = N.GN_DIRECT
algorithmEnumOfGlobal (DIRECT_L _)               = N.GN_DIRECT_L
algorithmEnumOfGlobal (DIRECT_L_RAND _ _)        = N.GN_DIRECT_L_RAND
algorithmEnumOfGlobal (DIRECT_NOSCAL _)          = N.GN_DIRECT_NOSCAL
algorithmEnumOfGlobal (DIRECT_L_NOSCAL _)        = N.GN_DIRECT_L_NOSCAL
algorithmEnumOfGlobal (DIRECT_L_RAND_NOSCAL _ _) = N.GN_DIRECT_L_RAND_NOSCAL
algorithmEnumOfGlobal (ORIG_DIRECT _ _)          = N.GN_ORIG_DIRECT
algorithmEnumOfGlobal (ORIG_DIRECT_L _ _)        = N.GN_ORIG_DIRECT_L
algorithmEnumOfGlobal (STOGO _)                  = N.GD_STOGO
algorithmEnumOfGlobal (STOGO_RAND _ _)           = N.GD_STOGO_RAND
algorithmEnumOfGlobal (CRS2_LM _ _ _)            = N.GN_CRS2_LM
algorithmEnumOfGlobal (ISRES _ _ _ _ _)          = N.GN_ISRES
algorithmEnumOfGlobal (ESCH _)                   = N.GN_ESCH
algorithmEnumOfGlobal (MLSL _ _ _)               = N.G_MLSL
algorithmEnumOfGlobal (MLSL_LDS _ _ _)           = N.G_MLSL_LDS

applyGlobalObjective :: N.Opt -> GlobalAlgorithm -> IO ()
applyGlobalObjective opt alg = go alg
  where
    obj = tryTo . applyObjective opt . MinimumObjective
    objD = tryTo . applyObjectiveD opt . MinimumObjective

    go (DIRECT o)                 = obj o
    go (DIRECT_L o)               = obj o
    go (DIRECT_NOSCAL o)          = obj o
    go (DIRECT_L_NOSCAL o)        = obj o
    go (ESCH o)                   = obj o
    go (STOGO o)                  = objD o
    go (DIRECT_L_RAND o _)        = obj o
    go (DIRECT_L_RAND_NOSCAL o _) = obj o
    go (ORIG_DIRECT o _)          = obj o
    go (ORIG_DIRECT_L o _)        = obj o
    go (STOGO_RAND o _)           = objD o
    go (CRS2_LM o _ _)            = obj o
    go (ISRES o _ _ _ _)          = obj o
    go (MLSL o _ _)               = obj o
    go (MLSL_LDS o _ _)           = obj o

applyGlobalAlgorithm :: N.Opt -> GlobalAlgorithm -> IO ()
applyGlobalAlgorithm opt alg = do
  applyGlobalObjective opt alg
  go alg
  where
    seed = applyRandomSeed
    pop = maybe (return ()) (tryTo . applyPopulation opt)
    ic = traverse_ (tryTo . applyConstraint opt)
    ec = traverse_ (tryTo . applyConstraint opt)

    local lp = setupLocalProblem lp >>= N.set_local_optimizer opt

    go (DIRECT_L_RAND _ s)        = seed s
    go (DIRECT_L_RAND_NOSCAL _ s) = seed s
    go (ORIG_DIRECT _ ineq)       = ic ineq
    go (ORIG_DIRECT_L _ ineq)     = ic ineq
    go (STOGO_RAND _ s)           = seed s
    go (CRS2_LM _ s p)            = seed s *> pop p
    go (ISRES _ ineq eq s p)      = ic ineq *> ec eq *> seed s *> pop p
    go (MLSL _ lp p)              = local lp *> pop p
    go (MLSL_LDS _ lp p)          = local lp *> pop p
    go _                          = return ()

tryTo :: IO N.Result -> IO ()
tryTo act = do
  result <- act
  if (N.isSuccess result)
    then return ()
    else Ex.throw $ NloptException result

data NloptException = NloptException N.Result deriving (Show, Typeable)
instance Exception NloptException

-- | Solve the specified global optimization problem.
--
-- = Example program
--
-- The following interactive session example uses the 'ISRES'
-- algorithm, a stochastic, derivative-free global optimizer, to
-- minimize a trivial function with a minimum of 22.0 at @(0, 0)@.
-- The search is conducted within a box from -10 to 10 in each
-- dimension.
--
-- >>> import Numeric.LinearAlgebra ( dot, fromList )
-- >>> let objf x = x `dot` x + 22                              -- define objective
-- >>> let stop = ObjectiveRelativeTolerance 1e-12 :| []        -- define stopping criterion
-- >>> let algorithm = ISRES objf [] [] (SeedValue 22) Nothing  -- specify algorithm
-- >>> let lowerbounds = fromList [-10, -10]                    -- specify bounds
-- >>> let upperbounds = fromList [10, 10]                      -- specify bounds
-- >>> let problem = GlobalProblem lowerbounds upperbounds stop algorithm
-- >>> let x0 = fromList [5, 8]                                 -- specify initial guess
-- >>> minimizeGlobal problem x0
-- Right (Solution {solutionCost = 22.000000000002807, solutionParams = [-1.660591102367038e-6,2.2407062393213684e-7], solutionResult = FTOL_REACHED})
minimizeGlobal :: GlobalProblem  -- ^ Problem specification
               -> Vector Double  -- ^ Initial parameter guess
               -> Either N.Result Solution  -- ^ Optimization results
minimizeGlobal prob x0 =
  unsafePerformIO $ (Right <$> minimizeGlobal' prob x0) `Ex.catch` handler
  where
    handler :: NloptException -> IO (Either N.Result a)
    handler (NloptException retcode) = return $ Left retcode

applyGlobalProblem :: N.Opt -> GlobalProblem -> IO ()
applyGlobalProblem opt (GlobalProblem lb ub stop alg) = do
  tryTo $ applyBounds opt (LowerBounds lb)
  tryTo $ applyBounds opt (UpperBounds ub)
  traverse_ (tryTo . applyStoppingCondition opt) stop
  applyGlobalAlgorithm opt alg

newOpt :: N.Algorithm -> Word -> IO N.Opt
newOpt alg sz = do
  opt' <- N.create alg sz
  case opt' of
    Nothing -> Ex.throw $ NloptException N.FAILURE
    Just opt -> return opt

setupGlobalProblem :: GlobalProblem -> IO N.Opt
setupGlobalProblem gp@(GlobalProblem _ _ _ alg) = do
  opt <- newOpt (algorithmEnumOfGlobal alg) (problemSize gp)
  applyGlobalProblem opt gp
  return opt

solveProblem :: N.Opt -> Vector Double -> IO Solution
solveProblem opt x0 = do
  (N.Output outret outcost outx nevals) <- N.optimize opt x0
  if (N.isSuccess outret)
    then return $ Solution outcost outx outret nevals
    else Ex.throw $ NloptException outret

minimizeGlobal' :: GlobalProblem -> Vector Double -> IO Solution
minimizeGlobal' gp x0 = do
  opt <- setupGlobalProblem gp
  solveProblem opt x0

data LocalProblem = LocalProblem
  { lsize :: Word                       -- ^ The dimension of the
                                        -- parameter vector.
  , lstop :: NonEmpty StoppingCondition -- ^ At least one stopping
                                        -- condition
  , lalgorithm :: LocalAlgorithm        -- ^ Algorithm specification
  }

-- | These are the local minimization algorithms provided by NLOPT.  Please see
-- <http://ab-initio.mit.edu/wiki/index.php/NLopt_Algorithms the NLOPT algorithm manual>
-- for more details on how the methods work and how they relate to one
-- another.  Note that some local methods require you provide
-- derivatives (gradients or Jacobians) for your objective function
-- and constraint functions.
--
-- Optional parameters are wrapped in a 'Maybe'; for example, if you
-- see 'Maybe' 'VectorStorage', you can simply specify 'Nothing' to
-- use the default behavior.
data LocalAlgorithm
    -- | Limited-memory BFGS
  = LBFGS_NOCEDAL ObjectiveD (Maybe VectorStorage)
    -- | Limited-memory BFGS
  | LBFGS ObjectiveD (Maybe VectorStorage)
    -- | Shifted limited-memory variable-metric, rank-2
  | VAR2 ObjectiveD (Maybe VectorStorage)
    -- | Shifted limited-memory variable-metric, rank-1
  | VAR1 ObjectiveD (Maybe VectorStorage)
    -- | Truncated Newton's method
  | TNEWTON ObjectiveD (Maybe VectorStorage)
    -- | Truncated Newton's method with automatic restarting
  | TNEWTON_RESTART ObjectiveD (Maybe VectorStorage)
    -- | Preconditioned truncated Newton's method
  | TNEWTON_PRECOND ObjectiveD (Maybe VectorStorage)
    -- | Preconditioned truncated Newton's method with automatic
    -- restarting
  | TNEWTON_PRECOND_RESTART ObjectiveD (Maybe VectorStorage)
    -- | Method of moving averages
  | MMA ObjectiveD InequalityConstraintsD
    -- | Sequential Least-Squares Quadratic Programming
  | SLSQP ObjectiveD [Bounds] InequalityConstraintsD EqualityConstraintsD
    -- | Conservative Convex Separable Approximation
  | CCSAQ ObjectiveD Preconditioner
    -- | PRincipal AXIS gradient-free local optimization
  | PRAXIS Objective [Bounds] (Maybe InitialStep)
    -- | Constrained Optimization BY Linear Approximations
  | COBYLA Objective [Bounds] InequalityConstraints EqualityConstraints
    (Maybe InitialStep)
    -- | Powell's NEWUOA algorithm
  | NEWUOA Objective (Maybe InitialStep)
    -- | Powell's NEWUOA algorithm with bounds by SGJ
  | NEWUOA_BOUND Objective [Bounds] (Maybe InitialStep)
    -- | Nelder-Mead Simplex gradient-free method
  | NELDERMEAD Objective [Bounds] (Maybe InitialStep)
    -- | NLOPT implementation of Rowan's Subplex algorithm
  | SBPLX Objective [Bounds] (Maybe InitialStep)
    -- | Bounded Optimization BY Quadratic Approximations
  | BOBYQA Objective [Bounds] (Maybe InitialStep)

algorithmEnumOfLocal :: LocalAlgorithm -> N.Algorithm
algorithmEnumOfLocal (LBFGS_NOCEDAL _ _)           = N.LD_LBFGS_NOCEDAL
algorithmEnumOfLocal (LBFGS _ _)                   = N.LD_LBFGS
algorithmEnumOfLocal (VAR2 _ _)                    = N.LD_VAR2
algorithmEnumOfLocal (VAR1 _ _)                    = N.LD_VAR1
algorithmEnumOfLocal (TNEWTON _ _)                 = N.LD_TNEWTON
algorithmEnumOfLocal (TNEWTON_RESTART _ _)         = N.LD_TNEWTON_RESTART
algorithmEnumOfLocal (TNEWTON_PRECOND _ _)         = N.LD_TNEWTON_PRECOND
algorithmEnumOfLocal (TNEWTON_PRECOND_RESTART _ _) = N.LD_TNEWTON_PRECOND_RESTART
algorithmEnumOfLocal (MMA _ _)                     = N.LD_MMA
algorithmEnumOfLocal (SLSQP _ _ _ _)               = N.LD_SLSQP
algorithmEnumOfLocal (CCSAQ _ _)                   = N.LD_CCSAQ
algorithmEnumOfLocal (PRAXIS _ _ _)                = N.LN_PRAXIS
algorithmEnumOfLocal (COBYLA _ _ _ _ _)            = N.LN_COBYLA
algorithmEnumOfLocal (NEWUOA _ _)                  = N.LN_NEWUOA
algorithmEnumOfLocal (NEWUOA_BOUND _ _ _)          = N.LN_NEWUOA
algorithmEnumOfLocal (NELDERMEAD _ _ _)            = N.LN_NELDERMEAD
algorithmEnumOfLocal (SBPLX _ _ _)                 = N.LN_SBPLX
algorithmEnumOfLocal (BOBYQA _ _ _)                = N.LN_BOBYQA

applyLocalObjective :: N.Opt -> LocalAlgorithm -> IO ()
applyLocalObjective opt alg = go alg
  where
    obj = tryTo . applyObjective opt . MinimumObjective
    objD = tryTo . applyObjectiveD opt . MinimumObjective
    precond p = tryTo . applyObjectiveD opt . PreconditionedMinimumObjective p

    go (LBFGS_NOCEDAL o _)           = objD o
    go (LBFGS o _)                   = objD o
    go (VAR2 o _)                    = objD o
    go (VAR1 o _)                    = objD o
    go (TNEWTON o _)                 = objD o
    go (TNEWTON_RESTART o _)         = objD o
    go (TNEWTON_PRECOND o _)         = objD o
    go (TNEWTON_PRECOND_RESTART o _) = objD o
    go (MMA o _)                     = objD o
    go (SLSQP o _ _ _)               = objD o
    go (CCSAQ o prec)                = precond prec o
    go (PRAXIS o _ _)                = obj o
    go (COBYLA o _ _ _ _)            = obj o
    go (NEWUOA o _)                  = obj o
    go (NEWUOA_BOUND o _ _)          = obj o
    go (NELDERMEAD o _ _)            = obj o
    go (SBPLX o _ _)                 = obj o
    go (BOBYQA o _ _)                = obj o

applyLocalAlgorithm :: N.Opt -> LocalAlgorithm -> IO ()
applyLocalAlgorithm opt alg = do
  applyLocalObjective opt alg
  go alg
  where
    ic = traverse_ (tryTo . applyConstraint opt)
    icd = traverse_ (tryTo . applyConstraint opt)
    ec = traverse_ (tryTo . applyConstraint opt)
    ecd = traverse_ (tryTo . applyConstraint opt)
    store = maybe (return ()) (tryTo . applyVectorStorage opt)
    bound = traverse_ (tryTo . applyBounds opt)
    step0 = maybe (return ()) (tryTo . applyInitialStep opt)

    go (LBFGS_NOCEDAL _ vs)           = store vs
    go (LBFGS _ vs)                   = store vs
    go (VAR2 _ vs)                    = store vs
    go (VAR1 _ vs)                    = store vs
    go (TNEWTON _ vs)                 = store vs
    go (TNEWTON_RESTART _ vs)         = store vs
    go (TNEWTON_PRECOND _ vs)         = store vs
    go (TNEWTON_PRECOND_RESTART _ vs) = store vs
    go (MMA _ ineqd)                  = icd ineqd
    go (SLSQP _ b ineqd eqd)          =
      bound b *> icd ineqd *> ecd eqd
    go (CCSAQ _ _   )                 = return ()
    go (PRAXIS _ b s)                 = bound b *> step0 s
    go (COBYLA _ b ineq eq s)         =
      bound b *> ic ineq *> ec eq *> step0 s
    go (NEWUOA _ s)                   = step0 s
    go (NEWUOA_BOUND _ b s)           = bound b *> step0 s
    go (NELDERMEAD _ b s)             = bound b *> step0 s
    go (SBPLX _ b s)                  = bound b *> step0 s
    go (BOBYQA _ b s)                 = bound b *> step0 s

applyLocalProblem :: N.Opt -> LocalProblem -> IO ()
applyLocalProblem opt (LocalProblem _ stop alg) = do
  traverse_ (tryTo . applyStoppingCondition opt) stop
  applyLocalAlgorithm opt alg

setupLocalProblem :: LocalProblem -> IO N.Opt
setupLocalProblem lp@(LocalProblem sz _ alg) = do
  opt <- newOpt (algorithmEnumOfLocal alg) sz
  applyLocalProblem opt lp
  return opt

minimizeLocal' :: LocalProblem -> Vector Double -> IO Solution
minimizeLocal' lp x0 = do
  opt <- setupLocalProblem lp
  solveProblem opt x0

-- |
-- == Example program
--
-- The following interactive session example enforces the same scalar
-- constraint as the nonlinear constraint example, but this time it
-- uses the SLSQP solver to find the minimum.
--
-- >>> import Numeric.LinearAlgebra ( dot, fromList, toList, scale )
-- >>> let objf x = (x `dot` x + 22, 2 `scale` x)
-- >>> let stop = ObjectiveRelativeTolerance 1e-9 :| []
-- >>> let constraintf x = (sum (toList x) - 1.0, fromList [1, 1])
-- >>> let constraint = EqualityConstraint (Scalar constraintf) 1e-6
-- >>> let algorithm = SLSQP objf [] [] [constraint]
-- >>> let problem = LocalProblem 2 stop algorithm
-- >>> let x0 = fromList [5, 10]
-- >>> minimizeLocal problem x0
-- Right (Solution {solutionCost = 22.5, solutionParams = [0.4999999999999998,0.5000000000000002], solutionResult = FTOL_REACHED})
minimizeLocal :: LocalProblem -> Vector Double -> Either N.Result Solution
minimizeLocal prob x0 =
  unsafePerformIO $ (Right <$> minimizeLocal' prob x0) `Ex.catch` handler
  where
    handler :: NloptException -> IO (Either N.Result a)
    handler (NloptException retcode) = return $ Left retcode

class ProblemSize c where
  problemSize :: c -> Word

instance ProblemSize LocalProblem where
  problemSize = lsize

instance ProblemSize GlobalProblem where
  problemSize = fromIntegral . V.length . lowerBounds

instance ProblemSize AugLagProblem where
  problemSize (AugLagProblem _ _ alg) = case alg of
    AUGLAG_LOCAL lp _ _  -> problemSize lp
    AUGLAG_EQ_LOCAL lp   -> problemSize lp
    AUGLAG_GLOBAL gp _ _ -> problemSize gp
    AUGLAG_EQ_GLOBAL gp  -> problemSize gp


-- | __IMPORTANT NOTE__
--
-- For augmented lagrangian problems, you, the user, are responsible
-- for providing the appropriate type of constraint.  If the
-- subsidiary problem requires an `ObjectiveD`, then you should
-- provide constraint functions with derivatives.  If the subsidiary
-- problem requires an `Objective`, you should provide constraint
-- functions without derivatives.  If you don't do this, you may get a
-- runtime error.
data AugLagProblem = AugLagProblem
  { alEquality :: EqualityConstraints   -- ^ Possibly empty set of
                                        -- equality constraints
  , alEqualityD :: EqualityConstraintsD -- ^ Possibly empty set of
                                        -- equality constraints with
                                        -- derivatives
  , alalgorithm :: AugLagAlgorithm      -- ^ Algorithm specification.
  }

-- | The Augmented Lagrangian solvers allow you to enforce nonlinear
-- constraints while using local or global algorithms that don't
-- natively support them.  The subsidiary problem is used to do the
-- minimization, but the @AUGLAG@ methods modify the objective to
-- enforce the constraints.  Please see
-- <http://ab-initio.mit.edu/wiki/index.php/NLopt_Algorithms the NLOPT algorithm manual>
-- for more details on how the methods work and how they relate to one another.
--
-- See the documentation for 'AugLagProblem' for an important note
-- about the constraint functions.
data AugLagAlgorithm
    -- | AUGmented LAGrangian with a local subsidiary method
  = AUGLAG_LOCAL LocalProblem InequalityConstraints InequalityConstraintsD
    -- | AUGmented LAGrangian with a local subsidiary method and with
    -- penalty functions only for equality constraints
  | AUGLAG_EQ_LOCAL LocalProblem
    -- | AUGmented LAGrangian with a global subsidiary method
  | AUGLAG_GLOBAL GlobalProblem InequalityConstraints InequalityConstraintsD
    -- | AUGmented LAGrangian with a global subsidiary method and with
    -- penalty functions only for equality constraints.
  | AUGLAG_EQ_GLOBAL GlobalProblem

algorithmEnumOfAugLag :: AugLagAlgorithm -> N.Algorithm
algorithmEnumOfAugLag (AUGLAG_LOCAL _ _ _) = N.AUGLAG
algorithmEnumOfAugLag (AUGLAG_EQ_LOCAL _) = N.AUGLAG_EQ
algorithmEnumOfAugLag (AUGLAG_GLOBAL _ _ _) = N.AUGLAG
algorithmEnumOfAugLag (AUGLAG_EQ_GLOBAL _) = N.AUGLAG_EQ

-- | This structure is returned in the event of a successful
-- optimization.
data Solution = Solution
  { solutionCost :: Double          -- ^ The objective function value
                                    -- at the minimum
  , solutionParams :: Vector Double -- ^ The parameter vector which
                                    -- minimizes the objective
  , solutionResult :: N.Result      -- ^ Why the optimizer stopped

  , nEvals :: Int                   -- ^ Number of evaluations until stop
  } deriving (Eq, Show, Read)

applyAugLagAlgorithm :: N.Opt -> AugLagAlgorithm -> IO ()
applyAugLagAlgorithm opt alg = go alg
  where
    ic = traverse_ (tryTo . applyConstraint opt)
    icd = traverse_ (tryTo . applyConstraint opt)
    -- AUGLAG won't work at all if you don't pass it the same
    -- objective as the subproblem -- here we pull out the subproblem
    -- objectives from the algorithm spec and set the same objective
    -- function so the user can't mess it up.
    local lp = tryTo $ do
      localopt <- setupLocalProblem lp
      applyLocalObjective opt (lalgorithm lp)
      N.set_local_optimizer opt localopt
    global gp = do
      tryTo $ setupGlobalProblem gp >>= N.set_local_optimizer opt
      applyGlobalObjective opt (galgorithm gp)

    go (AUGLAG_LOCAL lp ineq ineqd)  = local lp *> ic ineq *> icd ineqd
    go (AUGLAG_EQ_LOCAL lp)          = local lp
    go (AUGLAG_GLOBAL gp ineq ineqd) = global gp *> ic ineq *> icd ineqd
    go (AUGLAG_EQ_GLOBAL gp)         = global gp

applyAugLagProblem :: N.Opt -> AugLagProblem -> IO ()
applyAugLagProblem opt (AugLagProblem eq eqd alg) = do
  traverse_ (tryTo . applyConstraint opt) eq
  traverse_ (tryTo . applyConstraint opt) eqd
  applyAugLagAlgorithm opt alg

minimizeAugLag' :: AugLagProblem -> Vector Double -> IO Solution
minimizeAugLag' ap@(AugLagProblem _ _ alg) x0 = do
  opt <- newOpt (algorithmEnumOfAugLag alg) (problemSize ap)
  applyAugLagProblem opt ap
  solveProblem opt x0

-- |
-- == Example program
--
-- The following interactive session example enforces the same scalar
-- constraint as the nonlinear constraint example, but this time it
-- uses the augmented Lagrangian method to enforce the constraint and
-- the 'SBPLX' algorithm, which does not support nonlinear constraints
-- itself, to perform the minimization.  As before, the parameters
-- must always sum to 1, and the minimizer finds the same constrained
-- minimum of 22.5 at @(0.5, 0.5)@.
--
-- >>> import Numeric.LinearAlgebra ( dot, fromList, toList )
-- >>> let objf x = x `dot` x + 22
-- >>> let stop = ObjectiveRelativeTolerance 1e-9 :| []
-- >>> let algorithm = SBPLX objf [] Nothing
-- >>> let subproblem = LocalProblem 2 stop algorithm
-- >>> let x0 = fromList [5, 10]
-- >>> minimizeLocal subproblem x0
-- Right (Solution {solutionCost = 22.0, solutionParams = [0.0,0.0], solutionResult = FTOL_REACHED})
-- >>>          -- define constraint function:
-- >>> let constraintf x = sum (toList x) - 1.0
-- >>>          -- define constraint object to pass to the algorithm:
-- >>> let constraint = EqualityConstraint (Scalar constraintf) 1e-6
-- >>> let problem = AugLagProblem [constraint] [] (AUGLAG_EQ_LOCAL subproblem)
-- >>> minimizeAugLag problem x0
-- Right (Solution {solutionCost = 22.500000015505844, solutionParams = [0.5000880506776678,0.4999119493223323], solutionResult = FTOL_REACHED})

minimizeAugLag :: AugLagProblem -> Vector Double -> Either N.Result Solution
minimizeAugLag prob x0 =
  unsafePerformIO $ (Right <$> minimizeAugLag' prob x0) `Ex.catch` handler
  where
    handler :: NloptException -> IO (Either N.Result a)
    handler (NloptException retcode) = return $ Left retcode
