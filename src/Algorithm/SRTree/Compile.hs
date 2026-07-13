{-# LANGUAGE GADTs #-}

module Algorithm.SRTree.Compile where

import Data.SRTree
import Data.SRTree.Eval (compileLoss, Target, Columns, Theta)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Storable as VS
import Algorithm.SRTree.AD
import Algorithm.SRTree.Utils

data EvalTree = EvalTree {
  ctLoss :: Theta -> Double,
  ctAD   :: VS.Vector Double -> (Double, VS.Vector Double),
  ctTree :: Fix SRTree,
  ctRows :: Int
}

-- | Compile a tree and store it in a CompiledTree data structure
compileTree :: Columns -> Target -> Maybe Target -> Fix SRTree -> EvalTree
compileTree xss ys mYerr tree = EvalTree {
  ctLoss = compileLoss xss tree ys,
  ctAD   = compileFunAndGrad MultiThread xss ys mYerr tree,
  ctTree = tree,
  ctRows = U.length ys
}

data EvaluatedTree = EvaluatedTree {
  valLoss             :: Double,
  valTheta            :: Theta,
  valRows             :: Double,
  valParams           :: Double,
  valTree             :: Fix SRTree,
  valLogParams        :: Double,
  valLogParamsLattice :: Double
}

evaluateTree :: EvalTree -> Target -> [[Double]] -> Theta -> EvaluatedTree
evaluateTree et fisher hessian theta = EvaluatedTree {
  valLoss             = ctLoss et theta,
  valTheta            = theta,
  valRows             = fromIntegral (ctRows et),
  valParams           = fromIntegral (U.length theta),
  valTree             = ctTree et,
  valLogParams        = logParameters fisher theta,
  valLogParamsLattice = logParametersLatt hessian fisher theta
}


-- log of the parameters complexity
logParameters :: U.Vector Double -> Target -> Double
logParameters fisher theta = -(p / 2) * log 3 + 0.5 * logFisher + logTheta
  where
    (logTheta, logFisher, p) = foldr addIfSignificant (0, 0, 0) $ zip (U.toList theta) (U.toList fisher)

-- same as above but for the Lattice
logParametersLatt :: [[Double]] -> U.Vector Double -> Target -> Double
logParametersLatt hessian fisher theta = 0.5 * p * (1 - log 3) + 0.5 * log detFisher
  where
    detFisher = det $ map U.fromList hessian

    (logTheta, logFisher, p) = foldr addIfSignificant (0, 0, 0) $ zip (U.toList theta) (U.toList fisher)

addIfSignificant (v, f) (acc_v, acc_f, acc_p)
  | isSignificant v f = (acc_v + log (abs v), acc_f + log f, acc_p + 1)
  | otherwise = (acc_v, acc_f, acc_p)
{-# INLINE addIfSignificant #-}

isSignificant v f = abs (v / sqrt(12 / f) ) >= 1
{-# INLINE isSignificant #-}
