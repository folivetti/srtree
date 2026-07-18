{-# LANGUAGE GADTs #-}

module Algorithm.SRTree.Compile where

import Data.SRTree
import Data.SRTree.Eval (compileLoss, Target, Columns, Theta)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Generic as G
import Algorithm.SRTree.AD
import Algorithm.SRTree.Utils
import Algorithm.SRTree.Likelihoods (Distribution(..), Loss(..), buildLoss, hessianNLL)
import Algorithm.SRTree.NonlinearOpt (minimizeNLL, minimizeNLLWithFixedParam)
import Data.SRTree.Recursion (cata)

data EvalTree = EvalTree {
  ctDist            :: Distribution,
  ctLoss            :: Theta -> Double,
  ctAD              :: VS.Vector Double -> (Double, VS.Vector Double),
  ctOptimizer       :: Target -> Target,
  ctOptimizerFixed  :: Int -> Target -> Target,
  ctNLL             :: Target -> Double,
  ctGradNLL         :: Target -> (Double, Target),
  ctHessianNLL      :: Target -> Columns,
  ctTree            :: Fix SRTree,
  ctRows            :: Int,
  ctVar             :: Double
}

-- | Compile a tree and store it in a CompiledTree data structure
compileTree :: Distribution -> Columns -> Target -> Maybe Target -> Fix SRTree -> EvalTree
compileTree dist xss ys mYerr tree = EvalTree {
  ctDist            = dist,
  ctLoss            = compileLoss xss tree ys mYerr,
  ctAD              = compileFunAndGrad MultiThread xss ys mYerr tree,
  ctOptimizer       = fst3 . minimizeNLL MultiThread (NLL dist) mYerr 100 xss ys tree,
  ctOptimizerFixed  = minimizeNLLWithFixedParam MultiThread (NLL dist) mYerr 100 xss ys tree,
  ctNLL             = compileLoss xss lossTree ys mYerr,
  ctGradNLL         = \theta -> let fg = compileFunAndGrad MultiThread xss ys mYerr lossTree
                                    (obj, gradStorable) = fg (G.convert theta)
                                in (obj, G.convert gradStorable),
  ctHessianNLL      = hessianNLL dist mYerr xss ys tree,
  ctTree            = tree,
  ctRows            = n,
  ctVar             = let ym = U.sum ys / fromIntegral n
                      in U.foldr (\yi acc -> acc + (yi - ym)^2) 0 ys
}
  where
    n = U.length ys
    lossTree = buildLoss (NLL dist) (fromIntegral n) tree
    fst3 (a, _, _) = a

data EvaluatedTree = EvaluatedTree {
  valLoss             :: Double,
  valTheta            :: Theta,
  valRows             :: Double,
  valParams           :: Double,
  valTree             :: Fix SRTree,
  valLogParams        :: Double,
  valLogParamsLattice :: Double,
  valVar              :: Double
}

evaluateTree :: EvalTree -> Target -> [[Double]] -> Theta -> EvaluatedTree
evaluateTree et fisher hessian theta = EvaluatedTree {
  valLoss             = ctLoss et theta,
  valTheta            = theta,
  valRows             = fromIntegral (ctRows et),
  valParams           = fromIntegral (U.length theta),
  valTree             = ctTree et,
  valLogParams        = logParameters fisher theta,
  valLogParamsLattice = logParametersLatt hessian fisher theta,
  valVar              = ctVar et
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

fixParam :: Int -> Double -> Fix SRTree -> Fix SRTree
fixParam ix val = cata alg
  where
    alg (Param i) | i == ix   = Fix $ Const val
                  | i > ix    = Fix $ Param (i-1)
                  | otherwise = Fix $ Param i
    alg other = Fix other
{-# INLINE fixParam #-}
