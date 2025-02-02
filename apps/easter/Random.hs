module Random where 

import System.Random 
import Control.Monad.State.Strict
import Control.Monad
import Data.SRTree 
import Data.SRTree.Eval
import Data.Massiv.Array as MA

type Rng a = StateT StdGen IO a 

toss :: Rng Bool
toss = state random
{-# INLINE toss #-}

tossBiased :: Double -> Rng Bool
tossBiased p = do r <- state random 
                  pure (r < p)

randomVal :: Rng Double
randomVal = state random

randomRange :: (Ord val, Random val) => (val, val) -> Rng val
randomRange rng = state (randomR rng)
{-# INLINE randomRange #-}

randomFrom :: [a] -> Rng a
randomFrom funs = do n <- randomRange (0, length funs - 1)
                     pure $ funs !! n
{-# INLINE randomFrom #-}

randomVec :: Int -> Rng PVector
randomVec n = MA.fromList compMode <$> replicateM n (randomRange (-1, 1))

randomTree :: Int -> Int -> Int -> Rng (Fix SRTree) -> Rng (SRTree ()) -> Bool -> Rng (Fix SRTree)
randomTree minDepth maxDepth maxSize genTerm genNonTerm grow 
  | noSpaceLeft = genTerm
  | needNonTerm = genRecursion 
  | otherwise   = do r <- toss
                     if r 
                       then genTerm 
                       else genRecursion
  where 
    noSpaceLeft = maxDepth <= 1 || maxSize <= 2
    needNonTerm = (minDepth >= 0 || (maxDepth > 2 && not grow)) -- && maxSize > 2

    genRecursion = do 
        node <- genNonTerm
        case node of 
          Uni f _    -> Fix . Uni f <$> randomTree (minDepth - 1) (maxDepth - 1) (maxSize - 1) genTerm genNonTerm grow 
          Bin op _ _ -> do l <- randomTree (minDepth - 1) (maxDepth - 1) (if grow then maxSize - 2 else maxSize `div` 2) genTerm genNonTerm grow
                           r <- randomTree (minDepth - 1) (maxDepth - 1) (maxSize - 1 - countNodes l) genTerm genNonTerm grow 
                           pure . Fix  $ Bin op l r
{-# INLINE randomTree #-}
