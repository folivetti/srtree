module Random where 

import System.Random 
import Control.Monad.State.Strict
import Control.Monad
import Data.SRTree 
import Data.SRTree.Eval
import Data.Massiv.Array as MA
import Data.Random.Normal

type Rng a = IO a

toss :: Rng Bool
toss = randomIO
{-# INLINE toss #-}

tossBiased :: Double -> Rng Bool
tossBiased p = do r <- randomIO
                  pure (r < p)

randomVal :: Rng Double
randomVal = randomIO

randomRange :: (Ord val, Random val) => (val, val) -> Rng val
randomRange rng = (randomRIO rng)
{-# INLINE randomRange #-}

randomFrom :: [a] -> Rng a
randomFrom funs = do n <- randomRange (0, length funs - 1)
                     pure $ funs !! n
{-# INLINE randomFrom #-}

randomVec :: Int -> Rng PVector
randomVec n = MA.fromList compMode <$> replicateM n (randomRange (-1, 1))
