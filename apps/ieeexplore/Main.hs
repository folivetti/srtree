{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}
{-# LANGUAGE  MultiWayIf #-}
{-# LANGUAGE  OverloadedStrings #-}

module Main where 

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Simplify
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.Opt
import Control.Lens (element, makeLenses, over, (&), (+~), (-~), (.~), (^.))
import Control.Monad (foldM, forM_, forM, when, unless, filterM, (>=>), replicateM, replicateM_)
import Control.Monad.State
import qualified Data.IntMap as IM
import Data.Massiv.Array as MA hiding (forM_, forM)
import Data.Maybe (fromJust, isNothing, isJust)
import Data.SRTree
import Data.SRTree.Datasets
import Data.SRTree.Eval
import Data.SRTree.Random (randomTree)
import Data.SRTree.Print
import Options.Applicative as Opt hiding (Const)
import System.Random
import qualified Data.Set as Set
import Data.List ( sort )

import Debug.Trace
import Algorithm.EqSat (runEqSat)


type RangedTree a = a 

data QueryDB = QDB { _mseDB :: RangedTree Double 
                   , _maeDB :: RangedTree Double 
                   , _r2DB  :: RangedTree Double 
                   , _mdlDB :: RangedTree Double 
                   , _bicDB :: RangedTree Double 
                   , _aicDB :: RangedTree Double 
                   , _lenDB :: RangedTree Int
                   , _ptDB  :: RangedTree Int -- DB 
                   } 

data ExtraInfo = ExtraInfo { _thetaMap :: IM.IntMap PVector
                           , _qdb      :: QueryDB
                           }

type InfoEGraph a = EGraphST (StateT ExtraInfo IO) a

--io = lift . lift
--{-# INLINE io #-}
--ext = lift
--{-# INLINE ext #-}

myCost :: SRTree Int -> Int
myCost (Var _)      = 1
myCost (Const _)    = 1
myCost (Param _)    = 1
myCost (Bin op l r) = 2 + l + r
myCost (Uni _ t)    = 3 + t



data Args = Args
  { dataset :: String,
    gens    :: Int,
    _maxSize :: Int
  }
  deriving (Show)

-- parser of command line arguments
opt :: Parser Args
opt = Args
   <$> strOption
       ( long "dataset"
       <> short 'd'
       <> metavar "INPUT-FILE"
       <> help "CSV dataset." )
   <*> option auto
      ( long "generations"
      <> short 'g'
      <> metavar "GENS"
      <> showDefault
      <> value 100
      <> help "Number of generations." )
  <*> option auto
       ( long "maxSize"
       <> short 's'
       <> help "max-size." )

main :: IO ()
main = do
  --args <- pure (Args "nikuradse_2.csv" 100) -- execParser opts
  args <- execParser opts
  ((x, y, _, _), _, _) <- loadDataset (dataset args) True
  print "opa"

  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Very simple example of GP using SRTree."
           <> header "tinyGP - a very simple example of GP using SRTRee." )
