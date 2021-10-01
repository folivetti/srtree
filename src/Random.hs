module Random where

import System.Random 
import Control.Monad.State 
import Control.Monad.Reader 
import Data.Maybe (fromJust)

import Tree

data TIR ix val = TIR { _funY :: Function
                      , _p :: Sigma ix val
                      , _q :: Sigma ix val 
                      }
type Sigma ix val = [Pi ix val]
type Pi ix val    = (val, Function, [Tree ix val])

assembleTree :: (Eq ix, Eq val, Floating val) => TIR ix val -> Tree ix val
assembleTree (TIR f p q) = Fun f (assemble p / (1 + assemble q))
  where
    -- assemble :: Sigma ix val -> Tree ix val
    assemble [p']    = mk p'
    assemble (p':ps) = mk p' + assemble ps

    -- mk :: Pi ix val -> Tree ix val
    mk (v, g, ts) = Const v * Fun g (product ts)

class HasVars p where
  _vars :: p ix val -> [ix]
class HasVals p where
  _range :: p ix val -> (val, val)
class HasExps p where
  _exponents :: p ix val -> (Int, Int)
class HasFuns p where
  _funs :: p ix val -> [Function]

class (HasVars p, HasVals p, HasExps p, HasFuns p) => HasEverything p

type RndTree p ix val = ReaderT (p ix val) (StateT StdGen IO) (Tree ix val)

data FullParams ix val = P [ix] (val, val) (Int, Int) [Function]

instance HasVars FullParams where
  _vars (P ixs _ _ _) = ixs
instance HasVals FullParams where
  _range (P _ r _ _) = r
instance HasExps FullParams where
  _exponents (P _ _ e _) = e
instance HasFuns FullParams where
  _funs (P _ _ _ fs) = fs
instance HasEverything FullParams

toss :: StateT StdGen IO Bool
toss = state random

randomFrom :: [a] -> StateT StdGen IO a
randomFrom funs = do n <- randomRange (0, length funs - 1)
                     pure $ funs !! n

randomRange :: (Ord val, Random val) => (val, val) -> StateT StdGen IO val
randomRange rng = state (randomR rng)

randomVar :: HasVars p => RndTree p ix val
randomVar = do vars <- asks _vars
               lift $ Var <$> randomFrom vars

randomConst :: (Ord val, Random val, HasVals p) => RndTree p ix val
randomConst = do rng <- asks _range
                 lift $ Const <$> randomRange rng

randomPow :: (Ord val, Random val, HasExps p) => RndTree p ix val
randomPow = do rng <- asks _exponents
               lift $ Pow Empty <$> randomRange rng

randomFunction :: HasFuns p => RndTree p ix val
randomFunction = do funs <- asks _funs
                    lift $ (`Fun` Empty) <$> randomFrom funs

randomNode :: (Ord val, Random val, HasEverything p) => RndTree p ix val
randomNode = do
  choice <- lift $ randomRange (0, 9 :: Int)
  case choice of
    0 -> randomVar
    1 -> randomConst
    2 -> randomFunction
    3 -> randomPow
    4 -> pure $ Add Empty Empty
    5 -> pure $ Sub Empty Empty
    6 -> pure $ Mul Empty Empty
    7 -> pure $ Div Empty Empty
    8 -> pure $ Power Empty Empty
    9 -> pure $ LogBase Empty Empty

randomTree :: (Ord val, Random val, HasEverything p) => Int -> RndTree p ix val
randomTree 0      = do
  coin <- lift toss
  if coin
    then randomVar
    else randomConst
randomTree budget = do 
  node  <- randomNode
  fromJust <$> case arity node of
    0 -> pure $ Just node
    1 -> replaceChild node <$> randomTree (budget - 1)
    2 -> replaceChildren node <$> randomTree (budget `div` 2) <*> randomTree (budget `div` 2)
