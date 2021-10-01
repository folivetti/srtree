{-# language ScopedTypeVariables #-}
module Eval where

import Tree

import Numeric.Interval
import Data.Map.Strict (Map(..), (!), (!?), insert, fromList)
import qualified Data.Map.Strict as M
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative hiding (Const)

evalTree :: (Floating val, OptIntPow val) => Tree ix val -> Reader (ix -> Maybe val) (Maybe val)
evalTree Empty         = pure Nothing
evalTree (Const c)     = pure $ Just c
evalTree (Var ix)      = askAbout ix
evalTree (Fun f t)     = evalFun f <$$> evalTree t
evalTree (Pow t k)     = (^. k) <$$> evalTree t
evalTree (Add l r)     = (+)  <$*> evalTree l <*> evalTree r
evalTree (Sub l r)     = (-)  <$*> evalTree l <*> evalTree r
evalTree (Mul l r)     = (*)  <$*> evalTree l <*> evalTree r
evalTree (Div l r)     = (/)  <$*> evalTree l <*> evalTree r
evalTree (Power l r)   = (**) <$*> evalTree l <*> evalTree r
evalTree (LogBase l r) = logBase <$*> evalTree l <*> evalTree r

evalTreeMap :: (Floating v1, OptIntPow v1, Floating v2, OptIntPow v2) => (v1 -> v2) -> Tree ix v1 -> Reader (ix -> Maybe v2) (Maybe v2)
evalTreeMap f Empty         = pure Nothing
evalTreeMap f (Const c)     = pure $ Just $ f c
evalTreeMap f (Var ix)      = askAbout ix
evalTreeMap f (Fun g t)     = evalFun g <$$> evalTreeMap f t
evalTreeMap f (Pow t k)     = (^. k) <$$> evalTreeMap f t
evalTreeMap f (Add l r)     = (+)  <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (Sub l r)     = (-)  <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (Mul l r)     = (*)  <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (Div l r)     = (/)  <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (Power l r)   = (**) <$*> evalTreeMap f l <*> evalTreeMap f r
evalTreeMap f (LogBase l r) = logBase <$*> evalTreeMap f l <*> evalTreeMap f r

-- | lift functions inside nested applicatives.
(<$$>) :: (Applicative f, Applicative g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) = fmap . fmap
(<$*>) :: (Applicative f, Applicative g) => (a -> b -> c) -> f (g a) -> f (g b -> g c)
op <$*> m = liftA2 op <$> m

askAbout :: x -> Reader (x -> a) a
askAbout x = asks ($ x)

-- | Example of using `evalTree` with a Map.
evalTreeWithMap :: (Ord ix, Floating val, OptIntPow val) => Tree ix val -> Map ix val -> Maybe val
evalTreeWithMap t m = runReader (evalTree t) (m !?)

-- | Relabel occurences of a var into a tuple (ix, Int).
relabelOccurrences :: forall ix val . Ord ix => Tree ix val -> Tree (ix, Int) val
relabelOccurrences t = traverseIx updVar t `evalState` M.empty 
  where
    updVar :: ix -> State (Map ix Int) (ix, Int)
    updVar ix = do
      s <- get
      case s !? ix of
        Nothing -> do put $ insert ix 0 s
                      pure (ix, 0)
        Just c  -> do put $ insert ix (c+1) s
                      pure (ix, c+1)
