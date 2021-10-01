module Print where

import Control.Monad.Reader

import Tree

data DisplayNodes ix val = D
  { _displayVar      :: ix -> String
  , _displayVal      :: val -> String
  , _displayFun      :: Function -> String
  , _displayPow      :: String
  , _displayFloatPow :: String
  }

asExpr :: (Show ix, Show val) => Tree ix val -> Reader (DisplayNodes ix val) String
asExpr Empty = pure ""
asExpr (Var ix) = do
  display <- asks _displayVar
  pure $ display ix
asExpr (Const val) = do
  display <- asks _displayVal
  pure $ display val 
asExpr (Fun f t) = do
  display <- asks _displayFun
  st      <- asExpr t
  pure $ mconcat [display f, "(", st, ")"]
asExpr (Pow t ix) = do
  st  <- asExpr t
  pow <- asks _displayPow
  pure $ mconcat ["(", st, ")", pow, "(", show ix, ")"]
asExpr (Add l r) = do
  sl <- asExpr l
  sr <- asExpr r
  pure $ mconcat ["(", sl, ") + (", sr, ")"]
asExpr (Sub l r) = do
  sl <- asExpr l
  sr <- asExpr r
  pure $ mconcat ["(", sl, ") - (", sr, ")"]
asExpr (Mul l r) = do
  sl <- asExpr l
  sr <- asExpr r
  pure $ mconcat ["(", sl, ") * (", sr, ")"]
asExpr (Div l r) = do
  sl <- asExpr l
  sr <- asExpr r
  pure $ mconcat ["(", sl, ") / (", sr, ")"]
asExpr (Power l r) = do
  sl  <- asExpr l
  sr  <- asExpr r
  pow <- asks _displayFloatPow
  pure $ mconcat ["(", sl, ")", pow, "(", sr, ")"]
asExpr (LogBase l r) = do
  sl  <- asExpr l
  sr  <- asExpr r
  pure $ mconcat ["log(", sl, ",", sr, ")"]

asTree :: (Show ix, Show val) => Tree ix val -> Reader (DisplayNodes ix val) String
asTree Empty = pure ""
asTree (Var ix) = do
  display <- asks _displayVar
  pure $ mconcat ["[", display ix, "]\n"]
asTree (Const val) = do
  display <- asks _displayVal
  pure $ mconcat ["[", display val, "]\n"]
asTree (Fun f t) = do
  display <- asks _displayFun
  st      <- asTree t
  pure $ mconcat ["[", display f, "\n", st, "]\n"]
asTree (Pow t ix) = do
  st  <- asTree t
  pow <- asks _displayPow
  pure $ mconcat ["[", pow, "\n", st, "[", show ix, "]\n]"] 
asTree (Add l r) = do
  sl <- asTree l
  sr <- asTree r
  pure $ mconcat ["[+\n", sl, sr, "]\n"]
asTree (Sub l r) = do
  sl <- asTree l
  sr <- asTree r
  pure $ mconcat ["[-\n", sl, sr, "]\n"]
asTree (Mul l r) = do
  sl <- asTree l
  sr <- asTree r
  pure $ mconcat ["[×\n", sl, sr, "]\n"]
asTree (Div l r) = do
  sl <- asTree l
  sr <- asTree r
  pure $ mconcat ["[÷\n", sl, sr, "]\n"]
asTree (Power l r) = do
  sl  <- asTree l
  sr  <- asTree r
  pow <- asks _displayFloatPow
  pure $ mconcat ["[", pow, "\n", sl, sr, "]\n"]
asTree (LogBase l r) = do
  sl  <- asTree l
  sr  <- asTree r
  pure $ mconcat ["[log\n", sl, sr, "]\n"]

showExpr, showTree :: (Show ix, Show val) => Tree ix val -> DisplayNodes ix val -> String
showExpr t = runReader (asExpr t)
showTree t = runReader (asTree t)

printExpr :: (Show ix, Show val) => Tree ix val -> DisplayNodes ix val -> IO ()
printExpr t = putStrLn . showExpr t

showDefault t = showExpr t d
  where
    d = D (\ix -> mconcat ["x", show ix])
          show
          show
          "^"
          "**"

showTikz :: (Show ix, Show val, RealFrac val) => Tree ix val -> String 
showTikz t = showTree t d
  where
    d = D (\ix -> mconcat ["$x_{", show ix, "}$"])
          (\val -> mconcat ["$", show $ (/100) $ fromIntegral $ round $ val*100, "$"])
          show
          "\\^{}"
          "**"

showPython t = showExpr t d
  where
    d = D (\ix -> mconcat ["x[:,", show ix, "]"])
          show
          pyFun
          "**"
          "**"
          
    pyFun Id     = ""
    pyFun Abs    = "np.abs"
    pyFun Sin    = "np.sin"
    pyFun Cos    = "np.cos"
    pyFun Tan    = "np.tan"
    pyFun Sinh   = "np.sinh"
    pyFun Cosh   = "np.cosh"
    pyFun Tanh   = "np.tanh"
    pyFun ASin   = "np.asin"
    pyFun ACos   = "np.acos"
    pyFun ATan   = "np.atan"
    pyFun ASinh  = "np.asinh"
    pyFun ACosh  = "np.acosh"
    pyFun ATanh  = "np.atanh"
    pyFun Sqrt   = "np.sqrt"
    pyFun Square = "np.square"
    pyFun Log    = "np.log"
    pyFun Exp    = "np.exp"

showSimpy = undefined
