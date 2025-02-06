{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Print 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  
--
-- Conversion functions to display the expression trees in different formats.
--
-----------------------------------------------------------------------------
module Data.SRTree.Print 
         ( showExpr
         , showExprWithVars
         , printExpr
         , printExprWithVars
         , showTikz
         , printTikz
         , showPython
         , printPython
         , showLatex
         , printLatex
         , showOp
         )
         where

import Control.Monad.Reader (Reader, asks, runReader)
import Data.Char (toLower)
import Data.SRTree.Internal
import Data.SRTree.Recursion (cata)

-- | converts a tree with protected operators to
-- a conventional math tree
removeProtection :: Fix SRTree -> Fix SRTree
removeProtection = cata $
  \case
     Var ix -> Fix (Var ix)
     Param ix -> Fix (Param ix)
     Const x -> Fix (Const x)
     Uni SqrtAbs t -> sqrt (abs t)
     Uni LogAbs t -> log (abs t)
     Uni Cube t -> t ** 3
     Uni f t -> Fix (Uni f t)
     Bin AQ l r -> l / sqrt (1 + r*r)
     Bin PowerAbs l r -> abs l ** r
     Bin op l r -> Fix (Bin op l r)

-- | convert a tree into a string in math notation 
--
-- >>> showExpr $ "x0" + sin ( tanh ("t0" + 2) )
-- "(x0 + Sin(Tanh((t0 + 2.0))))"
showExpr :: Fix SRTree -> String
showExpr = cata alg . removeProtection
  where alg = \case
                Var ix     -> 'x' : show ix
                Param ix   -> 't' : show ix
                Const c    -> show c
                Bin op l r -> concat ["(", l, " ", showOp op, " ", r, ")"]
                Uni f t    -> concat [show f, "(", t, ")"]

-- | convert a tree into a string in math notation
-- given named vars.
--
-- >>> showExprWithVar ["mu", "eps"] $ "x0" + sin ( "x1" * tanh ("t0" + 2) )
-- "(mu + Sin(Tanh(eps * (t0 + 2.0))))"
showExprWithVars :: [String] -> Fix SRTree -> String
showExprWithVars varnames = cata alg . removeProtection
  where alg = \case
                Var ix     -> varnames !! ix
                Param ix   -> 't' : show ix
                Const c    -> show c
                Bin op l r -> concat ["(", l, " ", showOp op, " ", r, ")"]
                Uni f t    -> concat [show f, "(", t, ")"]

-- | prints the expression 
printExpr :: Fix SRTree -> IO ()
printExpr = putStrLn . showExpr 

-- | prints the expression
printExprWithVars :: [String] -> Fix SRTree -> IO ()
printExprWithVars varnames = putStrLn . showExprWithVars varnames

-- how to display an operator 
showOp :: Op -> String
showOp Add   = "+"
showOp Sub   = "-"
showOp Mul   = "*"
showOp Div   = "/"
showOp Power = "^"
showOp AQ    = "aq"
showOp PowerAbs = "|^|"
{-# INLINE showOp #-}

-- | Displays a tree as a numpy compatible expression.
--
-- >>> showPython $ "x0" + sin ( tanh ("t0" + 2) )
-- "(x[:, 0] + np.sin(np.tanh((t[:, 0] + 2.0))))"
showPython :: Fix SRTree -> String
showPython = cata alg . removeProtection
  where
    alg = \case
      Var ix        -> concat ["x[:, ", show ix, "]"]
      Param ix      -> concat ["t[", show ix, "]"]
      Const c       -> show c
      Bin Power l r -> concat [l, " ** ", r]
      Bin op l r    -> concat ["(", l, " ", showOp op, " ", r, ")"]
      Uni f t       -> concat [pyFun f, "(", t, ")"]
          

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
    pyFun Cbrt   = "np.cbrt"
    pyFun Recip  = "np.reciprocal"

-- | print the expression in numpy notation
printPython :: Fix SRTree -> IO ()
printPython = putStrLn . showPython

-- | Displays a tree as a LaTeX compatible expression.
--
-- >>> showLatex $ "x0" + sin ( tanh ("t0" + 2) )
-- "\\left(x_{, 0} + \\operatorname{sin}(\\operatorname{tanh}(\\left(\\theta_{, 0} + 2.0\\right)))\\right)"
showLatex :: Fix SRTree -> String
showLatex = cata alg . removeProtection
  where
    alg = \case
      Var ix        -> concat ["x_{, ", show ix, "}"]
      Param ix      -> concat ["\\theta_{, ", show ix, "}"]
      Const c       -> show c
      Bin Power l r -> concat [l, "^{", r, "}"]
      Bin op l r    -> concat ["\\left(", l, " ", showOp op, " ", r, "\\right)"]
      Uni Abs t     -> concat ["\\left |", t, "\\right |"]
      Uni f t       -> concat [showLatexFun f, "(", t, ")"]

showLatexFun :: Function -> String
showLatexFun f = mconcat ["\\operatorname{", map toLower $ show f, "}"]
{-# INLINE showLatexFun #-}

-- | prints expression in LaTeX notation. 
printLatex :: Fix SRTree -> IO ()
printLatex = putStrLn . showLatex

-- | Displays a tree in Tikz format
showTikz :: Fix SRTree -> String
showTikz = cata alg . removeProtection
  where
    alg = \case
      Var ix     -> concat ["[$x_{, ", show ix, "}$]\n"]
      Param ix   -> concat ["[$\\theta_{, ", show ix, "}$]\n"]
      Const c    -> concat ["[$", show (roundN 2 c), "$]\n"]
      Bin op l r -> concat ["[", showOpTikz op, l, r, "]\n"]
      Uni f t    -> concat ["[", map toLower $ show f, t, "]\n"]

    roundN n x = let ten = 10^n in (/ ten) . fromIntegral . round $ x*ten

    showOpTikz Add = "+\n"
    showOpTikz Sub = "-\n"
    showOpTikz Mul = "×\n"
    showOpTikz Div = "÷\n"
    showOpTikz Power = "\\^{}\n"

-- | prints the tree in TikZ format 
printTikz :: Fix SRTree -> IO ()
printTikz = putStrLn . showTikz
