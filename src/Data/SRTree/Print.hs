-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Print 
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2021
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
         , printExpr
         , showTikz
         , printTikz
         , showPython
         , printPython
         , showLatex
         , printLatex
         )
         where

import Control.Monad.Reader ( asks, runReader, Reader )
import Data.Char ( toLower )

import Data.SRTree.Internal
import Data.SRTree.Recursion

showExpr :: Fix SRTree -> String
showExpr = cata alg
  where
    alg (Var ix)     = 'x' : show ix
    alg (Param ix)   = 't' : show ix
    alg (Const c)    = show c
    alg (Bin op l r) = concat ["(", l, " ", showOp op, " ", r, ")"]
    alg (Uni f t)    = concat [show f, "(", t, ")"]

printExpr :: Fix SRTree -> IO ()
printExpr = putStrLn . showExpr 

showOp Add   = "+"
showOp Sub   = "-"
showOp Mul   = "*"
showOp Div   = "/"
showOp Power = "^"
{-# INLINE showOp #-}

-- | Displays a tree as a numpy compatible expression.
showPython :: Fix SRTree -> String
showPython = cata alg
  where
    alg (Var ix)     = concat ["x[:, ", show ix, "]"]
    alg (Param ix)   = concat ["t[:, ", show ix, "]"]
    alg (Const c)    = show c
    alg (Bin Power l r) = concat [l, " ** ", r]
    alg (Bin op l r) = concat ["(", l, " ", showOp op, " ", r, ")"]
    alg (Uni f t)    = concat [pyFun f, "(", t, ")"]
          
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

printPython :: Fix SRTree -> IO ()
printPython = putStrLn . showPython

-- | Displays a tree as a sympy compatible expression.
showLatex :: Fix SRTree -> String
showLatex = cata alg
  where
    alg (Var ix)     = concat ["x_{, ", show ix, "}"]
    alg (Param ix)   = concat ["\\theta_{, ", show ix, "}"]
    alg (Const c)    = show c
    alg (Bin Power l r) = concat [l, "^{", r, "}"]
    alg (Bin op l r) = concat ["\\left(", l, " ", showOp op, " ", r, "\\right)"]
    alg (Uni Abs t)  = concat ["\\left |", t, "\\right |"]
    alg (Uni f t)    = concat [showLatexFun f, "(", t, ")"]

showLatexFun :: Function -> String
showLatexFun f = mconcat ["\\operatorname{", map toLower $ show f, "}"]
{-# INLINE showLatexFun #-}

printLatex :: Fix SRTree -> IO ()
printLatex = putStrLn . showLatex

-- | Displays a tree in Tikz format
showTikz :: Fix SRTree -> String
showTikz = cata alg
  where
    roundN n x = let ten = 10^n in (/ ten) . fromIntegral . round $ x*ten
    alg (Var ix)     = concat ["[$x_{, ", show ix, "}$]\n"]
    alg (Param ix)   = concat ["[$\\theta_{, ", show ix, "}$]\n"]
    alg (Const c)    = concat ["[$", show (roundN 2 c), "$]\n"]
    alg (Bin op l r) = concat ["[", showOpTikz op, l, r, "]\n"]
    alg (Uni f t)    = concat ["[", map toLower $ show f, t, "]\n"]

    showOpTikz Add = "+\n"
    showOpTikz Sub = "-\n"
    showOpTikz Mul = "×\n"
    showOpTikz Div = "÷\n"
    showOpTikz Power = "\\^{}\n"

printTikz = putStrLn . showTikz
