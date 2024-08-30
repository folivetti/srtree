{-# language LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.ParseSR.IO
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
-- Functions to parse multiple expressions from stdin or a text file.
--
-----------------------------------------------------------------------------
module Text.ParseSR.IO ( withInput, withOutput, withOutputDebug )
    where

-- import Data.SRTree.EqSat1
import Algorithm.EqSat.Simplify ( simplifyEqSatDefault )
import Control.Monad (forM_, unless)
import qualified Data.ByteString.Char8 as B
import Data.SRTree
import Data.SRTree.Recursion (Fix (..))
import System.IO
import Text.ParseSR (Output, SRAlgs, parseSR, showOutput)

-- | given a filename, the symbolic regression algorithm,  a string of variables name, 
-- and two booleans indicating whether to convert float values to parameters and 
-- whether to simplify the expression or not, it will read the file and parse everything 
-- returning a list of either an error message or a tree.
--
-- empty filename defaults to stdin 
withInput :: String -> SRAlgs -> String -> Bool -> Bool -> IO [Either String (Fix SRTree)]
withInput fname sr hd param simpl = do
  h <- if null fname then pure stdin else openFile fname ReadMode
  contents <- hGetLines h 
  let myParserFun = parseSR sr (B.pack hd) param . B.pack
      -- myParser = if simpl then fmap simplifyEqSat . myParserFun else myParserFun
      myParser = if simpl then fmap simplifyEqSatDefault . myParserFun else myParserFun
      es = map myParser $ filter (not . null) contents
  unless (null fname) $ hClose h
  pure es

-- | outputs a list of either error or trees to a file using the Output format. 
--
-- empty filename defaults to stdout 
withOutput :: String -> Output -> [Either String (Fix SRTree)] -> IO ()
withOutput fname output exprs = do
  h <- if null fname then pure stdout else openFile fname WriteMode
  forM_ exprs $ \case 
                   Left  err -> hPutStrLn h $ "invalid expression: " <> err
                   Right ex  -> hPutStrLn h (showOutput output ex)
  unless (null fname) $ hClose h

-- | debug version of output function to check the invalid parsers
withOutputDebug :: String -> Output -> [Either String (Fix SRTree, Fix SRTree)] -> IO ()
withOutputDebug fname output exprs = do
  h <- if null fname then pure stdout else openFile fname WriteMode
  forM_ exprs $ \case 
                   Left  err      -> hPutStrLn h $ "invalid expression: " <> err
                   Right (t1, t2) -> do 
                                       hPutStrLn h ("First: " <> showOutput output t1)
                                       hPutStrLn h ("Second: " <> showOutput output t2)
                                       hFlush h
  unless (null fname) $ hClose h

hGetLines :: Handle -> IO [String]
hGetLines h = do
  done <- hIsEOF h
  if done
    then return []
    else do
      line <- hGetLine h
      (line :) <$> hGetLines h
