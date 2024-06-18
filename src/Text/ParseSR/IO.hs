{-# language LambdaCase #-}
module Text.ParseSR.IO ( withInput, withOutput, withOutputDebug )
    where

import Control.Monad ( unless, forM_ )
import System.IO
import qualified Data.ByteString.Char8 as B
import Data.SRTree
import Data.SRTree.Recursion (Fix(..))
import Data.SRTree.EqSat
import Text.ParseSR ( SRAlgs, Output, parseSR, showOutput )

withInput :: String -> SRAlgs -> String -> Bool -> Bool -> IO [Either String (Fix SRTree)]
withInput fname sr hd param simpl = do
  h <- if null fname then pure stdin else openFile fname ReadMode
  contents <- hGetLines h 
  let myParserFun = parseSR sr (B.pack hd) param . B.pack
      myParser = if simpl then fmap simplifyEqSat . myParserFun else myParserFun
      es = map myParser $ filter (not . null) contents
  unless (null fname) $ hClose h
  pure es

withOutput :: String -> Output -> [Either String (Fix SRTree)] -> IO ()
withOutput fname output exprs = do
  h <- if null fname then pure stdout else openFile fname WriteMode
  forM_ exprs $ \case 
                   Left  err -> hPutStrLn h $ "invalid expression: " <> err
                   Right ex  -> hPutStrLn h (showOutput output ex)
  unless (null fname) $ hClose h

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
