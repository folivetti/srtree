{-# language ImportQualifiedPost #-}
{-# language ViewPatterns #-}
{-# language OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SRTree.Datasets
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  FlexibleInstances, DeriveFunctor, ScopedTypeVariables, ConstraintKinds
--
-- Utility library to handle regression datasets
-- this module exports only the `loadDataset` function.
--
-----------------------------------------------------------------------------
module Data.SRTree.Datasets ( loadDataset, loadTrainingOnly, getX, splitData, DataSet(..) )
    where

import Codec.Compression.GZip (decompress)
import Data.ByteString.Char8 qualified as B
import Data.ByteString.Lazy qualified as BS
import Data.List (delete, find, intercalate)
import Data.Massiv.Array
  ( Array,
    Comp (Seq, Par),
    Ix2 ((:.)),
    S (..),
    Sz (Sz1),
    (<!),
  )
import Data.Massiv.Array qualified as M
import Data.Maybe (fromJust)
import Data.SRTree.Eval (PVector, SRMatrix, compMode)
import Data.Vector qualified as V
import System.FilePath (takeExtension)
import Text.Read (readMaybe)
import Data.Massiv.Array as MA hiding (forM_, forM, map, take, tail, zip, replicate, all, read)
import Control.Monad.State.Strict
import System.Random
import List.Shuffle ( shuffle )


-- a dataset is a triple (X, y, y_error)
type DataSet = (SRMatrix, PVector, Maybe PVector)

-- | Loads a list of list of bytestrings to a matrix of double
loadMtx :: [[B.ByteString]] -> Array S Ix2 Double
loadMtx = M.fromLists' compMode . map (map (read . B.unpack))
{-# INLINE loadMtx #-}

-- | Returns true if the extension is .gz
isGZip :: FilePath -> Bool
isGZip = (== ".gz") . takeExtension
{-# INLINE isGZip #-}

-- | Detects the separator automatically by 
--   checking whether the use of each separator generates
--   the same amount of SRMatrix in every row and at least two SRMatrix.
--
--  >>> detectSep ["x1,x2,x3,x4"] 
-- ','
detectSep :: [B.ByteString] -> Char
detectSep xss = go seps
  where
    seps = [' ','\t','|',':',';',',']
    xss' = map B.strip xss

    -- consistency check whether all rows have the same
    -- number of columns when spliting by this sep 
    allSameLen []     = True
    allSameLen (y:ys) = y /= 1 && all (==y) ys

    go []     = error $ "CSV parsing error: unsupported separator. Supporter separators are "
                      <> intercalate "," (map show seps)
    go (c:cs) = if allSameLen $ map (length . B.split c) xss'
                   then c
                   else go cs
{-# INLINE detectSep #-}

-- | reads a file and returns a list of list of `ByteString`
-- corresponding to each element of the matrix.
-- The first row can be a header. 
readFileToLines :: FilePath -> IO [[B.ByteString]]
readFileToLines filename = do
  content <- removeBEmpty . toLines . toChar8 . unzip <$> BS.readFile filename
  let sep = getSep content
  pure . removeEmpty . map (B.split sep) $ content
  where
      getSep       = detectSep . take 100 -- use only first 100 rows to detect separator
      removeBEmpty = filter (not . B.null)
      removeEmpty  = filter (not . null)
      toLines      = B.split '\n'
      unzip        = if isGZip filename then decompress else id
      toChar8      = B.pack . map (toEnum . fromEnum) . BS.unpack
{-# INLINE readFileToLines #-}

-- | Splits the parameters from the filename
-- the expected format of the filename is *filename.ext:p1:p2:p3:p4*
-- where p1 and p2 is the starting and end rows for the training data,
-- by default p1 = 0 and p2 = number of rows - 1
-- p3 is the target PVector, it can be a string corresponding to the header
-- or an index.
-- p4 is a comma separated list of SRMatrix (either index or name) to be used as 
-- input variables. These will be renamed internally as x0, x1, ... in the order
-- of this list.
splitFileNameParams :: FilePath -> (FilePath, [B.ByteString])
splitFileNameParams (B.pack -> filename) = (B.unpack fname, take 6 params)
  where
    (fname : params') = B.split ':' filename
    -- fill up the empty parameters with an empty string
    params            = params' <> replicate (6 - min 6 (length params')) B.empty
{-# inline splitFileNameParams #-}

-- | Tries to parse a string into an int
parseVal :: String -> Either String Int
parseVal xs = case readMaybe xs of
                Nothing -> Left xs
                Just x  -> Right x
{-# inline parseVal #-}

-- | Given a map between PVector name and indeces,
-- the target PVector and the variables SRMatrix,
-- returns the indices of the variables SRMatrix and the target
getColumns :: [(B.ByteString, Int)] -> B.ByteString -> B.ByteString -> B.ByteString -> ([Int], Int, Int)
getColumns headerMap target columns target_error = (ixs, iy, iy_error)
  where
      n_cols  = length headerMap
      getIx c = case parseVal c of
                  -- if the PVector is a name, retrive the index
                  Left name -> case find ((== B.pack name) . fst) headerMap of
                                 Nothing -> error $ "PVector name " <> name <> " does not exist."
                                 Just v  -> snd v
                  -- if it is an int, check if it is within range
                  Right v   -> if v >= 0 && v < n_cols
                                 then v
                                 else error $ "PVector index " <> show v <> " out of range."
      -- if the input variables SRMatrix are ommitted, use
      -- every PVector except for iy
      ixs = if B.null columns
               then delete iy [0 .. n_cols - 1]
               else map (getIx . B.unpack) $ B.split ',' columns
      -- if the target PVector is ommitted, use the last one
      iy = if B.null target
              then n_cols - 1
              else getIx $ B.unpack target
      -- if the target PVector is ommitted, use the last one
      iy_error = if B.null target_error
                  then (-1)
                  else getIx $ B.unpack target_error
{-# inline getColumns #-}

-- | Given the start and end rows, it returns the 
-- hmatrix extractors for the training and validation data
getRows :: B.ByteString -> B.ByteString -> Int -> (Int, Int)
getRows (B.unpack -> start) (B.unpack -> end) nRows
  | st_ix >= end_ix                 = error $ "Invalid range: " <> show start <> ":" <> show end <> "."
  | st_ix == 0 && end_ix == nRows-1 = (0, nRows - 1)
  | otherwise                       = (st_ix, end_ix)
  where
      st_ix = if null start
                then 0
                else case readMaybe start of
                       Nothing -> error $ "Invalid starting row " <> start <> "."
                       Just x  -> if x < 0 || x >= nRows
                                    then error $ "Invalid starting row " <> show x <> "."
                                    else x
      end_ix = if null end
                then nRows - 1
                else case readMaybe end of
                       Nothing -> error $ "Invalid end row " <> end <> "."
                       Just x  -> if x < 0 || x >= nRows
                                    then error $ "Invalid end row " <> show x <> "."
                                    else x
{-# inline getRows #-}

-- | `loadDataset` loads a dataset with a filename in the format:
--   filename.ext:start_row:end_row:target:features:y_err
--   it returns the X_train, y_train, X_test, y_test, varnames, target name 
--   where varnames are a comma separated list of the name of the vars 
--   and target name is the name of the target
--
-- where
--
-- **start_row:end_row** is the range of the training rows (default 0:nrows-1).
--   every other row not included in this range will be used as validation
-- **target** is either the name of the PVector (if the datafile has headers) or the index
-- of the target variable
-- **features** is a comma separated list of SRMatrix names or indices to be used as
-- input variables of the regression model.
loadDataset :: FilePath -> Bool -> IO ((SRMatrix, PVector, SRMatrix, PVector), (Maybe PVector, Maybe PVector), String, String)
loadDataset filename hasHeader = do  
  csv <- readFileToLines fname
  pure $ processData csv params hasHeader
  where
    (fname, params) = splitFileNameParams filename

-- support function that does everything for loadDataset
processData :: [[B.ByteString]] -> [B.ByteString] -> Bool -> ((SRMatrix, PVector, SRMatrix, PVector), (Maybe PVector, Maybe PVector), String, String)
processData csv params hasHeader = ((x_train, y_train, x_val, y_val) , (y_err_train, y_err_val), varnames, targetname)
  where
    ncols             = length $ head csv
    nrows             = length csv - fromEnum hasHeader
    (header, content) = if hasHeader
                           then (zip (map B.strip $ head csv) [0..], tail csv)
                           else (map (\i -> (B.pack ('x' : show i), i)) [0 .. ncols-1], csv)
    varnames          = intercalate "," [B.unpack v | c <- ixs
                                        , let v = fst . fromJust $ find ((==c).snd) header
                                        ]
    targetname        = if hasHeader then (B.unpack . fst . fromJust . find ((==iy).snd) $ header) else "y"
    -- get rows and SRMatrix indices
    (st, end)                  = getRows (params !! 0) (params !! 1) nrows
    (ixs, iy, iy_err) = getColumns header (params !! 2) (params !! 3) (params !! 4)

    -- load data and split sets
    datum   = loadMtx content
    p       = length ixs

    x       = M.computeAs S $ M.throwEither $ M.stackInnerSlicesM $ map (datum <!) ixs
    y       = datum <! iy
    y_err   = datum <! iy_err

    x_train = M.computeAs S $ M.extractFromTo' (st :. 0) (end+1 :. p) x
    y_train = M.computeAs S $ M.extractFromTo' st (end+1) y 
    x_val   = M.computeAs S $ M.throwEither $ M.deleteRowsM st (Sz1 $ end - st + 1) x
    y_val   = M.computeAs S $ M.throwEither $ M.deleteColumnsM st (Sz1 $ end - st + 1) y

    y_err_train = if iy_err == -1 then Nothing else Just $ M.computeAs S $ M.extractFromTo' st (end+1) y_err
    y_err_val   = if iy_err == -1 then Nothing else Just $ M.computeAs S $ M.throwEither $ M.deleteColumnsM st (Sz1 $ end - st + 1) y_err
{-# inline processData #-}

chunksOf :: Int -> [e] -> [[e]]
chunksOf i ls = Prelude.map (Prelude.take i) (build (splitter ls))
 where
  splitter :: [e] -> ([e] -> a -> a) -> a -> a
  splitter [] _ n = n
  splitter l c n = l `c` splitter (Prelude.drop i l) c n
  build :: ((a -> [a] -> [a]) -> [a] -> [a]) -> [a]
  build g = g (:) []

splitData :: DataSet ->Int -> State StdGen (DataSet, DataSet)
splitData (x, y, mYErr) k = do
  if k == 1
    then pure ((x, y, mYErr), (x, y, mYErr))
    else do
      ixs' <- (state . shuffle) [0 .. sz-1]
      let ixs = chunksOf k ixs'

      let (x_tr, x_te) = getX ixs x
          (y_tr, y_te) = getY ixs y
          mY = fmap (getY ixs) mYErr
          (y_err_tr, y_err_te) = (fmap fst mY, fmap snd mY)
      pure ((x_tr, y_tr, y_err_tr), (x_te, y_te, y_err_te))
  where
    (MA.Sz sz) = MA.size y
    comp_x     = MA.getComp x
    comp_y     = MA.getComp y

    getX :: [[Int]] -> SRMatrix -> (SRMatrix, SRMatrix)
    getX ixs xs' = let xs = MA.toLists xs' :: [MA.ListItem MA.Ix2 Double]
                    in ( MA.fromLists' comp_x [xs !! ix | ixs_i <- ixs, ix <- Prelude.tail ixs_i]
                       , MA.fromLists' comp_x [xs !! ix | ixs_i <- ixs, let ix = Prelude.head ixs_i]
                       )
    getY :: [[Int]] -> PVector -> (PVector, PVector)
    getY ixs ys  = ( MA.fromList comp_y [ys MA.! ix | ixs_i <- ixs, ix <- Prelude.tail ixs_i]
                   , MA.fromList comp_y [ys MA.! ix | ixs_i <- ixs, let ix = Prelude.head ixs_i]
                   )

getTrain :: ((a, b1, c1, d1), (c2, b2), c3, d2) -> (a, b1, c2)
getTrain ((a, b, _, _), (c, _), _, _) = (a,b,c)

getX :: DataSet -> SRMatrix
getX (a, _, _) = a

getTarget :: DataSet -> PVector
getTarget (_, b, _) = b

getError :: DataSet -> Maybe PVector
getError (_, _, c) = c

loadTrainingOnly fname b = getTrain <$> loadDataset fname b
