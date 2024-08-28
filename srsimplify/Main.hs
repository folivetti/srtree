module Main (main) where

import Options.Applicative
import Text.ParseSR.IO ( withInput, withOutput )
import Text.ParseSR ( SRAlgs (..), Output (..) )
import System.Random ( getStdGen, mkStdGen )
import Text.Read ( readMaybe )
import Data.Char ( toLower, toUpper )
import Data.List ( intercalate )

-- Data type to store command line arguments
data Args = Args
    {   from        :: SRAlgs
      , to          :: Output
      , infile      :: String
      , outfile     :: String
      , varnames    :: String
    } deriving Show

-- parser of command line arguments
opt :: Parser Args
opt = Args
   <$> option sralgsReader
       ( long "from"
       <> short 'f'
       <> metavar ("[" <> intercalate "|" sralgsHelp <> "]")
       <> help "Input expression format" )
   <*> option srtoReader -- TODO
       ( long "to"
       <> short 't'
       <> metavar ("[" <> intercalate "|" srtoHelp <> "]")
       <> help "Output expression format" )
   <*> strOption
       ( long "input"
       <> short 'i'
       <> metavar "INPUT-FILE"
       <> showDefault
       <> value ""
       <> help "Input file containing expressions. \
               \ Empty string gets expression from stdin." )
   <*> strOption
       ( long "output"
       <> short 'o'
       <> metavar "OUTPUT-FILE"
       <> showDefault
       <> value ""
       <> help "Output file to store the stats in CSV format. \
                \ Empty string prints expressions to stdout." )
   <*> strOption
      ( long "varnames"
      <> short 'v'
      <> metavar "VARNAMES"
      <> showDefault
      <> value ""
      <> help "Comma separated string of variable names. \
               \ Empty string defaults to the algorithm default (x0, x1,..)." )

-- helper functions to show the possible options
mkDescription :: Show a => [a] -> [String]
mkDescription = map (envelope '\'' . map toLower . show)
  where
    envelope :: a -> [a] -> [a]
    envelope c xs = c : xs <> [c]
{-# INLINE mkDescription #-}

sralgsHelp :: [String]
sralgsHelp = mkDescription [toEnum 0 :: SRAlgs ..]
{-# INLINE sralgsHelp #-}

srtoHelp :: [String]
srtoHelp = mkDescription [toEnum 0 :: Output ..]
{-# INLINE srtoHelp #-}

-- helper functions to parse the options
mkReader :: Read a => String -> (a -> b) -> String -> ReadM b
mkReader err val sr = eitherReader
                    $ case readMaybe sr of
                        Nothing -> pure (Left err)
                        Just x  -> pure (Right (val x))

sralgsReader :: ReadM SRAlgs
sralgsReader =
  str >>= (mkReader errMsg id . map toUpper)
  where
    errMsg = "unknown algorithm. Available options are " <> intercalate "," sralgsHelp

srtoReader :: ReadM Output
srtoReader =
  str >>= (mkReader errMsg id . map toUpper)
  where
    errMsg = "unknown algorithm. Available options are " <> intercalate "," srtoHelp

main :: IO ()
main = do
  args <- execParser opts
  withInput (infile args) (from args) (varnames args) False True
    >>= withOutput (outfile args) (to args)
  where
    opts = info (opt <**> helper)
            ( fullDesc <> progDesc "Simplify an expression\
                                   \ using equality saturation."
           <> header "simplify - a CLI tool to simplify\
                     \ symbolic regression expressions with equality saturation." )
