module Args where

import Data.Char ( toLower, toUpper )
import Data.List ( intercalate )
import Algorithm.SRTree.Likelihoods ( Distribution (..) )
import Algorithm.SRTree.ConfidenceIntervals ( PType (..) )
import Options.Applicative
import Text.ParseSR ( SRAlgs (..) )
import Text.Read ( readMaybe )

-- Data type to store command line arguments
data Args = Args
    {   from        :: SRAlgs
      , infile      :: String
      , outfile     :: String
      , dataset     :: String
      , test        :: String
      , niter       :: Int
      , hasHeader   :: Bool
      , simpl       :: Bool
      , dist        :: Distribution
      , msErr       :: Maybe Double
      , restart     :: Bool
      , rseed       :: Int
      , toScreen    :: Bool
      , useProfile  :: Bool
      , alpha       :: Double
      , ptype       :: PType
    } deriving Show

-- parser of command line arguments
opt :: Parser Args
opt = Args
   <$> option sralgsReader
       ( long "from"
       <> short 'f'
       <> metavar ("[" <> intercalate "|" sralgsHelp <> "]")
       <> help "Input expression format" )
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
       ( long "dataset"
       <> short 'd'
       <> metavar "DATASET-FILENAME"
       <> help "Filename of the dataset used for optimizing the parameters. \
               \ Empty string omits stats that make use of the training data. \
               \ It will auto-detect and handle gzipped file based on gz extension. \
               \ It will also auto-detect the delimiter.\n\
               \ The filename can include extra information: \
               \ filename.csv:start:end:target:vars where start and end \
               \ corresponds to the range of rows that should be used for fitting,\
               \ target is the column index (or name) of the target variable and cols\
               \ is a comma separated list of column indeces or names of the variables\
               \ in the same order as used by the symbolic model." )
   <*> strOption
       ( long "test"
       <> metavar "TEST"
       <> showDefault
       <> value ""
       <> help "Filename of the test dataset.\
               \ Empty string omits stats that make use of the training data.\
               \ It can have additional information as in the training set,\
               \ but the validation range will be discarded." )
   <*> option auto
       ( long "niter"
       <> metavar "NITER"
       <> showDefault
       <> value 10
       <> help "Number of iterations for the optimization algorithm.")
   <*> switch
       ( long "hasheader"
       <> help "Uses the first row of the csv file as header.")
   <*> switch
        ( long "simplify"
        <> help "Apply basic simplification." )
   <*> option distRead
        ( long "distribution"
        <> metavar ("[" <> intercalate "|" distHelp <> "]")
        <> showDefault
        <> value Gaussian
        <> help "Minimize negative log-likelihood following one of\
                \ the avaliable distributions.\
                \ The default is Gaussian."
        )
   <*> option s2Reader
       ( long "sErr"
       <> metavar "Serr"
       <> showDefault
       <> value Nothing
       <> help "Estimated standard error of the data.\
                \ If not passed, it uses the model MSE.")
   <*> switch
        ( long "restart"
        <> help "If set, it samples the initial values of\
                 \ the parameters using a Gaussian distribution N(0, 1),\
                 \ otherwise it uses the original values of the expression." )
   <*> option auto
       ( long "seed"
       <> metavar "SEED"
       <> showDefault
       <> value (-1)
       <> help "Random seed to initialize the parameters values.\
                \ Used only if restart is enabled.")
   <*> switch
        ( long "report"
        <> help "If set, reports the analysis in a user-friendly\
                \ format instead of csv. It will also include\
                \ confidence interval for the parameters and predictions" )
   <*> switch
        ( long "profile"
        <> help "If set, it will use profile likelihood to calculate the CIs." )
   <*> option auto
       ( long "alpha"
       <> metavar "ALPHA"
       <> showDefault
       <> value 0.05
       <> help "Significance level for confidence intervals.")
    <*> option auto
        ( long "ptype"
        <> metavar "[Bates | ODE | Constrained]"
        <> showDefault
        <> value Constrained
        <> help "Profile Likelihood method. Default: Constrained. NOTE: Constrained method only calculates the endpoint."
        )

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

distHelp :: [String]
distHelp = mkDescription [toEnum 0 :: Distribution ..]
{-# INLINE distHelp #-}

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

s2Reader :: ReadM (Maybe Double)
s2Reader =
  str >>= \s -> mkReader ("wrong format " <> s) Just s

distRead :: ReadM Distribution
distRead =
  str >>= \s -> mkReader ("unsupported distribution " <> s) id (capitalize s)
  where
    capitalize ""     = ""
    capitalize (c:cs) = toUpper c : map toLower cs
