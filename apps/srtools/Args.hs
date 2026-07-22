{--
   sssss  rrrr   ttttt  oooo  oooo  llll  ssss
  ss      rr rr    tt   oo  oo oo  oo ll   ss
   sss    rrrr     tt   oo  oo oo  oo ll    sss
     ss   rr rr    tt   oo  oo oo  oo ll      ss
  ssss    rr rr    tt    oooo   oooo  llll ssss

         Symbolic Regression Tools
--}
module Args where

import Data.Char (toLower, toUpper)
import Data.List (intercalate)
import Algorithm.SRTree.Likelihoods (Distribution (..))
import Algorithm.SRTree.ConfidenceIntervals (PType (..))
import Options.Applicative
import Text.ParseSR (SRAlgs (..))
import Text.Read (readMaybe)

data Args = Args
    { from        :: !SRAlgs
    , infile      :: !String
    , outfile     :: !String
    , dataset     :: !String
    , test        :: !String
    , niter       :: !Int
    , hasHeader   :: !Bool
    , simpl       :: !Bool
    , dist        :: !Distribution
    , restart     :: !Bool
    , rseed       :: !Int
    , toScreen    :: !Bool
    , useProfile  :: !Bool
    , simple      :: !Bool
    , sigma       :: !Double
    , alpha       :: !Double
    , ptype       :: !PType
    , contour     :: !Bool
    , debug       :: !Bool
    } deriving Show

opt :: Parser Args
opt = Args
   <$> option sralgsReader
       ( long "from" <> short 'f'
       <> metavar ("[" <> intercalate "|" sralgsHelp <> "]")
       <> help "Input expression format" )
   <*> strOption
       ( long "input" <> short 'i' <> metavar "INPUT-FILE"
       <> showDefault <> value ""
       <> help "Input file containing expressions." )
   <*> strOption
       ( long "output" <> short 'o' <> metavar "OUTPUT-FILE"
       <> showDefault <> value ""
       <> help "Output file for CSV stats." )
   <*> strOption
       ( long "dataset" <> short 'd' <> metavar "DATASET-FILENAME"
       <> help "Dataset filename." )
   <*> strOption
       ( long "test" <> metavar "TEST"
       <> showDefault <> value ""
       <> help "Test dataset filename." )
   <*> option auto
       ( long "niter" <> metavar "NITER"
       <> showDefault <> value 10
       <> help "Optimisation iterations." )
   <*> switch ( long "hasheader" <> help "Dataset has header row." )
   <*> switch ( long "simplify" <> help "Apply basic simplification." )
    <*> option distRead
         ( long "distribution" <> metavar "DIST"
         <> showDefault <> value Gaussian
         <> help "Distribution: MSE, Gaussian, HGaussian, Bernoulli, Poisson, ROXY, Log10." )
   <*> switch ( long "restart" <> help "Random restart of parameters." )
   <*> option auto
       ( long "seed" <> metavar "SEED"
       <> showDefault <> value (-1)
       <> help "Random seed." )
   <*> switch ( long "report"
       <> help "Detailed screen report with CIs and predictions." )
   <*> switch ( long "profile"
       <> help "Use profile likelihood for CIs." )
   <*> switch ( long "simple"
       <> help "Calculate only SSE." )
   <*> option auto
       ( long "sigma" <> metavar "SIGMA"
       <> showDefault <> value 0.001
       <> help "Error estimate for Gaussian." )
   <*> option auto
       ( long "alpha" <> metavar "ALPHA"
       <> showDefault <> value 0.05
       <> help "Significance level." )
   <*> option auto
        ( long "ptype" <> metavar "[Bates|ODE|Constrained]"
        <> showDefault <> value Constrained
        <> help "Profile method. Default: Constrained." )
    <*> switch ( long "contour" <> help "Display contour plot points." )
    <*> switch ( long "debug" <> help "Display data points for the plots (except prediction intervals)." )

sralgsHelp :: [String]
sralgsHelp = map (envelope '\'' . map toLower . show) [(toEnum 0 :: SRAlgs) ..]
  where envelope c xs = c : xs <> [c]

distRead :: ReadM Distribution
distRead = eitherReader $ \s ->
  let cap "" = ""
      cap (c:cs) = toUpper c : map toLower cs
      sLower = map toLower s
  in case sLower of
       "mse"          -> Right LeastSquares
       "leastsquares" -> Right LeastSquares
       "gaussian"     -> Right Gaussian
       "hgaussian"    -> Right HGaussian
       "bernoulli"    -> Right Bernoulli
       "poisson"      -> Right Poisson
       "roxy"         -> Right ROXY
       "log10"        -> Right Poisson
       _              -> Left ("unsupported distribution " ++ s)

sralgsReader :: ReadM SRAlgs
sralgsReader = eitherReader $ \s ->
  case readMaybe (map toUpper s) of
    Nothing -> Left ("unknown format. Options: " ++ intercalate "," sralgsHelp)
    Just x  -> Right x
