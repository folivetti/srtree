{-# language OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.ParseSR
-- Copyright   :  (c) Fabricio Olivetti 2021 - 2024
-- License     :  BSD3
-- Maintainer  :  fabricio.olivetti@gmail.com
-- Stability   :  experimental
-- Portability :  ConstraintKinds
--
-- Functions to parse a string representing an expression
--
-----------------------------------------------------------------------------
module Text.ParseSR ( parseSR, parseSR', showOutput, SRAlgs(..), Output(..) )
    where

import Control.Applicative ((<|>))
import Data.Attoparsec.ByteString.Char8
import Data.Attoparsec.Expr
import qualified Data.ByteString.Char8 as B
import Data.Char (toLower)
import Data.List (sortOn)
import Data.SRTree
import qualified Data.SRTree.Print as P
import Debug.Trace (trace)

-- * Data types

-- | Parser of a symbolic regression tree with `Int` variable index and
-- numerical values represented as `Double`. The numerical values type
-- can be changed with `fmap`.
type ParseTree = Parser (Fix SRTree)

-- * Data types and caller functions

-- | Supported algorithms.
data SRAlgs = TIR | HL | OPERON | BINGO | GOMEA | PYSR | SBP | EPLEX deriving (Show, Read, Enum, Bounded)

-- | Supported outputs.
data Output = PYTHON | MATH | TIKZ | LATEX deriving (Show, Read, Enum, Bounded)

-- | Returns the corresponding function from Data.SRTree.Print for a given `Output`.
showOutput :: Output -> Fix SRTree -> String
showOutput PYTHON = P.showPython
showOutput MATH   = P.showExpr
showOutput TIKZ   = P.showTikz
showOutput LATEX  = P.showLatex

-- | Calls the corresponding parser for a given `SRAlgs`
--
-- >>> fmap (showOutput MATH) $ parseSR OPERON "lambda,theta" False "lambda ^ 2 - sin(theta*3*lambda)"
-- Right "((x0 ^ 2.0) - Sin(((x1 * 3.0) * x0)))"
parseSR :: SRAlgs -> B.ByteString -> Bool -> B.ByteString -> Either String (Fix SRTree)
parseSR HL     header reparam = eitherResult . (`feed` "") . parse (parseHL True reparam $ splitHeader header) . putEOL . B.strip
parseSR BINGO  header reparam = eitherResult . (`feed` "") . parse (parseBingo True reparam $ splitHeader header) . putEOL . B.strip
parseSR TIR    header reparam = eitherResult . (`feed` "") . parse (parseTIR True reparam $ splitHeader header) . putEOL . B.strip
parseSR OPERON header reparam = eitherResult . (`feed` "") . parse (parseOperon True reparam $ splitHeader header) . putEOL . B.strip
parseSR GOMEA  header reparam = eitherResult . (`feed` "") . parse (parseGOMEA True reparam $ splitHeader header) . putEOL . B.strip
parseSR SBP    header reparam = eitherResult . (`feed` "") . parse (parseGOMEA True reparam $ splitHeader header) . putEOL . B.strip
parseSR EPLEX  header reparam = eitherResult . (`feed` "") . parse (parseGOMEA True reparam $ splitHeader header) . putEOL . B.strip
parseSR PYSR   header reparam = eitherResult . (`feed` "") . parse (parsePySR True reparam $ splitHeader header) . putEOL .  B.strip

parseSR' :: SRAlgs -> B.ByteString -> Bool -> B.ByteString -> Either String (Fix SRTree)
parseSR' HL     header reparam = eitherResult . (`feed` "") . parse (parseHL False reparam $ splitHeader header) . putEOL . B.strip
parseSR' BINGO  header reparam = eitherResult . (`feed` "") . parse (parseBingo False reparam $ splitHeader header) . putEOL . B.strip
parseSR' TIR    header reparam = eitherResult . (`feed` "") . parse (parseTIR False reparam $ splitHeader header) . putEOL . B.strip
parseSR' OPERON header reparam = eitherResult . (`feed` "") . parse (parseOperon False reparam $ splitHeader header) . putEOL . B.strip
parseSR' GOMEA  header reparam = eitherResult . (`feed` "") . parse (parseGOMEA False reparam $ splitHeader header) . putEOL . B.strip
parseSR' SBP    header reparam = eitherResult . (`feed` "") . parse (parseGOMEA False reparam $ splitHeader header) . putEOL . B.strip
parseSR' EPLEX  header reparam = eitherResult . (`feed` "") . parse (parseGOMEA False reparam $ splitHeader header) . putEOL . B.strip
parseSR' PYSR   header reparam = eitherResult . (`feed` "") . parse (parsePySR False reparam $ splitHeader header) . putEOL .  B.strip

eitherResult' :: Show r => Result r -> Either String r
eitherResult' res = trace (show res) $ eitherResult res

-- * Parsers

-- | Creates a parser for a binary operator
binary :: B.ByteString -> (a -> a -> a) -> Assoc -> Operator B.ByteString a
binary name fun  = Infix (do{ string (B.cons ' ' (B.snoc name ' ')) <|> string name; pure fun })

-- | Creates a parser for a unary function
prefix :: B.ByteString -> (a -> a) -> Operator B.ByteString a
prefix  name fun = Prefix (do{ string name; pure fun })

-- | Envelopes the parser in parens
parens :: Parser a -> Parser a
parens e = do{ string "("; e' <- e; string ")"; pure e' } <?> "parens"

-- | Parse an expression using a user-defined parser given by the `Operator` lists containing
-- the name of the functions and operators of that SR algorithm, a list of parsers `binFuns` for binary functions
-- a parser `var` for variables, a boolean indicating whether to change floating point values to free
-- parameters variables, and a list of variable names with their corresponding indexes.
parseExpr :: Bool -> [[Operator B.ByteString (Fix SRTree)]] -> [ParseTree -> ParseTree] -> ParseTree -> Bool -> [(B.ByteString, Int)] -> ParseTree
parseExpr relabel table binFuns var reparam header =
    do e <- if relabel then (relabelParams <$> expr) else expr
       many1' space
       pure e
  where
    term  = parens expr <|> enclosedAbs expr <|> choice (map ($ expr) binFuns) <|> coef <|> varC <?> "term"
    expr  = buildExpressionParser table term
    coef  = if reparam 
              then do eNumber <- intOrDouble
                      case eNumber of
                        Left x  -> pure $ fromIntegral x
                        Right _ -> pure $ param 0
              else Fix . Const <$> signed double <?> "const"
    varC = if null header
             then var
             else var <|> varHeader

    varHeader        = choice $ map (uncurry getParserVar) $ sortOn (negate . B.length . fst) header
    getParserVar k v = (string k <|> enveloped k) >> pure (Fix $ Var v)
    enveloped s      = (char ' ' <|> char '(') >> string s >> (char ' ' <|> char ')') >> pure ""

enumerate :: [a] -> [(a, Int)]
enumerate = (`zip` [0..])

splitHeader :: B.ByteString -> [(B.ByteString, Int)]
splitHeader = enumerate . B.split ','

-- | Tries to parse as an `Int`, if it fails, 
-- parse as a Double.
intOrDouble :: Parser (Either Int Double)
intOrDouble = eitherP parseInt (signed double)
  where
      parseInt :: Parser Int
      parseInt = do x <- signed decimal
                    c <- peekChar
                    case c of                      
                      Just '.' -> digit >> pure 0
                      Just 'e' -> digit >> pure 0
                      Just 'E' -> digit >> pure 0
                      _   -> pure x

putEOL :: B.ByteString -> B.ByteString
putEOL bs | B.last bs == '\n' = bs
          | otherwise         = B.snoc bs '\n'

-- * Special case functions

-- | analytic quotient
aq :: Fix SRTree -> Fix SRTree -> Fix SRTree
aq x y = x / sqrt (1 + y ** 2)

log1p :: Fix SRTree -> Fix SRTree
log1p x = log (1 + x)

log10 :: Fix SRTree -> Fix SRTree
log10 x = log x / log 10

log2 :: Fix SRTree -> Fix SRTree
log2 x = log x / log 2

cbrt :: Fix SRTree -> Fix SRTree
cbrt x = x ** (1/3)

cube :: Fix SRTree -> Fix SRTree
cube x = Fix $ Uni Cube x

sqrtabs :: Fix SRTree -> Fix SRTree
sqrtabs x = Fix $ Uni SqrtAbs x

logabs :: Fix SRTree -> Fix SRTree
logabs x = Fix $ Uni LogAbs x

-- Parse `abs` functions as | x |
enclosedAbs :: Num a => Parser a -> Parser a
enclosedAbs expr = do char '|'
                      e <- expr
                      char '|'
                      pure $ abs e

-- | Parser for binary functions
binFun :: B.ByteString -> (a -> a -> a) -> Parser a -> Parser a
binFun name f expr = do string name
                        many' space >> char '(' >> many' space
                        e1 <- expr
                        many' space >> char ',' >> many' space -- many' space >> char ',' >> many' space
                        e2 <- expr
                        many' space >> char ')'
                        pure $ f e1 e2 

-- * Custom parsers for SR algorithms

-- | parser for Transformation-Interaction-Rational.
parseTIR :: Bool -> Bool -> [(B.ByteString, Int)] -> ParseTree
parseTIR b = parseExpr b (prefixOps : binOps) binFuns var
  where
    binFuns   = [ ]
    prefixOps = map (uncurry prefix)
                [   ("id", id), ("abs", abs)
                  , ("sinh", sinh), ("cosh", cosh), ("tanh", tanh)
                  , ("sin", sin), ("cos", cos), ("tan", tan)
                  , ("asinh", asinh), ("acosh", acosh), ("atanh", atanh)
                  , ("asin", asin), ("acos", acos), ("atan", atan)
                  , ("sqrtabs", sqrtabs), ("sqrt", sqrt), ("cbrt", cbrt), ("square", (**2))
                  , ("logabs", logabs), ("log", log), ("exp", exp), ("cube", cube), ("recip", recip)
                  , ("Id", id), ("Abs", abs)
                  , ("Sinh", sinh), ("Cosh", cosh), ("Tanh", tanh)
                  , ("Sin", sin), ("Cos", cos), ("Tan", tan)
                  , ("ASinh", asinh), ("ACosh", acosh), ("ATanh", atanh)
                  , ("ASin", asin), ("ACos", acos), ("ATan", atan)
                  , ("SqrtAbs", sqrtabs), ("Sqrt", sqrt), ("Cbrt", cbrt), ("Square", (**2))
                  , ("LogAbs", logabs), ("Log", log), ("Exp", exp), ("Recip", recip), ("Cube", cube)
                ]
    binOps = [[binary "^" (**) AssocLeft], [binary "**" (**) AssocLeft]
            , [binary "*" (*) AssocLeft, binary "/" (/) AssocLeft]
            , [binary "+" (+) AssocLeft, binary "-" (-) AssocLeft]
            , [binary "|**|" powabs AssocLeft], [binary "aq" aq AssocLeft]
            ]
    powabs l r = Fix $ Bin PowerAbs l r
    aq l r = Fix $ Bin AQ l r

    var = do char 'x'
             ix <- decimal
             pure $ Fix $ Var ix
          <|> do char 't'
                 ix <- decimal
                 pure $ Fix $ Param ix
          <?> "var"

-- | parser for Operon.
parseOperon :: Bool -> Bool -> [(B.ByteString, Int)] -> ParseTree
parseOperon b = parseExpr b (prefixOps : binOps) binFuns var
  where
    binFuns   = [ binFun "pow" (**) ]
    prefixOps = map (uncurry prefix)
                [ ("abs", abs), ("cbrt", cbrt)
                , ("acos", acos), ("cosh", cosh), ("cos", cos)
                , ("asin", asin), ("sinh", sinh), ("sin", sin)
                , ("exp", exp), ("log", log)
                , ("sqrt", sqrt), ("square", (**2))
                , ("atan", atan), ("tanh", tanh), ("tan", tan)
                ]
    binOps = [[binary "^" (**) AssocLeft]
            , [binary "*" (*) AssocLeft, binary "/" (/) AssocLeft]
            , [binary "+" (+) AssocLeft, binary "-" (-) AssocLeft]
            ]
    var = do char 'X'
             ix <- decimal
             pure $ Fix $ Var (ix - 1) -- Operon is not 0-based
          <?> "var"

-- | parser for HeuristicLab.
parseHL :: Bool -> Bool -> [(B.ByteString, Int)] -> ParseTree
parseHL b = parseExpr b (prefixOps : binOps) binFuns var
  where
    binFuns   = [ binFun "aq" aq ]
    prefixOps = map (uncurry prefix)
                [ ("logabs", log.abs), ("sqrtabs", sqrt.abs) -- the longer versions should come first
                , ("abs", abs), ("exp", exp), ("log", log)
                , ("sqrt", sqrt), ("sqr", (**2)), ("cube", (**3))
                , ("cbrt", cbrt), ("sin", sin), ("cos", cos)
                , ("tan", tan), ("tanh", tanh)
                ]
    binOps = [[binary "^" (**) AssocLeft]
            , [binary "*" (*) AssocLeft, binary "/" (/) AssocLeft]
            , [binary "+" (+) AssocLeft, binary "-" (-) AssocLeft]
            ]
    var = do char 'x'
             ix <- decimal
             pure $ Fix $ Var ix
          <?> "var"

-- | parser for Bingo
parseBingo :: Bool -> Bool -> [(B.ByteString, Int)] -> ParseTree
parseBingo b = parseExpr b (prefixOps : binOps) binFuns var
  where
    binFuns = []
    prefixOps = map (uncurry prefix)
                [ ("abs", abs), ("exp", exp), ("log", log.abs)
                , ("sqrt", sqrt.abs)
                , ("sinh", sinh), ("cosh", cosh)
                , ("sin", sin), ("cos", cos)
                ]
    binOps = [[binary "^" (**) AssocLeft]
            , [binary "/" (/) AssocLeft, binary "" (*) AssocLeft]
            , [binary "+" (+) AssocLeft, binary "-" (-) AssocLeft]
            ]
    var = do string "X_"
             ix <- decimal
             pure $ Fix $ Var ix
          <?> "var"

-- | parser for GOMEA
parseGOMEA :: Bool -> Bool -> [(B.ByteString, Int)] -> ParseTree
parseGOMEA b = parseExpr b (prefixOps : binOps) binFuns var
  where
    binFuns = []
    prefixOps = map (uncurry prefix)
                [ ("exp", exp), ("plog", log.abs)
                , ("sqrt", sqrt.abs)
                , ("sin", sin), ("cos", cos)
                ]
    binOps = [[binary "^" (**) AssocLeft]
            , [binary "/" (/) AssocLeft, binary "*" (*) AssocLeft, binary "aq" aq AssocLeft]
            , [binary "+" (+) AssocLeft, binary "-" (-) AssocLeft]
            ]
    var = do string "x"
             ix <- decimal
             pure $ Fix $ Var ix
          <?> "var"

-- | parser for PySR
parsePySR :: Bool -> Bool -> [(B.ByteString, Int)] -> ParseTree
parsePySR b = parseExpr b (prefixOps : binOps) binFuns var
  where
    binFuns   = [ binFun "pow" (**) ]
    prefixOps = map (uncurry prefix)
                [ ("abs", abs), ("exp", exp)
                , ("square", (**2)), ("cube", (**3)), ("neg", negate)
                , ("acosh_abs", acosh . (+1) . abs), ("acosh", acosh), ("asinh", asinh)
                , ("acos", acos), ("asin", asin), ("atan", atan)
                , ("sqrt_abs", sqrt.abs), ("sqrt", sqrt)
                , ("sinh", sinh), ("cosh", cosh), ("tanh", tanh)
                , ("sin", sin), ("cos", cos), ("tan", tan)
                , ("log10", log10), ("log2", log2), ("log1p", log1p) 
                , ("log_abs", log.abs), ("log10_abs", log10 . abs)
                , ("log", log)
                ]
    binOps = [[binary "^" (**) AssocLeft]
            , [binary "/" (/) AssocLeft, binary "*" (*) AssocLeft]
            , [binary "+" (+) AssocLeft, binary "-" (-) AssocLeft]
            ]
    var = do string "x"
             ix <- decimal
             pure $ Fix $ Var ix
          <?> "var"
