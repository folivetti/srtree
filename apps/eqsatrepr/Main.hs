{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.SRTree 
import Algorithm.EqSat.Egraph
import Data.SRTree.Print 
import qualified Data.Map as Map
import qualified Data.IntMap as IM
import Control.Monad.State.Strict
import System.Random
import Data.SRTree.Recursion ( cata )
import Control.Monad
import Control.Monad.Reader
import qualified Data.SRTree.Random as RT
import Data.List ( nub )
import Algorithm.EqSat.DB
import Algorithm.EqSat.Info
import Algorithm.EqSat.Build
import Algorithm.EqSat.Queries
import Algorithm.EqSat

isConstPt :: Pattern -> Map.Map ClassOrVar ClassOrVar -> EGraph -> Bool
isConstPt (VarPat c) subst eg =
    let cid = getInt $ subst Map.! (Right $ fromEnum c)
    in case (_consts . _info) (_eClass eg IM.! cid) of
         ConstVal x -> True
         _ -> False
isConstPt _ _ _ = False

notZero (VarPat c) subst eg =
  let cid = getInt $ subst Map.! (Right $ fromEnum c)
   in case (_consts . _info) (_eClass eg IM.! cid) of
         ConstVal x -> x /= 0
         _ -> True
notZero _ _ _ = True

rewriteBasic =
    [
      "x" * "x" :=> "x" ** 2
    , "x" * "y" :=> "y" * "x"
    , "x" + "y" :=> "y" + "x"
    , ("x" ** "y") * "x" :=> "x" ** ("y" + 1) :| isConstPt "y"
    -- , ("x" * "y") / "x" :=> "y"
    , ("x" ** "y") * ("x" ** "z") :=> "x" ** ("y" + "z")
    , ("x" + "y") + "z" :=> "x" + ("y" + "z")
    , ("x" + "y") - "z" :=> "x" + ("y" - "z")
    , ("x" * "y") * "z" :=> "x" * ("y" * "z")
    , ("x" * "y") + ("x" * "z") :=> "x" * ("y" + "z")
    , "x" - ("y" + "z") :=> ("x" - "y") - "z"
    , "x" - ("y" - "z") :=> ("x" - "y") + "z"
    , ("x" * "y") / "z" :=> ("x" / "z") * "y"
    , (("w" * "x") / ("z" * "y") :=> ("w" / "z") * ("x" / "y") :| isConstPt "w") :| isConstPt "z"
    , ((("x" * "y") + ("z" * "w")) :=> "x" * ("y" + ("z" / "x") * "w") :| isConstPt "x") :| isConstPt "z"
    , ((("x" * "y") - ("z" * "w")) :=> "x" * ("y" - ("z" / "x") * "w") :| isConstPt "x") :| isConstPt "z"
    , ((("x" * "y") * ("z" * "w")) :=> ("x" * "z") * ("y" * "w") :| isConstPt "x") :| isConstPt "z"
    ]

rewritesFun =
    [
      log (sqrt "x") :=> 0.5 * log "x"
    , log (exp "x")  :=> "x"
    , exp (log "x")  :=> "x"
    , "x" ** (1/2)   :=> sqrt "x"
    ,  log ("x" * "y") :=> log "x" + log "y"
    , log ("x" / "y") :=> log "x" - log "y"
    , log ("x" ** "y") :=> "y" * log "x"
    , sqrt ("y" * "x") :=> sqrt "y" * sqrt "x"
    , sqrt ("y" / "x") :=> sqrt "y" / sqrt "x"
    , abs ("x" * "y") :=> abs "x" * abs "y"
    ,  sqrt ("z" * ("x" - "y")) :=> sqrt (negate "z") * sqrt ("y" - "x")
    , sqrt ("z" * ("x" + "y")) :=> sqrt "z" * sqrt ("x" + "y")
    ]

-- Rules that reduces redundant parameters
constReduction =
    [
      0 + "x" :=> "x"
    , "x" - 0 :=> "x"
    , 1 * "x" :=> "x"
    , 0 * "x" :=> 0
    , 0 / "x" :=> 0 :| notZero "x"
    , "x" - "x" :=> 0
    , "x" / "x" :=> 1 :| notZero "x"
    , "x" ** 1 :=> "x"
    , 0 ** "x" :=> 0
    , 1 ** "x" :=> 1
    , "x" * (1 / "x") :=> 1
    , 0 - "x" :=> negate "x"
    , "x" + negate "y" :=> "x" - "y"
    , negate ("x" * "y") :=> (negate "x") * "y" :| isConstPt "x"
    ]


x0 = var 0
x1 = var 1
x2 = var 2
x3 = var 3
x4 = var 4
x5 = var 5
x6 = var 6
x7 = var 7
x8 = var 8

trees :: [Fix SRTree]
trees = [  (4.059e-3 + (0.988153 * (((1.923901 * x1) * ((-1.228652 * x0) * (-0.278891 * x2))) * ((((((-0.35119 * x5) + (-0.354523 * x3)) - (-0.369148 * x6)) + ((0.342012 * x4) + (2.054e-2 * x2))) - ((0.349297 * x7) - (0.336081 * x8)))))))
        , ((14.316036 * (((((0.975231 * x4)) * (1.259663 * x3)) * (0.314221 * x0)) * (0.178249 * x2))))
        , (1.2 * (3.4 * x1 * 4.2 * x0) / ((3.2 * x2) * ((1.1 * x3) * (3.5 * x4))))
        , ((1.002563 * (((0.428416 * x1) * (2.554566 * x0)) / (((2.53743 * x2) * (2.327917 * x3)) * (2.320736 * x3)))))
        , (2.82238 + (3.092415 * (sin(log(abs(0.0))) * ((-0.162842 * x2) - (0.116404 * x1)))))
        , log(0.0) * ((1.2 * x2) - (0.116404 * x1))
        , ((x0 - x0) * x0)
        , (1 + 1) - 1
        , (x0 + x0) - x0
        , (x0/x0 + 1) - 1
        , (x0 * x0) / x0
        , sin(log(0.0))
        , -1 * exp(log(abs(-1.3 * (x1 - 1.2 * x2))))
        , -1 * exp(log(abs((1.3 * x1 + 1.56 * x2))))
        , -1 * exp(log(abs((-1.3 * x1 + 1.56 * x2))))
        , -1 * exp(log(abs(((0.256 * x3) + (-0.2561 * x2)))))
        , log(abs(-1.199026) * abs((x2 + (1.191617 * x3))))
        , log(abs((1.199026 * x2) + (-1.191617 * x3)))
        , 1 * x0
        , x0 * 1
        , x0 + x1
        , x1 + x0
        , x0 + sin(x1)
        , x0 * (1 + x1)
        , (1 + x1) * x0
        , x0 + x0 * x1
        , (x0 + x1) + 2
        , x0 + (x1 + 2)
        , x0 + (2 + x1)
        , log(abs(0)) + x0
        , abs(((1.3 * x1) + (-1.56 * x2))) * (-1.0)
        ]


myCost :: SRTree Int -> Int
myCost (Var _) = 1
myCost (Const _) = 1
myCost (Param _) = 1
myCost (Bin op l r) = 2 + l + r
myCost (Uni _ t) = 3 + t

rewrites = rewriteBasic <> constReduction <> rewritesFun

testEqSat :: Fix SRTree -> IO ()
testEqSat t = do
    let e = eqSat t rewrites myCost 30 `evalState` emptyGraph
    putStr $ (showExpr t) <> " == " <> (showExpr e) <> "\n"

testEqSats :: IO ()
testEqSats = mapM_ testEqSat trees



initialPop :: HyperParams -> Rng [Fix SRTree]
initialPop hyperparams = do
   let depths = [3 .. _maxDepth hyperparams]
   pop <- forM depths $ \md ->
           do let m = _popSize hyperparams `div` (_maxDepth hyperparams - 3 + 1)
                  g = take m $ cycle [True, False]
              mapM (randomTree hyperparams{ _maxDepth = md}) g
   pure (concat pop)
{-# INLINE initialPop #-}

data Method = Grow | Full

type Rng a = StateT StdGen IO a
type GenUni = Fix SRTree -> Fix SRTree
type GenBin = Fix SRTree -> Fix SRTree -> Fix SRTree

toss :: Rng Bool
toss = state random
{-# INLINE toss #-}

randomRange :: (Ord val, Random val) => (val, val) -> Rng val
randomRange rng = state (randomR rng)
{-# INLINE randomRange #-}

randomFrom :: [a] -> Rng a
randomFrom funs = do n <- randomRange (0, length funs - 1)
                     pure $ funs !! n
{-# INLINE randomFrom #-}

countNodes' :: Fix SRTree -> Int
countNodes' = cata alg
  where
    alg (Var _)     = 1
    alg (Param _)   = 1
    alg (Const _)   = 0
    alg (Bin _ l r) = 1 + l + r
    alg (Uni Abs t) = t
    alg (Uni _ t)   = 1 + t
{-# INLINE countNodes' #-}


randomTree :: HyperParams -> Bool -> Rng (Fix SRTree)
randomTree hp grow
  | depth <= 1 || size <= 2 = randomFrom term
  | (min_depth >= 0 || (depth > 2 && not grow)) && size > 2 = genNonTerm
  | otherwise = genTermOrNon
  where
    min_depth = _minDepth hp
    depth     = _maxDepth hp
    size      = _maxSize hp
    term      = _term hp
    nonterm   = _nonterm hp

    genNonTerm =
       do et <- randomFrom nonterm
          case et of
            Left uniT -> uniT <$> randomTree hp{_minDepth = min_depth-1, _maxDepth = depth - 1, _maxSize = size - 1} grow
            Right binT -> do l <- randomTree hp{_minDepth = min_depth-1, _maxDepth = depth - 1, _maxSize = size - 1} grow
                             r <- randomTree hp{_minDepth = min_depth-1, _maxDepth = depth - 1, _maxSize = size - 1 - countNodes' l} grow
                             pure (binT l r)
    genTermOrNon = do r <- toss
                      if r
                        then randomFrom term
                        else genNonTerm
{-# INLINE randomTree #-}

data HyperParams =
    HP { _minDepth  :: Int
       , _maxDepth  :: Int
       , _maxSize   :: Int
       , _popSize   :: Int
       , _tournSize :: Int
       , _pc        :: Double
       , _pm        :: Double
       , _term      :: [Fix SRTree]
       , _nonterm   :: [Either GenUni GenBin]
       }


countSubTrees = do ecs <- gets (IM.keys . _eClass) 
                   subs <- mapM (\ec -> getAllExpressionsFrom ec >>= pure . length) ecs 
                   pure $ sum subs 
countRootTrees rs = do subs <- mapM (\ec -> getAllExpressionsFrom ec >>= pure . length) rs
                       pure $ sum subs

terms = [var 0, var 1, var 2, param 0, param 1, param 2, param 3]
nonterms = [Right (+), Right (-), Right (*), Right (/), Right (\l r -> abs l ** r), Left (1/)]

calcRedundancy :: Int -> IO ()
calcRedundancy nPop = do
    let hp = HP 2 4 10 nPop 2 1.0 0.25 terms nonterms
        p  = RT.P [0, 1, 2, 3, 4, 5] (0, 3) (1, 3) [Log]
    g <- getStdGen
    pop <- (`evalStateT` g)  <$> replicateM nPop $ runReaderT (RT.randomTree 10) p
    let nSubsSingle = sum $ map (\p -> (fromTrees myCost [p] >> countSubTrees) `evalState` emptyGraph) pop 
        myEqPop = do rs <- fromTrees myCost pop
                     let rsN = nub rs 
                     cnt <- countSubTrees
                     pure (cnt, rsN)
        (nSubs, rsN) = myEqPop `evalState` emptyGraph 
    putStr "Ratio of subtrees: "
    putStrLn $ show nSubsSingle <> "/" <> show nSubs <> " = " <> show (fromIntegral nSubsSingle / fromIntegral nSubs)
    let nSubsR = sum $ map (\p -> (fromTree myCost p >>= \r -> countRootTrees [r]) `evalState` emptyGraph) pop
        nSubsSingleR = (fromTrees myCost pop >>= countRootTrees) `evalState` emptyGraph
    putStr "Ratio of rooted trees: "
    putStrLn $ show nSubsSingleR <> "/" <> show nSubsR <> " = " <> show (fromIntegral nSubsSingleR / fromIntegral nSubsR)

main :: IO ()
main = do 
    let t1 = var 0 + 12.0
        t2 = 3.2 * var 0
        t3 = 3.2 * var 0 / (var 0 + 12.0)
        t4 = var 0 + sin (var 0)
        t5 = 1.5 + exp 5.2
        egraphRun :: EGraphST IO ()
        egraphRun = do v <- fromTrees myCost [t3,t1,t2,t4]
                       roots <- findRootClasses
                       ecId  <- gets ((Map.! (Var 0)) . _eNodeToEClass)
                       calculateHeights 
                       h <- gets (map _height . IM.elems . _eClass)
                       v <- gets (map (_consts . _info) . IM.elems . _eClass)
                       c <- gets (map (_cost . _info) . IM.elems . _eClass)
                       parents <- gets (_parents . (IM.! ecId) . _eClass)
                       exprs <- mapM getExpressionFrom roots
                       exprs' <- gets (IM.keys . _eClass) >>= mapM getExpressionFrom 

                       lift $ do putStr "Parents of x0: "
                                 print parents 
                                 putStrLn "\nexpressions from root: "
                                 mapM_ (putStrLn . showExpr) exprs
                                 putStrLn "\nexpressions from each e-class: "
                                 mapM_ (putStrLn . showExpr) exprs'
                                 putStrLn "heights: "
                                 mapM_ print h -- (print . _height) (IM.elems $ _eClass eg')
                                 putStrLn "values: "
                                 mapM_ print v -- (print . _consts . _info) (IM.elems $ _eClass eg')
                                 putStrLn "costs: "
                                 mapM_ print c -- (print . _cost . _info) (IM.elems $ _eClass eg')
        nPop = 10000
        hp = HP 3 7 100 nPop 2 1.0 0.25 terms nonterms
        p  = RT.P [0] (-3, 3) (-3, 3) []
    egraphRun `evalStateT` emptyGraph
    g <- getStdGen
    pop <- evalStateT (initialPop hp) g
    mapM_ (\nP -> putStr "pop " >> print nP >> calcRedundancy nP >> putStrLn "") [100, 200, 500, 1000, 5000, 10000, 20000, 100000]
