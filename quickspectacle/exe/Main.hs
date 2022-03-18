{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
module Main where

import QuickSpectacle
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Dynamic (dynTypeRep)
import Application.TermSearch.Type (TypeSkeleton(..), AblationType (Default))
import Data.Text (Text, unpack)
import qualified Data.Bifunctor as Bi
import Application.TermSearch.Dataset (typeToFta)
import Data.ECTA.Term (Symbol(..), Term (Term))
import Data.ECTA
import Application.TermSearch.TermSearch (constArg, reduceFullyAndLog, relevantTermsUptoK, filterType, generalize, prettyPrintAllTerms, parseHoogleComponent, anyEnv, prettyTerm, reduceFully, termsK, relevantTermK, useLambdaArgs, app, constructLambdaK, applyOperator, lambda)
import Data.Proxy (Proxy)
import Type.Reflection (someTypeRep)
import Data.Typeable (Proxy(Proxy))
import Application.TermSearch.Utils (theArrowNode, arrowType, var1, var2, var3, var4)
import Data.ECTA.Paths (mkEqConstraints, path, Pathable (getPath))



sig :: Sig
sig = mconcat
    [ con "return" (return :: Int -> [Int])
    , con "(>>=)" ((>>=) :: [Int] -> (Int -> [Int]) -> [Int])
    , con "xs" ([] :: [Int])
    , con "x" (0 :: Int)
    , con "f" (const [] :: Int -> [Int])
    ]

sigList :: Sig -> [(Text, TypeSkeleton)]
sigList sig = Map.toList $ Map.map (typeRepToTypeSkeleton . dynTypeRep) sig

tk :: Node -> Int -> [Node]
tk _ 0 = []
tk anyArg 1 = [anyArg]
tk anyArg n = [union [mapp nl1 nl1,nl1]]
 where nl1 = union $ tk anyArg (n-1)

mapp :: Node -> Node -> Node
mapp n1 n2 = Node [
    mkEdge "app"
    [getPath (path [0,2]) n1, theArrowNode, n1, n2]
    (mkEqConstraints [
          [path [1], path [2, 0, 0]] -- it's a function
        , [path [3, 0], path [2, 0, 1]]
        , [path [0], path [2,0,2]]
        ]
    )]


pp (Term (Symbol t) []) = t
pp (Term (Symbol "app") (arg:rest)) =
    "(" <> wparifreq <> " " <> mconcat (map pp rest) <> ")"
  where parg = pp arg
        wparifreq = if length (words $ unpack parg) > 1
                    then "(" <> parg <> ")"
                    else parg


main :: IO ()
main = do
          let argNodes =  map (Bi.bimap Symbol typeToFta) $ sigList sig
              anyArg = Node $
                 map (\(s,t) -> Edge (Symbol s) [typeToFta t]) $ sigList sig
          let t = typeRepToTypeSkeleton (someTypeRep (Proxy :: Proxy [Int]))
              resNode = typeToFta t
              -- !filterNode = filterType () resNode
            --   tk = relevantTermsUptoK anyArg [] 6
          print resNode
          print $ sigList sig
          print argNodes
          print anyArg
          print $ mapp anyArg anyArg
          mapM_ (putStrLn . unpack . pp . prettyTerm ) $
            concatMap (getAllTerms . refold . reduceFully . flip filterType resNode ) (tk anyArg 5)
