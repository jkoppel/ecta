{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
module Main where

import QuickSpectacle
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Dynamic (dynTypeRep)
import Application.TermSearch.Type (TypeSkeleton(..), AblationType (Default))
import Data.Text (Text)
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
    [ con "return" (return :: A -> [A])
    , con "(>>=)" ((>>=) :: [A] -> (A -> [A]) -> [A])
    , con "xs" ([] :: [A])
    , con "x" (A undefined :: A)
    ]

sigList :: Sig -> [(Text, TypeSkeleton)]
sigList sig = Map.toList $ Map.map (typeRepToTypeSkeleton . dynTypeRep) sig

tk :: Node -> Int -> [Node]
tk _ 0 = []
tk anyArg 1 = [anyArg]
tk anyArg n = [union $ mapp (union nl1) anyArg:nl1]
 where nl1 = tk anyArg (n-1)

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




main :: IO ()
main = do
          let argNodes =  map (Bi.bimap Symbol typeToFta) $ sigList sig
              anyArg = Node $
                 map (\(s,t) -> Edge (Symbol s) [typeToFta t]) $ sigList sig
          let t = typeRepToTypeSkeleton (someTypeRep (Proxy :: Proxy [A]))
              resNode = typeToFta t
              -- !filterNode = filterType () resNode
            --   tk = relevantTermsUptoK anyArg [] 6
          print resNode
          print $ sigList sig
          print argNodes
          print anyArg
          print $ mapp anyArg anyArg
          mapM_ (print . prettyTerm ) $
            concatMap (getAllTerms . refold . reduceFully . flip filterType resNode ) (tk anyArg 4)
          --mapM_ (print  ) $ (getAllTerms  ) $ app 0 anyArg anyArg
