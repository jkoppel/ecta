{-# LANGUAGE OverloadedStrings #-}

module ECTASpec ( spec ) where

import Control.Monad ( replicateM )
import qualified Data.HashSet as HashSet
import Data.HashSet ( HashSet )
import Data.List ( and, subsequences, (\\) )
import qualified Data.Text as Text

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Internal.ECTA
import Internal.Paths
import TermSearch

-----------------------------------------------------------------


constTerms :: [Symbol] -> Node
constTerms ss = Node (map (\s -> Edge s []) ss)

ex1 :: Node
ex1 = Node [mkEdge "f" [constTerms ["1", "2"], Node [Edge "g" [constTerms ["1", "2"]]]] (mkEqConstraints [[path [0], path [1,0]]])]

ex2 :: Node
ex2 = Node [mkEdge "f" [constTerms ["1", "2", "3"], Node [Edge "g" [constTerms ["1", "2", "4"]]]] (mkEqConstraints [[path [0], path [1,0]]])]

ex3 :: Node
ex3 = Node [Edge "f" [Node [Edge "g" [constTerms ["1", "2"]]]], Edge "h" [Node [Edge "i" [constTerms ["3", "4"]]]]]

ex3_root_doubled :: Node
ex3_root_doubled = Node [Edge "ff" [Node [Edge "g" [constTerms ["1", "2"]]]], Edge "hh" [Node [Edge "i" [constTerms ["3", "4"]]]]]

ex3_doubled :: Node
ex3_doubled = Node [Edge "f" [Node [Edge "g" [constTerms ["11", "22"]]]], Edge "h" [Node [Edge "i" [constTerms ["33", "44"]]]]]

doubleNodeSymbols :: Node -> Node
doubleNodeSymbols (Node es) = Node $ map doubleEdgeSymbol es
  where
    doubleEdgeSymbol :: Edge -> Edge
    doubleEdgeSymbol (Edge (Symbol s) ns) = Edge (Symbol (Text.append s s)) ns

testBigNode :: Node
testBigNode = uptoDepth4

testUnreducedConstraint :: Edge
testUnreducedConstraint = mkEdge "foo" [Node [Edge "A" [], Edge "B" []], Node [Edge "B" [], Edge "C" []]] (mkEqConstraints [[path [0], path [1]]])

bug062721NonIdempotentEqConstraintReduction :: (EqConstraints, [Node])
bug062721NonIdempotentEqConstraintReduction =
  ( EqConstraints {getEclasses = [PathEClass [Path [0],Path [2,0,2]],PathEClass [Path [1],Path [2,0,0]],PathEClass [Path [2,0,1],Path [3,0]]]}
  , [(Node [(Edge "baseType" [])]),(Node [(Edge "(->)" [])]),(Node [(mkEdge "app" [(Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))]),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])]),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "(->)" [])]),(Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "baseType" [])]),(Node [(Edge "baseType" [])])])])]),(Edge "x" [(Node [(Edge "baseType" [])])]),(Edge "n" [(Node [(Edge "Int" [])])]),(Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,1]],PathEClass [Path [1,2],Path [2,2]]]})])]),(Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Int" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [2,1],Path [2,2,0]]]})])]),(Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,2,1,0]],PathEClass [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]]})])])]),(Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "baseType" [])]),(Node [(Edge "baseType" [])])])])]),(Edge "x" [(Node [(Edge "baseType" [])])]),(Edge "n" [(Node [(Edge "Int" [])])]),(Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,1]],PathEClass [Path [1,2],Path [2,2]]]})])]),(Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Int" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [2,1],Path [2,2,0]]]})])]),(Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,2,1,0]],PathEClass [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]]})])])])] EqConstraints {getEclasses = [PathEClass [Path [0],Path [2,0,2]],PathEClass [Path [1],Path [2,0,0]],PathEClass [Path [2,0,1],Path [3,0]]]})]),(Node [(mkEdge "app" [(Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))]),(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))]),(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))]),(Edge "Maybe" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "(->)" [])]),(Node [(mkEdge "app" [(Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))]),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])]),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "(->)" [])]),(Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "baseType" [])]),(Node [(Edge "baseType" [])])])])]),(Edge "x" [(Node [(Edge "baseType" [])])]),(Edge "n" [(Node [(Edge "Int" [])])]),(Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,1]],PathEClass [Path [1,2],Path [2,2]]]})])]),(Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Int" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [2,1],Path [2,2,0]]]})])]),(Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,2,1,0]],PathEClass [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]]})])])]),(Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "baseType" [])]),(Node [(Edge "baseType" [])])])])]),(Edge "x" [(Node [(Edge "baseType" [])])]),(Edge "n" [(Node [(Edge "Int" [])])]),(Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,1]],PathEClass [Path [1,2],Path [2,2]]]})])]),(Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Int" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [2,1],Path [2,2,0]]]})])]),(Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,2,1,0]],PathEClass [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]]})])])])] EqConstraints {getEclasses = [PathEClass [Path [0],Path [2,0,2]],PathEClass [Path [1],Path [2,0,0]],PathEClass [Path [2,0,1],Path [3,0]]]})]),(Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "baseType" [])]),(Node [(Edge "baseType" [])])])])]),(Edge "x" [(Node [(Edge "baseType" [])])]),(Edge "n" [(Node [(Edge "Int" [])])]),(Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,1]],PathEClass [Path [1,2],Path [2,2]]]})])]),(Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Int" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [2,1],Path [2,2,0]]]})])]),(Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,2,1,0]],PathEClass [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]]})])])])] EqConstraints {getEclasses = [PathEClass [Path [0],Path [2,0,2]],PathEClass [Path [1],Path [2,0,0]],PathEClass [Path [2,0,1],Path [3,0]]]}),(mkEdge "app" [(Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))]),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])]),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "(->)" [])]),(Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "baseType" [])]),(Node [(Edge "baseType" [])])])])]),(Edge "x" [(Node [(Edge "baseType" [])])]),(Edge "n" [(Node [(Edge "Int" [])])]),(Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,1]],PathEClass [Path [1,2],Path [2,2]]]})])]),(Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Int" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [2,1],Path [2,2,0]]]})])]),(Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,2,1,0]],PathEClass [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]]})])])]),(Node [(mkEdge "app" [(Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))]),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])]),(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "(->)" [])]),(Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "baseType" [])]),(Node [(Edge "baseType" [])])])])]),(Edge "x" [(Node [(Edge "baseType" [])])]),(Edge "n" [(Node [(Edge "Int" [])])]),(Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,1]],PathEClass [Path [1,2],Path [2,2]]]})])]),(Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Int" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [2,1],Path [2,2,0]]]})])]),(Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,2,1,0]],PathEClass [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]]})])])]),(Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "baseType" [])]),(Node [(Edge "baseType" [])])])])]),(Edge "x" [(Node [(Edge "baseType" [])])]),(Edge "n" [(Node [(Edge "Int" [])])]),(Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,1]],PathEClass [Path [1,2],Path [2,2]]]})])]),(Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Int" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [2,1],Path [2,2,0]]]})])]),(Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])])),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])]),(Mu (Node [(Edge "baseType" []),(Edge "->" [(Node [(Edge "(->)" [])]),Rec,Rec]),(Edge "Maybe" [Rec]),(Edge "List" [Rec])]))])])])])] EqConstraints {getEclasses = [PathEClass [Path [1,1],Path [2,2,1,0]],PathEClass [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]]})])])])] EqConstraints {getEclasses = [PathEClass [Path [0],Path [2,0,2]],PathEClass [Path [1],Path [2,0,0]],PathEClass [Path [2,0,1],Path [3,0]]]})])] EqConstraints {getEclasses = [PathEClass [Path [0],Path [2,0,2]],PathEClass [Path [1],Path [2,0,0]],PathEClass [Path [2,0,1],Path [3,0]]]})])]
  )

bug062721NonIdempotentEqConstraintReductionGen :: Gen [Node]
bug062721NonIdempotentEqConstraintReductionGen = return $ snd bug062721NonIdempotentEqConstraintReduction

infiniteLineNode :: Node
infiniteLineNode = Mu (Node [Edge "f" [Rec]])

--------------------------------------------------------------
-------------------- QuickCheck Instances --------------------
--------------------------------------------------------------

-- Cap size at 3 whenever you will generate all denotations
_MAX_NODE_DEPTH = 5

capSize :: Int -> Gen a -> Gen a
capSize max g = sized $ \n -> if n > max then
                                resize max g
                              else
                                g

instance Arbitrary Node where
  arbitrary = capSize _MAX_NODE_DEPTH $ sized $ \n -> do
    k <- chooseInt (1, 3)
    Node <$> replicateM k arbitrary

  shrink EmptyNode = []
  shrink (Node es) = [Node es' | seq <- subsequences es \\ [es], es' <- mapM shrink seq] ++ concatMap (\e -> edgeChildren e) es
  shrink (Mu _)    = []
  shrink Rec       = []


testEdgeTypes :: [(Symbol, Int)]
testEdgeTypes = [ ("f", 1)
                , ("g", 2)
                , ("h", 1)
                , ("w", 3)
                , ("a", 0)
                , ("b", 0)
                , ("c", 0)
                ]

testConstants :: [Symbol]
testConstants = map fst $ filter ((== 0) . snd) testEdgeTypes

randPathPair :: [Node] -> Gen [Path]
randPathPair ns = do p1 <- randPath ns
                     p2 <- randPath ns
                     return [p1, p2]

randPath :: [Node] -> Gen Path
randPath [] = return EmptyPath
randPath ns = do i <- chooseInt (0, length ns - 1)
                 let Node es = ns !! i
                 ns' <- edgeChildren <$> elements es
                 b <- arbitrary
                 if b then return (path [i]) else ConsPath i <$> randPath ns'

instance Arbitrary Edge where
  arbitrary =
    sized $ \n -> case n of
                   0 -> Edge <$> elements testConstants <*> pure []
                   _ -> do (sym, arity) <- elements testEdgeTypes
                           ns <- replicateM arity (resize (n-1) (arbitrary `suchThat` (/= EmptyNode)))
                           numConstraintPairs <- elements [0,0,1,1,2,3]
                           ps <- replicateM numConstraintPairs (randPathPair ns)
                           return $ mkEdge sym ns (mkEqConstraints ps)

  shrink e = mkEdge (edgeSymbol e) <$> (mapM shrink (edgeChildren e)) <*> pure (edgeEcs e)


dropEqConstraints :: Node -> Node
dropEqConstraints = mapNodes go
  where
    go :: Node -> Node
    go (Node es) = Node (map dropEc es)

    dropEc :: Edge -> Edge
    dropEc (Edge s ns) = Edge s ns


--------------------------------------------------------------
----------------------------- Main ---------------------------
--------------------------------------------------------------


spec :: Spec
spec = do
  describe "Pathable" $ do
    it "Node.getPath root" $
      getPath (path []) testBigNode `shouldBe` testBigNode

    it "Node.getPath one-level" $
      getPath (path [0]) ex1 `shouldBe` (constTerms ["1", "2"])

    it "Node.getPath merges multiple branches" $
      getPath (path [0,0]) ex3 `shouldBe` (constTerms ["1", "2", "3", "4"])

    it "Node.modifyAtPath modifies at root" $
      modifyAtPath doubleNodeSymbols (path []) ex3 `shouldBe` ex3_root_doubled

    it "Node.modifyAtPath modifies at path" $
      modifyAtPath doubleNodeSymbols (path [0,0]) ex3 `shouldBe` ex3_doubled

  describe "ECDFTA-nodes" $ do
    it "equality constraints constrain" $
        denotation ex1 `shouldSatisfy` ((== 2) . length)

    it "reduces paths constrained by equality constraints" $
        reducePartially ex2 `shouldBe` reducePartially ex1

    it "has already performed all normalizations" $
        refreshNode testBigNode `shouldBe` testBigNode

  describe "intersection" $ do
    it "intersection commutes with denotation" $
      property $ mapSize (min 3) $ \n1 n2 -> HashSet.fromList (denotation $ intersect n1 n2)
                                               `shouldBe` HashSet.intersection (HashSet.fromList $ denotation n1)
                                                                               (HashSet.fromList $ denotation n2)

  describe "reduction" $ do
    it "reduction preserves denotation" $
      property $ mapSize (min 3) $ \n -> HashSet.fromList (denotation n) `shouldBe` HashSet.fromList (denotation $ reducePartially n)

    it "reducing a single constraint is idempotent 1" $
      property $ \e -> let ns  = edgeChildren e
                           ecs = edgeEcs e
                           ns' = reduceEqConstraints ecs ns
                       in  ns' == reduceEqConstraints ecs ns'

    it "reducing a single constraint is idempotent 2" $
      property $ \e1 e2 -> let maybeE'  = intersectEdge e1 e2
                           in (maybeE' /= Nothing) ==>
                                 let Just e' = maybeE'
                                     ns  = edgeChildren e'
                                     ecs = edgeEcs e'
                                     ns' = reduceEqConstraints ecs ns
                                 in  ns' == reduceEqConstraints ecs ns'

    -- | TODO (6/29/21): Need a better way to visualize the type nodes.
    --   Reversing the order that eclasses are processed seems to make no difference.
    {-
    it "reducing a constraint is idempotent: buggy input 6/27/21" $
      forAllShrink bug062721NonIdempotentEqConstraintReductionGen shrink
                                                                   (\ns -> let ecs = fst bug062721NonIdempotentEqConstraintReduction
                                                                               ns' = reduceEqConstraints ecs ns
                                                                           in ns' == reduceEqConstraints ecs ns')
     -}

    -- | TODO: I've become less convinced this can actually be done in one pass. But this test passes.
    it "leaf reduction means, for everything at a path, there is something matching at the other paths" $
      property $ \e -> let e' = reduceEdgeIntersection e
                           ns = edgeChildren e' in
                      (e' /= emptyEdge && edgeEcs e' /= EmptyConstraints) ==>
                         and [intersect n1 n2 /= EmptyNode | ec <- unsafeGetEclasses (edgeEcs e')
                                                           , p1 <- unPathEClass ec
                                                           , p2 <- unPathEClass ec
                                                           , n1 <- getAllAtPath p1 ns
                                                           , let n2 = getPath p2 ns]

    it "recursive terms are unrolled to the depth of the constraints and no more" $
      let ecs  = (mkEqConstraints [[path [0,0,0,0], path [1,0,0]]])
          ns   = [infiniteLineNode, infiniteLineNode]
          ns'  = reduceEqConstraints ecs ns
          ns'' = reduceEqConstraints ecs ns'
          f    = \n -> Node [Edge "f" [n]]
      in (ns' == ns'') && ns' == [f $ f $ f $ f infiniteLineNode, f $ f $ f $ infiniteLineNode]
         `shouldBe` True
