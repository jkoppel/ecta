{-# LANGUAGE OverloadedStrings #-}

module ECTASpec ( spec ) where

import qualified Data.HashSet as HashSet
import Data.HashSet ( HashSet )
import Data.IORef ( newIORef, readIORef, modifyIORef )
import Data.List ( and, nub, sort )
import Data.Semigroup ( Max(..) )
import qualified Data.Text as Text

import System.IO.Unsafe ( unsafePerformIO )

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Data.ECTA
import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Term
import TermSearch

import Test.Generators.ECTA

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

-- | This is an ECTA for which the naive static reduction algorithm does not terminate
replicator :: Node
replicator = Node [mkEdge "g" [basicNode, basicNode] constraint]
  where
    basicNode = Node [mkEdge "g" [muNode, muNode] constraint]
    constraint = mkEqConstraints [[path [1], path [0, 1], path [0, 0]]]
    muNode = Mu (Node [Edge "g" [Rec, Rec]])

--------------------------------------------------------------
----------------------------- Main ---------------------------
--------------------------------------------------------------


spec :: Spec
spec = do
  describe "Pathable" $ do
    it "Node.getPath root" $
      property $ \(n :: Node) -> getPath (path []) n `shouldBe` n

    it "Node.getPath one-level" $
      getPath (path [0]) ex1 `shouldBe` (constTerms ["1", "2"])

    it "Node.getPath merges multiple branches" $
      getPath (path [0,0]) ex3 `shouldBe` (constTerms ["1", "2", "3", "4"])

    it "Node.modifyAtPath modifies at root" $
      modifyAtPath doubleNodeSymbols (path []) ex3 `shouldBe` ex3_root_doubled

    it "Node.modifyAtPath modifies at path" $
      modifyAtPath doubleNodeSymbols (path [0,0]) ex3 `shouldBe` ex3_doubled

  describe "ECTA-nodes" $ do
    it "equality constraints constrain" $
        naiveDenotation ex1 `shouldSatisfy` ((== 2) . length)

    it "reduces paths constrained by equality constraints" $
        reducePartially ex2 `shouldBe` reducePartially ex1

  describe "intersection" $ do
    it "intersection commutes with naiveDenotation" $
      property $ mapSize (min 3) $ \n1 n2 -> HashSet.fromList (naiveDenotation $ intersect n1 n2)
                                               `shouldBe` HashSet.intersection (HashSet.fromList $ naiveDenotation n1)
                                                                               (HashSet.fromList $ naiveDenotation n2)

    it "intersect is associative" $
      property $ \n1 n2 n3 -> ((n1 `intersect` n2) `intersect` n3) == (n1 `intersect` (n2 `intersect` n3))

    it "intersect is commutative" $
      property $ \n1 n2 -> intersect n1 n2 == intersect n2 n1

    it "intersect distributes over union" $
      property $ \n1 n2 n3 -> intersect n1 (union [n2, n3]) == union [intersect n1 n2, intersect n1 n3]

    it "intersect is idempotent" $
      property $ \n1 -> intersect n1 n1 == n1

  describe "reduction" $ do
    it "reduction preserves naiveDenotation" $
      property $ mapSize (min 3) $ \n -> HashSet.fromList (naiveDenotation n) `shouldBe` HashSet.fromList (naiveDenotation $ reducePartially n)

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

    -- | TODO (6/29/21): Need a better way to visualize the type nodes. Cannot figure out why this fails.
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


  describe "folding" $
    it "refold folds the simplest unrolled input" $
      refold (Node [Edge "f" [infiniteLineNode]]) `shouldBe` infiniteLineNode

  describe "traversals" $ do
    it "mapNodes hits each node exactly once" $
      -- Note: If the Arbitrary Node instance is changed to return empty or mu nodes, this will need to change
      property $ \n -> unsafePerformIO $ do v <- newIORef 0
                                            let n' = mapNodes (\m -> unsafePerformIO (modifyIORef v (+1) >> pure m)) n
                                            let k = nodeCount n'
                                            numInvocations <- k `seq` readIORef v
                                            return $ k == numInvocations

    it "adding node above 1 node increases depth by 1" $
      property $ \n -> n /= EmptyNode ==>
                          1 + depth n == depth (Node [Edge "f" [n]])

    it "adding node above 3 nodes increases max depth by 1" $
      property $ \n1 n2 n3 -> all (/= EmptyNode) [n1, n2, n3] ==>
                                (1 + getMax (foldMap (Max . depth) [n1, n2, n3])) == depth (Node [Edge "w" [n1, n2, n3]])


  describe "enumeration" $ do
    it "naive and sophisticated enumeration are equivalent on nodes without mu" $
      property $ mapSize (min 3) $
        \n -> HashSet.fromList (naiveDenotation n) `shouldBe` HashSet.fromList (getAllTerms $ reducePartially n)