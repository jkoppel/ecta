{-# LANGUAGE OverloadedStrings #-}

module ECDFTASpec ( spec ) where

import qualified Data.Text as Text

import Test.Hspec

import ECDFTA
import Paths
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

--------------------------
------ Main
--------------------------




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
