{-# LANGUAGE OverloadedStrings #-}

module ECDFTASpec ( spec ) where

import Control.Monad ( replicateM )
import qualified Data.HashSet as HashSet
import Data.HashSet ( HashSet )
import Data.List ( subsequences, (\\) )
import qualified Data.Text as Text

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

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
  shrink (Node es) = map Node (subsequences es \\ [es]) ++ concatMap (\(Edge _ ns) -> ns) es


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
                           numConstraintPairs <- elements [0,0,0,0,1,1,2,3]
                           ps <- replicateM numConstraintPairs (randPathPair ns)
                           return $ mkEdge sym ns (mkEqConstraints ps)


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
