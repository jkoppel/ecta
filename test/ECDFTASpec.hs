{-# LANGUAGE OverloadedStrings #-}

module ECDFTASpec ( spec ) where


import Test.Hspec

import ECDFTA
import TermSearch

-----------------------------------------------------------------


constTerms :: [Symbol] -> Node
constTerms ss = Node (map (\s -> Edge s [] []) ss)

ex1 :: Node
ex1 = Node [Edge "f" [constTerms ["1", "2"], Node [Edge "g" [constTerms ["1", "2"]] []]] [EqConstraint (path [0]) (path [1,0])]]

ex2 :: Node
ex2 = Node [Edge "f" [constTerms ["1", "2", "3"], Node [Edge "g" [constTerms ["1", "2", "4"]] []]] [EqConstraint (path [0]) (path [1,0])]]

testBigNode :: Node
testBigNode = uptoDepth4

--------------------------
------ Main
--------------------------


spec :: Spec
spec = do
  describe "ECDFTA-nodes" $ do
    it "equality constraints constrain" $
        denotation ex1 `shouldSatisfy` ((== 2) . length)

    it "reduces paths constrained by equality constraints" $
        ex1 `shouldBe` ex2

    it "has already performed all normalizations" $
        refreshNode testBigNode `shouldBe` testBigNode
