{-# LANGUAGE OverloadedStrings #-}

module DbSpec ( spec ) where

import Data.Maybe
import Test.Hspec

import ECTA
import Paths

import DbOpt

spec :: Spec
spec = do
  describe "staging constraints" $ do
    it "relation" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ relationT "test") `shouldBe` False
    it "scalar" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (scalarT (nameT "test"))) `shouldBe` True
    it "scalar-param" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (scalarT (paramT "test"))) `shouldBe` False
    it "filter" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (filterT (nameT "test") $ scalarT (nameT "test"))) `shouldBe` True
    it "filter-eq" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (filterT (eqT (nameT "test") (nameT "test")) $ scalarT (nameT "test"))) `shouldBe` True
    it "filter-eq-param" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (filterT (eqT (nameT "test") (paramT "test")) $ scalarT (nameT "test"))) `shouldBe` True
    it "list" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (listT (relationT "test") $ scalarT (nameT "test"))) `shouldBe` True
    it "list-param" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (listT (paramT "test") $ scalarT (nameT "test"))) `shouldBe` False
    it "hidx" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (hidxT (relationT "test") (scalarT (nameT "test")) (paramT "x"))) `shouldBe` True
    it "hidx-bad-key" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (hidxT (relationT "test") (scalarT (nameT "test")) (relationT "x"))) `shouldBe` False
    it "hidx" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (hidxT (selectT (nameT "k") (scalarT $ relationT "r")) (filterT (eqT (nameT "k") (cscopeT `dotT` (nameT "k"))) (scalarT $ relationT "r")) (paramT "p"))) `shouldBe` False
    it "depjoin" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (depjoinT (relationT "test") (paramT "test"))) `shouldBe` False
    it "depjoin" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (depjoinT (paramT "test") (relationT "test"))) `shouldBe` False
    it "depjoin" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (depjoinT (paramT "test") (paramT "test"))) `shouldBe` True
    it "tuple" $
      (containsConstr $ reducePartially $ liftClosedPat $ rtimeConstr $ (tupleT [(scalarT $ nameT "test")])) `shouldBe` True
    it "tuple" $
      (containsConstr $ reducePartially $ fromJust $ rewriteFirst introList $ liftClosedPat $ rtimeConstr $ (relationT "lineitem")) `shouldBe` True
    it "tuple" $
      (containsConstr $ reducePartially $ fromJust $ rewriteAll introList $ fromJust $ rewriteFirst filterToHidx $ liftClosedPat $ rtimeConstr $ (filterT (eqT (nameT "o_orderdate") (paramT "param1")) (relationT "orders"))) `shouldBe` True
    it "tuple" $
      (containsConstr $ reducePartially $ fromJust $ rewriteAll introList $ fromJust $ rewriteFirst filterToOidx1 $ liftClosedPat $ rtimeConstr $ (filterT (ltT (nameT "o_orderdate") (paramT "param1")) (relationT "orders"))) `shouldBe` True
