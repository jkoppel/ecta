module PathsSpec ( spec ) where

import Data.List ( nub, sort )
import qualified Data.Vector as Vector

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Internal.Paths

import Debug.Trace

-----------------------------------------------------------------

data PathTrieCommand = PathTrieAscend  Int
                     | PathTrieDescend Int
  deriving ( Show )

instance Arbitrary PathTrieCommand where
  arbitrary = do b <- arbitrary
                 i <- chooseInt (0, 5)
                 return $ if b then PathTrieAscend i else PathTrieDescend i
  shrink _ = []

invertPathTrieCommand :: PathTrieCommand -> PathTrieCommand
invertPathTrieCommand (PathTrieAscend i)  = PathTrieDescend i
invertPathTrieCommand (PathTrieDescend i) = PathTrieAscend  i

-- | A variant of pathTrieDescend that allows for descending out of bounds.
--   Makes the "descend/ascend are inverses" property easy to write
extendedPathTrieDescend :: PathTrieZipper -> Int -> PathTrieZipper
extendedPathTrieDescend (PathTrieZipper (PathTrie v) z') i
                                | i >= Vector.length v     = PathTrieZipper EmptyPathTrie (PathTrieAt i (PathTrie v) z')
extendedPathTrieDescend z                                i = pathTrieDescend z i

applyPathTrieCommand :: PathTrieCommand -> PathTrieZipper -> PathTrieZipper
applyPathTrieCommand (PathTrieAscend  i) z = pathTrieAscend z i
applyPathTrieCommand (PathTrieDescend i) z = extendedPathTrieDescend z i

-----------------------------------
------ Random generation
-----------------------------------

instance Arbitrary Path where
  arbitrary = path <$> listOf (chooseInt (0, 5))
  shrink = map Path . shrink . unPath

-----------------------------------
------ Constructing test inputs
-----------------------------------

mkTestPaths1 :: [[Int]] -> [[Path]]
mkTestPaths1 = map (map (path . (:[])))

mkTestPathsN :: [[[Int]]] -> [[Path]]
mkTestPathsN = map (map path)

--------

spec :: Spec
spec = do
  describe "subpath checking" $ do
    it "empty path is always subpath" $
      property $ \p -> isSubpath EmptyPath p

    it "is subpath of concatenation" $
      property $ \xs ys -> isSubpath (path xs) (path $ xs ++ ys)

    it "non-empty concatenation is not subpath of orig" $
      property $ \xs ys -> ys /= [] ==> not $ isSubpath (path $ xs ++ ys) (path xs)

    it "empty path is strict subpath of nonempty" $
      property $ \p -> p /= EmptyPath ==> isStrictSubpath EmptyPath p

    it "nothing is strict subpath of itself" $
      property $ \p -> not $ isStrictSubpath p p

  describe "substSubpath" $ do
    it "replaces prefix" $
      property $ \xs ys zs -> substSubpath (path zs) (path ys) (path $ ys ++ xs) `shouldBe` path (zs ++ xs)

  describe "path tries and zippers" $ do
    it "toPathTrie and fromPathTrie are inverses; fromPathTrie also sorts" $ do
      property $ \ps -> not (isContradicting [ps]) ==> fromPathTrie (toPathTrie $ nub ps) == (sort $ nub ps)

    it "ascending a zipper well beyond the root == adding ints to a path" $ do
      forAll (listOf (chooseInt (0, 5))) $ \ns -> fromPathTrie (zipperCurPathTrie $ foldr (flip pathTrieAscend) (pathTrieToZipper $ toPathTrie [EmptyPath]) ns) == [path ns]

    it "a sequence of path trie ascends/descends followed by its reverse yields the identity" $ do
      property $ \actions ps -> not (isContradicting [ps]) ==>
                                  (zipperCurPathTrie $ foldr applyPathTrieCommand (pathTrieToZipper $ toPathTrie $ nub ps) (reverse (map invertPathTrieCommand actions) ++ actions))
                                  == (toPathTrie $ nub ps)

  describe "mkEqConstraints" $ do
    it "removes unitary" $
      property $ \ps -> mkEqConstraints (map (:[]) ps) == EmptyConstraints

    it "removes empty" $
      property $ \n -> mkEqConstraints (replicate n []) == EmptyConstraints

    it "completes equalities" $
      mkEqConstraints (mkTestPaths1 [[1,2], [2,3], [4,5], [6,7], [7,1]]) `shouldBe` rawMkEqConstraints (normalizeEclasses $ mkTestPaths1 [[1,2,3,6,7], [4,5]])

    it "adds congruences" $
      mkEqConstraints (mkTestPathsN [[[0],[1]], [[2], [0]], [[0, 0], [0, 1]]]) `shouldBe` rawMkEqConstraints (normalizeEclasses $ (mkTestPathsN [[[0],[1],[2]], [[0, 0], [0, 1], [1, 0], [1,1], [2,0], [2,1]]]))

    it "detects contradictions from congruences" $
      -- This test input is from unifying `(a -> b) -> (a -> b)` and `(a -> (a -> a)) -> (a -> ([a] -> a))`
      constraintsAreContradictory (mkEqConstraints $ mkTestPathsN [ [[1, 1], [2,1]]
                                                                  , [[1, 1], [1, 2, 1], [1,2, 2], [2, 1], [2, 2, 1, 0], [2, 2, 2]]
                                                                  , [[1, 2], [2, 2]]
                                                                  ])
        `shouldBe` True

  -- | TODO: (6/23/21) QuickCheck generates very large lists, much larger than currently seen in actual inputs.
  -- mkEqConstraints contains a very inefficient addCongruences implementation. Therefore, these run too slowly.
  {-
  describe "constraintsImply" $ do
    modifyMaxSuccess (const 2) $
      it "Implies removed constraints" $
        property $ \cs1 cs2 -> length (concat cs1) < 300 && length (concat cs2) < 300
                               ==> constraintsImply (mkEqConstraints $ cs1 ++ cs2) (mkEqConstraints cs1)


    modifyMaxSuccess (const 2) $
      it "Does not imply added constraints" $
        property $ \cs1 cs2 -> length (concat cs1) < 300 && length (concat cs2) < 300
                               ==> let ecs1 = mkEqConstraints $ cs1 ++ cs2
                                       ecs2 = mkEqConstraints cs1
                                   in ecs1 /= ecs2 ==> not (constraintsImply ecs2 ecs1)
   -}

