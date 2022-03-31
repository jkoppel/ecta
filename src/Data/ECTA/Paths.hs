module Data.ECTA.Paths (
    -- * Paths
    Path(EmptyPath, ConsPath)
  , unPath
  , path
  , Pathable(..)
  , pathHeadUnsafe
  , pathTailUnsafe
  , isSubpath

  , PathTrie(TerminalPathTrie)
  , isEmptyPathTrie
  , isTerminalPathTrie
  , getMaxNonemptyIndex
  , toPathTrie
  , fromPathTrie
  , pathTrieDescend

  , PathEClass(getPathTrie)
  , unPathEClass
  , hasSubsumingMember
  , completedSubsumptionOrdering

    -- * Equality constraints over paths
  , EqConstraints(EmptyConstraints)
  , unsafeGetEclasses
  , mkEqConstraints
  , combineEqConstraints
  , eqConstraintsDescend
  , constraintsAreContradictory
  , constraintsImply
  , subsumptionOrderedEclasses
  , unsafeSubsumptionOrderedEclasses
  ) where

import Data.ECTA.Internal.Paths


import Data.Function ( on )
import Data.Hashable ( Hashable )
import Data.List ( isSubsequenceOf, nub, sort, sortBy, subsequences, (\\) )
import Data.Monoid ( Any(..) )
import Data.Semigroup ( Max(..) )
import qualified Data.Text as Text
import           Data.Vector ( Vector )
import qualified Data.Vector as Vector
import Data.Vector.Instances ()
import GHC.Exts ( inline )
import GHC.Generics ( Generic )

import Data.Equivalence.Monad ( runEquivM, equate, desc, classes )

import Data.Memoization ( MemoCacheTag(..), memo2 )
import Data.Text.Extended.Pretty
import Utility.Fixpoint


import QuickSpec
import Test.QuickCheck hiding ( classes )

---------------------------------------------------------
------------ Playing with QuickSpec ---------------------
---------------------------------------------------------


sig = [
    con "isSubpath"       isSubpath
  , con "isStrictSubpath" isStrictSubpath
  , con "EmptyPath"       EmptyPath
  , con "path"            path
  , con "++I"             ((++) :: [Int] -> [Int] -> [Int])
  , con "++P"             ((++) :: [Path] -> [Path] -> [Path])
  , con "++[P]"           ((++) :: [[Path]] -> [[Path]] -> [[Path]])
  , con "True"            True
  ]

{-
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

  describe "path tries" $ do
    it "fromPathTrie and toPathTrie are inverses" $ do
      property $ \pt -> toPathTrie (fromPathTrie pt) == pt

    it "comparing path trie is same as comparing list of paths" $ do
      property $ \ps1 ps2 -> not (isContradicting [ps1] || isContradicting [ps2])
                             ==> compare (toPathTrie $ nub ps1) (toPathTrie $ nub ps2)
                                   == compare (sort $ nub ps1) (sort $ nub ps2)

    it "unioning path trie same as unioning lists of paths, checking contradiction" $ do
      property $ \pt1 pt2 -> case unionPathTrie pt1 pt2 of
                               Nothing  -> isContradicting [fromPathTrie pt1 ++ fromPathTrie pt2]
                               Just pt' -> fromPathTrie pt' == (sort $ nub $ fromPathTrie pt1 ++ fromPathTrie pt2)

    it "PathTrie-based hasSubsumingMember same as list-based implementation" $ do
      property $ \pt1 pt2 -> let pec1 = PathEClass (fromPathTrie pt1)
                                 pec2 = PathEClass (fromPathTrie pt2)
                             in hasSubsumingMember pec1 pec2 == hasSubsumingMemberListBased (unPathEClass pec1) (unPathEClass pec2)



  describe "path trie zipper" $ do
    it "smallestNonempty works" $ do
      smallestNonempty (Vector.fromList [EmptyPathTrie, EmptyPathTrie, TerminalPathTrie, TerminalPathTrie, EmptyPathTrie]) `shouldBe` 2

    it "largestNonempty works" $ do
      largestNonempty  (Vector.fromList [EmptyPathTrie, EmptyPathTrie, TerminalPathTrie, TerminalPathTrie, EmptyPathTrie]) `shouldBe` 3

    it "ascending a zipper well beyond the root == adding ints to a path" $ do
      forAll (listOf (chooseInt (0, 4))) $ \ns -> fromPathTrie (zipperCurPathTrie $ foldr (flip pathTrieZipperAscend) (pathTrieToZipper $ toPathTrie [EmptyPath]) ns) == [path ns]

    it "a sequence of path trie zipper ascends/descends followed by its reverse yields the identity" $ do
      property $ \actions pt -> (zipperCurPathTrie $ foldr applyPathTrieCommand (pathTrieToZipper pt) (reverse (map invertPathTrieCommand actions) ++ actions))
                                == pt

  describe "PathEClass" $ do
    it "both ways of getting list of paths from a PathEClass are identical" $ do
      property $ \pt -> fromPathTrie (getPathTrie (PathEClass (fromPathTrie pt))) == getOrigPaths (PathEClass (fromPathTrie pt))
-}
