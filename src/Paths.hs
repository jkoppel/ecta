module Paths (
    -- * Paths
    Path(EmptyPath, ConsPath)
  , unPath
  , path
  , Pathable(..)
  , pathHeadUnsafe
  , pathTailUnsafe
  , isSubpath

  , PathTrie
  , PathTrieZipper
  , toPathTrie
  , fromPathTrie
  , pathTrieToZipper
  , zipperCurPathTrie
  , pathTrieDescend
  , pathTrieAscend

  , PathEClass
  , unPathEClass
  , hasSubsumingMember
  , completedSubsumptionOrdering

    -- * Equality constraints over paths
  , EqConstraints(EmptyConstraints)
  , unsafeGetEclasses
  , mkEqConstraints
  , combineEqConstraints
  , constraintsAreContradictory
  , constraintsImply
  , subsumptionOrderedEclasses
  , unsafeSubsumptionOrderedEclasses
  ) where

import Internal.Paths