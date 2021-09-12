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
  , pathTrieAscend
  , pathTrieDepth

  , PathEClass(getPathTrie)
  , unPathEClass
  , hasSubsumingMember
  , completedSubsumptionOrdering
  , pecDepth

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

import Data.ECTA.Internal.Paths