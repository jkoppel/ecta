module Paths (
    -- * Paths
    Path(EmptyPath, ConsPath)
  , path
  , Pathable(..)
  , pathHeadUnsafe
  , pathTailUnsafe
  , isSubpath

  , PathEClass(..)
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