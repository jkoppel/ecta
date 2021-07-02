{-# LANGUAGE CPP #-}

-- | Equality-constrained deterministic finite tree automata
--
-- Specialized to DAGs, plus at most one globally unique recursive node

module ECTA (
    Symbol(Symbol)
  , Term(..)
  , Edge(Edge)
  , mkEdge
  , edgeChildren
  , Node(Node, EmptyNode)
  , nodeEdges
  , createGloballyUniqueMu

  -- * Operations
  , pathsMatching
  , mapNodes
  , refold
  , unfoldBounded
  , crush
  , nodeCount
  , edgeCount
  , maxIndegree
  , union
  , intersect
  , denotation

  , reducePartially

  -- * Visualization / debugging
  , toDot

#ifdef PROFILE_CACHES
  , resetAllEctaCaches_BrokenDoNotUse
#endif
  ) where

import Internal.ECTA