{-# LANGUAGE CPP #-}

-- | Equality-constrained deterministic finite tree automata
--
-- Specialized to DAGs, plus at most one globally unique recursive node

module Data.ECTA (
    Edge(Edge)
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
  , onNormalNodes
  , nodeCount
  , edgeCount
  , maxIndegree
  , union
  , intersect
  , naiveDenotation

  , withoutRedundantEdges
  , reducePartially

  -- * Visualization / debugging
  , toDot

#ifdef PROFILE_CACHES
  , resetAllEctaCaches_BrokenDoNotUse
#endif
  ) where

import Data.ECTA.Internal.ECTA