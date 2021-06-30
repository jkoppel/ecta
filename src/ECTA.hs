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
  , union
  , intersect
  , denotation

  , reducePartially

  -- * Visualization / debugging
  , toDot
  , refreshNode
  , refreshEdge
  ) where

import Internal.ECTA