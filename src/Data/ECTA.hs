{-# LANGUAGE CPP #-}

-- | Equality-constrained deterministic finite tree automata
--
-- Specialized to DAGs, plus at most one globally unique recursive node

module Data.ECTA (
    Edge(Edge)
  , mkEdge
  , edgeChildren
  , edgeSymbol

  , Node(Node, EmptyNode)
  , nodeEdges
  , createGloballyUniqueMu

  -- * Operations
  , nodeMapChildren
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
  , withoutRedundantEdges
  , reducePartially

  -- * Enumeration
  , EnumerateM
  , runEnumerateM
  , enumerateFully
  , getAllTerms
  , getAllTruncatedTerms
  , naiveDenotation


  -- * Visualization / debugging
  , toDot
  ) where

import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.ECTA.Visualization