{-# LANGUAGE OverloadedStrings #-}

module Data.ECTA.Internal.ECTA.Type (
    Edge(.., Edge)
  , UninternedEdge(..)
  , mkEdge
  , emptyEdge
  , edgeChildren
  , edgeEcs
  , edgeSymbol
  , setChildren

  , Node(.., Node)
  , UninternedNode(..)
  , nodeIdentity
  , modifyNode
  , createGloballyUniqueMu
  ) where

import Data.Function ( on )
import Data.Hashable ( Hashable(..) )
import Data.List ( sort )

import GHC.Generics ( Generic )

import Data.List.Extra ( nubSort )

-- | Switch the comments on these lines to switch to ekmett's original `intern` library
--   instead of our single-threaded hashtable-based reimplementation.
import Data.Interned.Extended.HashTableBased
--import Data.Interned ( Interned(..), unintern, Id, Cache, mkCache )
--import Data.Interned.Extended.SingleThreaded ( intern )

import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term

---------------------------------------------------------------------------------------------



-----------------------------------------------------------------
----------------------------- Edges -----------------------------
-----------------------------------------------------------------


-- | Levels of equality-constraint reduction
-- 1) Unreduced: The FTA is identical in shape to what it would be if this constraint
--               were not present. To iterate through valid terms, one must
--               generate possible subterms and filter out equals.
--
-- 2) Leaf-reduced: Each node pointed to by the left path of the construct
--                  has been intersected with the union of all nodes pointed
--                  to by the right path. A filter is still required
--                  to find valid terms, but fewer invalid terms will be generated.
--
--                  HOWEVER, this property is unstable, and reducing other equality
--                  constraints on other nodes may make this property no longer hold.
--                  (See Sat.hs for a prime example.) We hence do not do anything
--                  with this level.
--
-- 3) Multiplied: Duplicates have been made of the hyperedge, and intersections performed, so that
--                it is guaranteed that, for each choice of term and the end of the left path,
--                there will be an equal term possible at the right edge. This enables
--                both efficient generation and counting.
--
-- The constraints being reduced is a property of the entire hyperedge, not of the individual constraints.
-- This is because reducing one constraint may result in another constraint becoming unreduced,
-- similar to how, in classic constraint propagation, one cannot process all constraints in a fixed linear order.
data ECReduction = ECUnreduced | ECLeafReduced | ECMultiplied
  deriving (Eq, Ord, Show, Generic)

instance Hashable ECReduction

-- | This design has a violation of the representable/valid principle: If one constructs an FTA
-- which is already fully reduced, then reducing it will change the edgeReduction field, but leave
-- all edges the same. They will not be equal, even though the graph is identical.
data Edge = InternedEdge { edgeId         :: !Id
                         , uninternedEdge :: !UninternedEdge
                         }

instance Show Edge where
  show e | edgeEcs e == EmptyConstraints = "(Edge " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ ")"
         | otherwise                     = "(mkEdge " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ " " ++ show (edgeEcs e) ++ ")"

--instance Show Edge where
--  show e = "InternedEdge " ++ show (edgeId e) ++ " " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ " " ++ show (edgeEcs e) ++ " " ++ show (edgeReduction e)

edgeSymbol :: Edge -> Symbol
edgeSymbol = uEdgeSymbol . uninternedEdge

edgeChildren :: Edge -> [Node]
edgeChildren = uEdgeChildren . uninternedEdge

edgeEcs :: Edge -> EqConstraints
edgeEcs = uEdgeEcs . uninternedEdge

edgeReduction :: Edge -> ECReduction
edgeReduction = uEdgeReduction . uninternedEdge


instance Eq Edge where
  (InternedEdge {edgeId = n1}) == (InternedEdge {edgeId = n2}) = n1 == n2

instance Ord Edge where
  compare = compare `on` edgeId

instance Hashable Edge where
  hashWithSalt s e = s `hashWithSalt` (edgeId e)


-----------------------------------------------------------------
------------------------------ Nodes ----------------------------
-----------------------------------------------------------------

-- | Seemingly-hacky yet theoretically-sound restricted implementation of cyclic terms:
-- Assumes a single globally unique recursive node
data Node = InternedNode {-# UNPACK #-} !Id ![Edge]
          | EmptyNode
          | Mu !Node
          | Rec

instance Eq Node where
  (InternedNode n1 _) == (InternedNode n2 _) = n1 == n2
  EmptyNode           == EmptyNode           = True
  Mu n1               == Mu n2               = True -- | And here I use the crazy globally unique Mu assumption
  Rec                 == Rec                 = True
  _                   == _                   = False

instance Show Node where
  show (InternedNode _ es) = "(Node " ++ show es ++ ")"
  show EmptyNode           = "EmptyNode"
  show (Mu n)              = "(Mu " ++ show n ++ ")"
  show Rec                 = "Rec"

instance Ord Node where
  compare n1 n2 = compare (dropEdges n1) (dropEdges n2)
    where
      dropEdges :: Node -> Either Id Int
      dropEdges (InternedNode n _) = Right n
      dropEdges EmptyNode          = Left 0
      dropEdges (Mu n)             = Left 1
      dropEdges Rec                = Left 2


instance Hashable Node where
  hashWithSalt s EmptyNode          = s `hashWithSalt` (-1 :: Int)
  hashWithSalt s (Mu _)             = s `hashWithSalt` (-2 :: Int)
  hashWithSalt s Rec                = s `hashWithSalt` (-3 :: Int)
  hashWithSalt s (InternedNode n _) = s `hashWithSalt` n


----------------------
------ Getters and setters
----------------------

nodeIdentity :: Node -> Id
nodeIdentity (InternedNode n _) = n

setChildren :: Edge -> [Node] -> Edge
setChildren e ns = mkEdge (edgeSymbol e) ns (edgeEcs e)

dropEcs :: Edge -> Edge
dropEcs e = Edge (edgeSymbol e) (edgeChildren e)


-----------------------------------------------------------------
------------------------- Interning Nodes -----------------------
-----------------------------------------------------------------

data UninternedNode = UninternedNode ![Edge]
                    | UninternedEmptyNode
                    | UninternedMu !Node
                    | UninternedRec
  deriving ( Eq, Generic )

instance Hashable UninternedNode

instance Interned Node where
  type Uninterned  Node = UninternedNode
  data Description Node = DNode !UninternedNode
    deriving ( Eq, Generic )

  describe = DNode

  identify i (UninternedNode es) = InternedNode i es
  identify _ UninternedEmptyNode = EmptyNode
  identify _ (UninternedMu n)    = Mu n
  identify _ UninternedRec       = Rec

  cache = nodeCache

instance Hashable (Description Node)

nodeCache :: Cache Node
nodeCache = mkCache
{-# NOINLINE nodeCache #-}

-----------------------------------------------------------------
------------------------ Interning Edges ------------------------
-----------------------------------------------------------------

data UninternedEdge = UninternedEdge { uEdgeSymbol    :: !Symbol
                                     , uEdgeChildren  :: ![Node]
                                     , uEdgeEcs       :: !EqConstraints
                                     , uEdgeReduction :: !ECReduction
                                     }
  deriving ( Eq, Show, Generic )

instance Hashable UninternedEdge

instance Interned Edge where
  type Uninterned  Edge = UninternedEdge
  data Description Edge = DEdge {-# UNPACK #-} !UninternedEdge
    deriving ( Eq, Generic )

  describe = DEdge

  identify i e = InternedEdge i e

  cache = edgeCache

instance Hashable (Description Edge)

edgeCache :: Cache Edge
edgeCache = mkCache
{-# NOINLINE edgeCache #-}

-----------------------------------------------------------------
----------------------- Smart constructors ----------------------
-----------------------------------------------------------------

-------------------
------ Edge constructors
-------------------

pattern Edge :: Symbol -> [Node] -> Edge
pattern Edge s ns <- (InternedEdge _ (UninternedEdge s ns _ _)) where
  Edge s ns = intern $ UninternedEdge s ns EmptyConstraints ECUnreduced

emptyEdge :: Edge
emptyEdge = Edge "" [EmptyNode]

isEmptyEdge :: Edge -> Bool
isEmptyEdge e@(Edge _ ns) = any (== EmptyNode) ns

removeEmptyEdges :: [Edge] -> [Edge]
removeEmptyEdges = filter (not . isEmptyEdge)

mkEdge :: Symbol -> [Node] -> EqConstraints -> Edge
mkEdge s ns ecs
   | constraintsAreContradictory ecs = emptyEdge
mkEdge s ns ecs
   | otherwise                       = intern $ UninternedEdge s ns ecs ECUnreduced


-------------------
------ Node constructors
-------------------

{-# COMPLETE Node, EmptyNode, Mu, Rec #-}

pattern Node :: [Edge] -> Node
pattern Node es <- (InternedNode _ es) where
  Node es = case removeEmptyEdges es of
              []  -> EmptyNode
              es' -> intern $ UninternedNode $ nubSort es'

mkNodeAlreadyNubbed :: [Edge] -> Node
mkNodeAlreadyNubbed es = case removeEmptyEdges es of
                           []  -> EmptyNode
                           es' -> intern $ UninternedNode $ sort es'

-- | An optimized Node constructor that avoids the interning/preprocessing of the Node constructor
--   when nothing changes
modifyNode :: Node -> ([Edge] -> [Edge]) -> Node
modifyNode n@(Node es) f = let es' = f es in
                           if es' == es then
                             n
                           else
                             Node es'

createGloballyUniqueMu :: (Node -> Node) -> Node
createGloballyUniqueMu f = Mu (f Rec)

collapseEmptyEdge :: Edge -> Maybe Edge
collapseEmptyEdge e@(Edge _ ns) = if any (== EmptyNode) ns then Nothing else Just e