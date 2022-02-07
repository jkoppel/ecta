{-# LANGUAGE OverloadedStrings #-}

module Data.ECTA.Internal.ECTA.Type (
    RecNodeId(..)

  , Edge(.., Edge)
  , UninternedEdge(..)
  , mkEdge
  , emptyEdge
  , edgeChildren
  , edgeEcs
  , edgeSymbol
  , setChildren

  , Node(.., Node, Mu)
  , UninternedNode(..)
  , fillInTmpRecNodes
  , nodeIdentity
  , modifyNode
  , createMu
  ) where

import Data.Function ( on )
import Data.Hashable ( Hashable(..) )
import Data.List ( sort )

import GHC.Generics ( Generic )

import Data.List.Extra ( nubSort )

-- | Switch the comments on these lines to switch to ekmett's original `intern` library
--   instead of our single-threaded hashtable-based reimplementation.
import Data.Interned.Extended.HashTableBased

-- NOTE 2/7/2022: This version is likely to break because there are nested calls to intern
--                for Mu nodes. See related comment in HashTableBased.hs
--import Data.Interned ( Interned(..), unintern, Id, Cache, mkCache )
--import Data.Interned.Extended.SingleThreaded ( intern )

import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term


import Data.Memoization

---------------------------------------------------------------------------------------------

-----------------------------------------------------------------
-------------------------- Mu node table ------------------------
-----------------------------------------------------------------

data RecNodeId = RecNodeId { unRecNodeId :: {-# UNPACK #-} !Id }
               | TmpRecNodeId
  deriving ( Eq, Ord, Show, Generic )

instance Hashable RecNodeId

-----------------------------------------------------------------
----------------------------- Edges -----------------------------
-----------------------------------------------------------------

data Edge = InternedEdge { edgeId         :: !Id
                         , uninternedEdge :: !UninternedEdge
                         }

instance Show Edge where
  show e | edgeEcs e == EmptyConstraints = "(Edge " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ ")"
         | otherwise                     = "(mkEdge " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ " " ++ show (edgeEcs e) ++ ")"

--instance Show Edge where
--  show e = "InternedEdge " ++ show (edgeId e) ++ " " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ " " ++ show (edgeEcs e)

edgeSymbol :: Edge -> Symbol
edgeSymbol = uEdgeSymbol . uninternedEdge

edgeChildren :: Edge -> [Node]
edgeChildren = uEdgeChildren . uninternedEdge

edgeEcs :: Edge -> EqConstraints
edgeEcs = uEdgeEcs . uninternedEdge

instance Eq Edge where
  (InternedEdge {edgeId = n1}) == (InternedEdge {edgeId = n2}) = n1 == n2

instance Ord Edge where
  compare = compare `on` edgeId

instance Hashable Edge where
  hashWithSalt s e = s `hashWithSalt` (edgeId e)


-----------------------------------------------------------------
------------------------------ Nodes ----------------------------
-----------------------------------------------------------------

data Node = InternedNode {-# UNPACK #-} !Id ![Edge]
          | EmptyNode
          | InternedMu {-# UNPACK #-} !Id !Node
          | Rec {-# UNPACK #-} !RecNodeId

instance Eq Node where
  (InternedNode i1 _) == (InternedNode i2 _) = i1 == i2
  EmptyNode           == EmptyNode           = True
  (InternedMu i1 _)   == (InternedMu i2 _)   = i1 == i2
  Rec i1              == Rec i2              = i1 == i2
  _                   == _                   = False

instance Show Node where
  show (InternedNode _ es) = "(Node " <> show es <> ")"
  show EmptyNode           = "EmptyNode"
  show (InternedMu _ n)    = "(Mu " <> show n <> ")"
  show (Rec n)             = "(Rec " <> show n <> ")"

instance Ord Node where
  compare n1 n2 = compare (nodeDescriptorInt n1) (nodeDescriptorInt n2)
    where
      nodeDescriptorInt :: Node -> Int
      nodeDescriptorInt EmptyNode           = -1
      nodeDescriptorInt (InternedNode i _)  = 3*i
      nodeDescriptorInt (InternedMu i _)    = 3*i + 1
      nodeDescriptorInt (Rec (RecNodeId i)) = 3*i + 2

instance Hashable Node where
  hashWithSalt s EmptyNode          = s `hashWithSalt` (-1 :: Int)
  hashWithSalt s (InternedMu i _)   = s `hashWithSalt` (-2 :: Int) `hashWithSalt` i
  hashWithSalt s (Rec i)            = s `hashWithSalt` (-3 :: Int) `hashWithSalt` i
  hashWithSalt s (InternedNode i _) = s `hashWithSalt` i


----------------------
------ Getters and setters
----------------------

nodeIdentity :: Node -> Id
nodeIdentity (InternedMu   i _) = i
nodeIdentity (InternedNode i _) = i

setChildren :: Edge -> [Node] -> Edge
setChildren e ns = mkEdge (edgeSymbol e) ns (edgeEcs e)

dropEcs :: Edge -> Edge
dropEcs e = Edge (edgeSymbol e) (edgeChildren e)


-----------------------------------------------------------------
------------------------- Interning Nodes -----------------------
-----------------------------------------------------------------

fillInTmpRecNodes :: Id -> Node -> Node
fillInTmpRecNodes i n = go n
  where
    -- | Memoized separately for each invocation
    go :: Node -> Node
    go = memo (NameTag "fillInTmpRecNodes") (go' i)
    {-# NOINLINE go #-}

    go' :: Id -> Node -> Node
    go' _ EmptyNode          = EmptyNode
    go' _ (Node es)          = Node $ map (\e -> setChildren e $ (map go (edgeChildren e))) es
    go' _ n@(Mu _)           = n
    go' i (Rec TmpRecNodeId) = Rec $ RecNodeId i
    go' _ n@(Rec _)          = n

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
  -- TODO (2/7/2022):
  --  WARNING: This next case contains a recursive call to intern. We do not currently have a stable guarantee
  --           that interned ID's won't be reused.
  identify i (UninternedMu n)    = InternedMu i $ fillInTmpRecNodes i n
  identify _ UninternedRec       = Rec TmpRecNodeId

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
pattern Edge s ns <- (InternedEdge _ (UninternedEdge s ns _)) where
  Edge s ns = intern $ UninternedEdge s ns EmptyConstraints

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
   | otherwise                       = intern $ UninternedEdge s ns ecs


-------------------
------ Node constructors
-------------------

{-# COMPLETE Node, EmptyNode, Mu, Rec #-}

pattern Node :: [Edge] -> Node
pattern Node es <- (InternedNode _ es) where
  Node es = case removeEmptyEdges es of
              []  -> EmptyNode
              es' -> intern $ UninternedNode $ nubSort es'

-- | This pattern intentionally may not be used as a constructor
--   Rationale: Doing so would tempt programmers to write code of the form (\(Mu x) -> (Mu x))
--   Such code is buggy, as it modifies the id of the outer Mu without modifying the RecNodeId’s which reference it.
pattern Mu :: Node -> Node
pattern Mu n <- (InternedMu _ n)

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

createMu :: (Node -> Node) -> Node
createMu f = intern $ UninternedMu (f (Rec TmpRecNodeId))

collapseEmptyEdge :: Edge -> Maybe Edge
collapseEmptyEdge e@(Edge _ ns) = if any (== EmptyNode) ns then Nothing else Just e
