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
  , InternedMu(..)
  , UninternedNode(..)
  , nodeIdentity
  , modifyNode
  , createMu
  ) where

import Data.Function ( on )
import Data.Hashable ( Hashable(..) )
import Data.List ( sort )
import GHC.Generics ( Generic )

import System.IO.Unsafe ( unsafePerformIO )

import Data.List.Extra ( nubSort )

--   Switch the comments on these lines to switch to ekmett's original `intern` library
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

newtype RecNodeId = RecNodeId { unRecNodeId :: Id }
  deriving ( Eq, Ord, Show, Generic )

instance Hashable RecNodeId

-----------------------------------------------------------------
----------------------------- Edges -----------------------------
-----------------------------------------------------------------

data Edge = InternedEdge { edgeId         :: !Id
                         , uninternedEdge :: !UninternedEdge
                         }
                         deriving (Generic)

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

data InternedMu = MkInternedMu {
      -- | 'Id' of the node itself
      internedMuId :: {-# UNPACK #-} !Id

      -- | The body of the 'Mu'
      --
      -- Recursive occurrences to this node should be
      --
      -- > Rec (RecNodeId internedMuId)
    , internedMuBody :: !Node

      -- | The body of the 'Mu', before it was assigned an 'Id'
      --
      -- Invariant:
      --
      -- > substFree internedMuId (Rec (RecNodeId (-1)) == internedMuNoId
    , internedMuNoId :: !Node
    }

data Node = InternedNode {-# UNPACK #-} !Id ![Edge]
          | EmptyNode
          | InternedMu {-# UNPACK #-} !InternedMu
          | Rec {-# UNPACK #-} !RecNodeId

instance Eq Node where
  (InternedNode i1 _) == (InternedNode i2 _) = i1 == i2
  EmptyNode           == EmptyNode           = True
  (InternedMu mu1)    == (InternedMu mu2)    = internedMuId mu1 == internedMuId mu2
  Rec i1              == Rec i2              = i1 == i2
  _                   == _                   = False

instance Show Node where
  show (InternedNode _ es) = "(Node " <> show es <> ")"
  show EmptyNode           = "EmptyNode"
  show (InternedMu mu)     = "(Mu " <> show (internedMuBody mu) <> ")"
  show (Rec n)             = "(Rec " <> show n <> ")"

instance Ord Node where
  compare n1 n2 = compare (nodeDescriptorInt n1) (nodeDescriptorInt n2)
    where
      nodeDescriptorInt :: Node -> Int
      nodeDescriptorInt EmptyNode           = -1
      nodeDescriptorInt (InternedNode i _)  = 3*i
      nodeDescriptorInt (InternedMu mu)     = 3*i + 1
        where
          i = internedMuId mu
      nodeDescriptorInt (Rec (RecNodeId i)) = 3*i + 2

instance Hashable Node where
  hashWithSalt s EmptyNode          = s `hashWithSalt` (-1 :: Int)
  hashWithSalt s (InternedMu mu)    = s `hashWithSalt` (-2 :: Int) `hashWithSalt` i
    where
      i = internedMuId mu
  hashWithSalt s (Rec i)            = s `hashWithSalt` (-3 :: Int) `hashWithSalt` i
  hashWithSalt s (InternedNode i _) = s `hashWithSalt` i

----------------------
------ Getters and setters
----------------------

nodeIdentity :: Node -> Id
nodeIdentity (InternedMu   mu)   = internedMuId mu
nodeIdentity (InternedNode i _)  = i
nodeIdentity (Rec (RecNodeId i)) = i
nodeIdentity n                   = error $ "nodeIdentity: unexpected node " <> show n

setChildren :: Edge -> [Node] -> Edge
setChildren e ns = mkEdge (edgeSymbol e) ns (edgeEcs e)

_dropEcs :: Edge -> Edge
_dropEcs e = Edge (edgeSymbol e) (edgeChildren e)


-----------------------------------------------------------------
------------------------- Interning Nodes -----------------------
-----------------------------------------------------------------

data UninternedNode =
      UninternedNode ![Edge]
    | UninternedEmptyNode

      -- | Recursive node
      --
      -- The function should be parametric in the Id:
      --
      -- > substFree i (Rec (RecNodeId j)) (f i) == f j
    | UninternedMu !(Id -> Node)

instance Eq UninternedNode where
  UninternedNode es   == UninternedNode es'  = es == es'
  UninternedEmptyNode == UninternedEmptyNode = True
  UninternedMu mu     == UninternedMu mu'    = mu (-1) == mu' (-1)
  _                   == _                   = False

instance Hashable UninternedNode where
  hashWithSalt salt = go
    where
      go :: UninternedNode -> Int
      go  UninternedEmptyNode = hashWithSalt salt (0 :: Int, ())
      go (UninternedNode es)  = hashWithSalt salt (1 :: Int, es)
      go (UninternedMu mu)    = hashWithSalt salt (2 :: Int, mu (-1))

instance Interned Node where
  type Uninterned  Node = UninternedNode
  data Description Node = DNode !UninternedNode
    deriving ( Eq, Generic )

  describe = DNode

  identify i (UninternedNode es) = InternedNode i es
  identify _ UninternedEmptyNode = EmptyNode
  identify i (UninternedMu n)    = InternedMu $ MkInternedMu {
        internedMuId   = i
      , internedMuBody = n i

        -- In order to establish the invariant for internedMuNoId, we need to know
        --
        -- > substFree i (Rec (RecNodeId (-1)) (n i) == n (-1)
        -- > == n (-1)
        --
        -- This follows directly from the parametricity requirement on 'UninternedMu'.
      , internedMuNoId = n (-1)
      }

  cache = nodeCache


instance Hashable (Description Node)

nodeCache :: Cache Node
nodeCache = unsafePerformIO freshCache
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
edgeCache = unsafePerformIO freshCache
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

{-# COMPLETE Edge #-}

emptyEdge :: Edge
emptyEdge = Edge "" [EmptyNode]

isEmptyEdge :: Edge -> Bool
isEmptyEdge (Edge _ ns) = any (== EmptyNode) ns

removeEmptyEdges :: [Edge] -> [Edge]
removeEmptyEdges = filter (not . isEmptyEdge)

mkEdge :: Symbol -> [Node] -> EqConstraints -> Edge
mkEdge s ns ecs
  | constraintsAreContradictory ecs = emptyEdge
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

_mkNodeAlreadyNubbed :: [Edge] -> Node
_mkNodeAlreadyNubbed es = case removeEmptyEdges es of
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
modifyNode n           _ = error $ "modifyNode: unexpected node " <> show n

_collapseEmptyEdge :: Edge -> Maybe Edge
_collapseEmptyEdge e@(Edge _ ns) = if any (== EmptyNode) ns then Nothing else Just e

------ Mu

-- | Pattern only a Mu constructor
--
-- When we go underneath a Mu constructor, we need to bind the corresponding Rec node to something: that's why pattern
-- matching on 'Mu' yields a function. Code that wants to traverse the term as-is should match on the interned
-- constructors instead (and then deal with the dangling references).
--
-- An identity function
--
-- > foo (Mu f) = Mu f
--
-- will run in O(1) time:
--
-- > foo (Mu f) = Mu f
-- >   -- { expand view patern }
-- > foo node | Just f <- matchMu node = createMu f
-- >   -- { case for @InternedMu mu@ }
-- > foo (InternedMu mu) | Just f <- matchMu (InternedMu m) = createMu f
-- >   -- { definition of matchMu }
-- > foo (InternedMu mu) = let f = \n' -> if n' == Rec (RecNodeId (-1)) then internedMuNoId mu else substFree (internedMuId mu) n' (internedMuBody mu)
-- >                       in createMu f
-- >   -- { definition of createMu }
-- > foo (InternedMu mu) = intern $ UninternedMu (f . Rec . RecNodeId)
--
-- At this point, `intern` will apply @f . Rec . RecNodeId@ to the identifier @(-1)@ in order to do the hash lookup.
-- This will trigger the special case in @f@, and immediately return @internedMuId@, which will be in the cache.
pattern Mu :: (Node -> Node) -> Node
pattern Mu f <- (matchMu -> Just f)
  where
    Mu = createMu

-- | Construct recursive node
--
-- Implementation note: 'createMu' and 'matchMu' interact in non-trivial ways; see docs of the 'Mu' pattern synonym
-- for performance considerations.
createMu :: (Node -> Node) -> Node
createMu f = intern $ UninternedMu (f . Rec . RecNodeId)

-- | Match on a 'Mu' node
--
-- Implementation note: 'createMu' and 'matchMu' interact in non-trivial ways; see docs of the 'Mu' pattern synonym
-- for performance considerations.
matchMu :: Node -> Maybe (Node -> Node)
matchMu (InternedMu mu) = Just $ \n' ->
    if n' == Rec (RecNodeId (-1)) then
      -- This is an important special case, because the term with (-1) as the ID is the one that is used for interning.
      -- It is justified by the equality
      --
      -- >    substFree internedMuId (Rec (RecNodeId (-1)) internedMuBody
      -- > == internedMuNoId
      --
      -- which is the invariant of 'internedMuNoId'.
      internedMuNoId mu
    else
      substFree (internedMuId mu) n' (internedMuBody mu)
matchMu _otherwise = Nothing

-- | Substitution
--
-- @substFree i n@ will replace all occurrences of @Rec (RecNodeId i)@ by @n@. We appeal to the uniqueness of node IDs
-- and assume that all occurrences of @i@ must be free (in other words, that any occurrences of 'Mu' will have a
-- /different/ identifier.
--
-- Postcondition:
--
-- > substFree i (Rec (RecNodeId i)) == id
substFree :: Id -> Node -> Node -> Node
substFree old new = go
  where
    go :: Node -> Node
    go = memo (NameTag "substFree") go'
    {-# NOINLINE go #-}

    go' :: Node -> Node
    go' EmptyNode               = EmptyNode
    go' (InternedNode _ es)     = intern $ UninternedNode (map goEdge es)
    go' (InternedMu mu)         = intern $ UninternedMu $ \nid -> go (substFree (internedMuId mu) (Rec (RecNodeId nid)) (internedMuBody mu))
    go' n@(Rec (RecNodeId nid)) = if nid == old
                                    then new
                                    else n

    goEdge :: Edge -> Edge
    goEdge e = setChildren e $ map go (edgeChildren e)

