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

  -- * Node operations
  , unfoldRec
  , nodeEdges
  , union
  , mapNodes
  ) where

import Data.Function ( on )
import Data.Hashable ( Hashable(..) )
import Data.List ( sort, concatMap )
import Control.Lens ( (&), ix, (^?), (%~) )
import Data.Maybe ( catMaybes )

import GHC.Generics ( Generic )
import Data.Aeson ( ToJSON, FromJSON )

import Data.List.Extra ( nubSort, nubOrd )

-- | Switch the comments on these lines to switch to ekmett's original `intern` library
--   instead of our single-threaded hashtable-based reimplementation.
import Data.Interned.Extended.HashTableBased
-- import Data.Interned ( Interned(..), unintern, Id, Cache, mkCache )
-- import Data.Interned.Extended.SingleThreaded ( intern )

import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term

import Data.Memoization ( MemoCacheTag(..), memo )
import Utility.HashJoin

import Debug.Trace
---------------------------------------------------------------------------------------------



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

-- | Seemingly-hacky yet theoretically-sound restricted implementation of cyclic terms:
-- Assumes a single globally unique recursive node
data Node = InternedNode {-# UNPACK #-} !Id ![Edge]
          | EmptyNode
          | Mu !Node
          | Rec
          deriving (Generic)

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
nodeIdentity EmptyNode          = -1
nodeIdentity (Mu n)             = -2
nodeIdentity Rec                = -3

setChildren :: Edge -> [Node] -> Edge
setChildren e ns = mkEdge (edgeSymbol e) ns (edgeEcs e)

dropEcs :: Edge -> Edge
dropEcs e = Edge (edgeSymbol e) (edgeChildren e)


----------------------
------ Node operations
----------------------

unfoldRec :: Node -> Node
unfoldRec = memo (NameTag "unfoldRec") go
  where
    go n = mapNodes (\x -> if x == Rec then Mu n else x) n

union :: [Node] -> Node
union ns = case filter (/= EmptyNode) ns of
             []  -> EmptyNode
             ns' -> Node (concat $ map nodeEdges ns')

mapNodes :: (Node -> Node) -> Node -> Node
mapNodes f n = go n
  where
    -- | Memoized separately for each mapNodes invocation
    go :: Node -> Node
    go = memo (NameTag "mapNodes") (go' f)
    {-# NOINLINE go #-}

    go' :: (Node -> Node) -> Node -> Node
    go' f EmptyNode = EmptyNode
    go' f (Node es) = f $ (Node $ map (\e -> setChildren e $ (map go (edgeChildren e))) es)
    go' f (Mu n)    = f $ (Mu $ go n)
    go' f Rec       = f Rec

nodeEdges :: Node -> [Edge]
nodeEdges (Node es) = es
nodeEdges (Mu n)    = nodeEdges (unfoldRec n)
nodeEdges _         = []


instance Pathable Node Node where
  type Emptyable Node = Node

  getPath _                EmptyNode = EmptyNode
  getPath EmptyPath        n         = n
  getPath p                (Mu n)    = getPath p (unfoldRec n)
  getPath (ConsPath p ps) (Node es)  = union $ nubOrd $ map (getPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns) = ns ^? ix p

  getAllAtPath _               EmptyNode = []
  getAllAtPath EmptyPath       n         = [n]
  getAllAtPath p               (Mu n)    = getAllAtPath p (unfoldRec n)
  getAllAtPath (ConsPath p ps) (Node es) = concatMap (getAllAtPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns) = ns ^? ix p

  modifyAtPath f EmptyPath       n         = f n
  modifyAtPath _ _               EmptyNode = EmptyNode
  modifyAtPath f p               (Mu n)    = modifyAtPath f p (unfoldRec n)
  modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
    where
      goEdge :: Edge -> Edge
      goEdge e = setChildren e (edgeChildren e & ix p %~ modifyAtPath f ps)

instance Pathable [Node] Node where
  type Emptyable Node = Node

  getPath EmptyPath       ns = union ns
  getPath (ConsPath p ps) ns = case ns ^? ix p of
                                 Nothing -> EmptyNode
                                 Just n  -> getPath ps n

  getAllAtPath EmptyPath       ns = []
  getAllAtPath (ConsPath p ps) ns = case ns ^? ix p of
                                      Nothing -> []
                                      Just n  -> getAllAtPath ps n

  modifyAtPath f EmptyPath       ns = ns
  modifyAtPath f (ConsPath p ps) ns = ns & ix p %~ modifyAtPath f ps

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
instance ToJSON Node
instance FromJSON Node
instance ToJSON UninternedNode
instance FromJSON UninternedNode

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
instance ToJSON Edge
instance FromJSON Edge
instance ToJSON UninternedEdge
instance FromJSON UninternedEdge

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
