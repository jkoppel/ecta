{-# LANGUAGE OverloadedStrings #-}

-- | Equality-constrained deterministic finite tree automata
--
-- Specialized to DAGs

module ECDFTA (
    Symbol
  , Term(..)
  , Path
  , path
  , Pathable(..)
  , EqConstraint(EqConstraint)
  , Edge(Edge)
  , Node(Node, StartNode, EmptyNode)

  -- * Operations
  , nodeCount
  , edgeCount
  , union
  , intersect
  , denotation
  ) where

import Control.Monad ( guard )
import Control.Monad.State ( evalState, State, MonadState(..), modify )
import Data.List ( sort, nub, intercalate )
import           Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes )
import           Data.Set ( Set )
import qualified Data.Set as Set
import Data.String (IsString(..) )
import qualified Data.Text as Text

import GHC.Generics ( Generic )

import Control.Lens ( (&), ix, _1, (^?), (%~) )

import Data.Hashable ( Hashable )
import Data.Interned ( Interned(..), intern, unintern, Id, Cache, mkCache )
import Data.Interned.Text ( InternedText )

-------------------------------------------------------------------------------


---------------------------------------------------------------
-------------- Terms, the things being represented ------------
---------------------------------------------------------------


data Symbol = Symbol {-# UNPACK #-} !InternedText
  deriving ( Eq, Ord, Generic )

instance Show Symbol where
  show (Symbol internedText) = Text.unpack $ unintern internedText

instance Hashable Symbol

instance IsString Symbol where
  fromString = Symbol . fromString

data Term = Term Symbol [Term]
  deriving ( Eq, Ord, Generic )

instance Hashable Term

instance Show Term where
  show (Term s []) = show s
  show (Term s ts) = show s ++ "(" ++ (intercalate "," $ map show ts) ++ ")"

---------------------
------ Paths
---------------------

data Path = Path { unPath :: ![Int] }
  deriving (Eq, Ord, Show, Generic)

instance Hashable Path

path :: [Int] -> Path
path = Path

{-# COMPLETE EmptyPath, ConsPath #-}

pattern EmptyPath :: Path
pattern EmptyPath = Path []

pattern ConsPath :: Int -> Path -> Path
pattern ConsPath p ps <- Path (p : (Path -> ps)) where
  ConsPath p (Path ps) = Path (p : ps)

pathHeadUnsafe :: Path -> Int
pathHeadUnsafe (Path ps) = head ps

pathTailUnsafe :: Path -> Path
pathTailUnsafe (Path ps) = Path (tail ps)

---------------------
------ Term ops
---------------------

-- | Really I think paths should be treated as a lens-library Traversal
class Pathable t t' | t -> t' where
  getPath      :: Path -> t -> t'
  modifyAtPath :: (t' -> t') -> Path -> t -> t

instance Pathable Term Term where
  getPath EmptyPath       t           = t
  getPath (ConsPath p ps) (Term _ ts) = case ts ^? ix p of
                                          Nothing -> Term "" [] -- TODO: this doesn't work
                                          Just t  -> getPath ps t

  modifyAtPath f EmptyPath       t           = f t
  modifyAtPath f (ConsPath p ps) (Term s ts) = Term s (ts & ix p %~ modifyAtPath f ps)

---------------------------------------------------------------
------------------- Data type and interning -------------------
---------------------------------------------------------------



data EqConstraint = EqConstraint' !Path !Path
  deriving (Eq, Ord, Show, Generic)

instance Hashable EqConstraint

pattern EqConstraint :: Path -> Path -> EqConstraint
pattern EqConstraint p1 p2 <- EqConstraint' p1 p2 where
  EqConstraint p1 p2 = EqConstraint' (min p1 p2) (max p1 p2)

data Edge = Edge' !Symbol ![Node] ![EqConstraint]
  deriving ( Eq, Ord, Show, Generic)

instance Hashable Edge

-- | Something's wrong. The StartNode doesn't really exist. Instead, there are edges with no children
--   These can be seen as implicit edges to the unique StartNode.
data Node = InternedNode {-# UNPACK #-} !Id ![Edge]
          | StartNode
          | EmptyNode
  deriving ( Show, Generic )

instance Eq Node where
  (InternedNode n1 _) == (InternedNode n2 _) = n1 == n2
  StartNode           == StartNode           = True
  EmptyNode           == EmptyNode           = True
  _                   == _                   = False

instance Ord Node where
  compare n1 n2 = compare (dropEdges n1) (dropEdges n2)
    where
      dropEdges :: Node -> Either Id Int
      dropEdges (InternedNode n _) = Left n
      dropEdges StartNode          = Right 0
      dropEdges EmptyNode          = Right 1

instance Hashable Node


-------------
------ Getters
-------------

nodeIdentity :: Node -> Id
nodeIdentity (InternedNode n _) = n

edgeSymbol :: Edge -> Symbol
edgeSymbol (Edge s _ _) = s

nodeEdges :: Node -> [Edge]
nodeEdges (Node es) = es
nodeEdges _         = []

-------------
------ Interning
-------------


data UninternedNode = UninternedNode ![Edge]
                    | UninternedStartNode
                    | UninternedEmptyNode

data DEdge = DEdge !Symbol ![Id] ![EqConstraint]
  deriving ( Eq, Ord, Generic )

instance Hashable DEdge

instance Interned Node where
  type Uninterned  Node = UninternedNode
  data Description Node = DNode ![DEdge]
                        | DStartNode
                        | DEmptyNode
    deriving ( Eq, Ord, Generic )

  describe (UninternedNode es) = DNode (map describeEdge es)
    where
      describeEdge (Edge s children constrs) = DEdge s (map nodeIdentity children) constrs
  describe UninternedStartNode = DStartNode
  describe UninternedEmptyNode = DEmptyNode

  identify i (UninternedNode es) = InternedNode i es
  identify _ UninternedStartNode = StartNode
  identify _ UninternedEmptyNode = EmptyNode

  cache = ecdftaCache

instance Hashable (Description Node)

ecdftaCache :: Cache Node
ecdftaCache = mkCache
{-# NOINLINE ecdftaCache #-}

---------------------
------ Smart constructors
---------------------

pattern Edge :: Symbol -> [Node] -> [EqConstraint] -> Edge
pattern Edge s ns ecs <- (Edge' s ns ecs) where
  Edge s ns ecs = Edge' s (foldr reduceEqConstraint ns ecs) (sort ecs) -- TODO: Reduce redundant work from multiple calls here

{-# COMPLETE Node, StartNode, EmptyNode #-}

pattern Node :: [Edge] -> Node
pattern Node es <- (InternedNode _ es) where
  Node es = case removeEmptyEdges es of
              []  -> EmptyNode
              es' -> intern $ UninternedNode $ nub $ sort es' -- TODO: Use sortUniq to eliminate a pass, ensure sort is fast for already sorted


collapseEmptyEdge :: Edge -> Maybe Edge
collapseEmptyEdge e@(Edge _ ns _) = if any (== EmptyNode) ns then Nothing else Just e

---------------------------------------------------------------
------------------------- Operations --------------------------
---------------------------------------------------------------

-----------------------
------ Edge operations
-----------------------

removeEmptyEdges :: [Edge] -> [Edge]
removeEmptyEdges = filter (not . isEmptyEdge)

isEmptyEdge :: Edge -> Bool
isEmptyEdge e@(Edge _ ns _) = any (== EmptyNode) ns


------------
------ Size operations
------------

nodeCount :: Node -> Int
nodeCount n = evalState (go n) Set.empty
  where
    go :: Node -> State (Set Id) Int
    go EmptyNode   = return 0
    go n@(Node es) = do
      seen <- get
      let nId = nodeIdentity n
      if Set.member nId seen then
        return 0
       else do
        modify (Set.insert nId)
        (+1) <$> sum <$> mapM (\(Edge _ ns _) -> sum <$> mapM go ns) es

edgeCount :: Node -> Int
edgeCount n = evalState (go n) Set.empty
  where
    go :: Node -> State (Set Id) Int
    go EmptyNode   = return 0
    go n@(Node es) = do
      seen <- get
      let nId = nodeIdentity n
      if Set.member nId seen then
        return 0
       else do
        modify (Set.insert nId)
        (+ (length es)) <$> sum <$> mapM (\(Edge _ ns _) -> sum <$> mapM go ns) es

-----------------------
------ Interning intersections
-----------------------

data IntersectedNode = IntersectedNode { intersectionId :: {-# UNPACK #-} !Id
                                       , runIntersect   :: !Node
                                       }

data DoIntersect = DoIntersect !Node !Node

instance Interned IntersectedNode where
  type Uninterned  IntersectedNode = DoIntersect
  data Description IntersectedNode = DIntersect !Id !Id
    deriving ( Eq, Ord, Generic )

  describe (DoIntersect n1 n2) = DIntersect (nodeIdentity n1) (nodeIdentity n2)

  identify i (DoIntersect n1 n2) = IntersectedNode i (doIntersect n1 n2)

  cache = intersectionCache

instance Hashable (Description IntersectedNode)

intersectionCache :: Cache IntersectedNode
intersectionCache = mkCache
{-# NOINLINE intersectionCache #-}

------------
------ Intersect
------------

intersect :: Node -> Node -> Node
intersect EmptyNode _         = EmptyNode
intersect _         EmptyNode = EmptyNode
intersect n1        n2        = runIntersect $ intern (DoIntersect n1 n2)

-- | TODO: Think through the reductions for the equality constraints added
doIntersect :: Node -> Node -> Node
doIntersect n1@(Node es1) n2@(Node es2)
  | n1 == n2                            = n1
  | otherwise                           = case catMaybes [intersectEdge e1 e2 | e1 <- es1, e2 <- es2] of
                                            [] -> EmptyNode
                                            es -> Node es
  where
    intersectEdge :: Edge -> Edge -> Maybe Edge
    intersectEdge (Edge s1 _ _) (Edge s2 _ _)
      | s1 /= s2                                                  = Nothing
    intersectEdge (Edge s children1 ecs1) (Edge _ children2 ecs2)
      | length children1 /= length children2                      = error ("Different lengths encountered for children of symbol " ++ show s)
    intersectEdge (Edge s children1 ecs1) (Edge _ children2 ecs2) = Just $ Edge s (zipWith intersect children1 children2) (ecs1 ++ ecs2)


------------
------ Union
------------

union :: [Node] -> Node
union ns = case filter (/= EmptyNode) ns of
             []  -> EmptyNode
             ns' -> Node (concat $ map nodeEdges ns')

----------------------
------ Path operations
----------------------

instance Pathable Node Node where
  getPath EmptyPath        n        = n
  getPath (ConsPath p ps) (Node es) = union $ map (getPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns _) = ns ^? ix p

  modifyAtPath f EmptyPath       n         = f n
  modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
    where
      goEdge :: Edge -> Edge
      goEdge (Edge s ns ecs) = Edge s (ns & ix p %~ modifyAtPath f ps) ecs

instance Pathable [Node] Node where
  getPath EmptyPath       ns = union ns
  getPath (ConsPath p ps) ns = case ns ^? ix p of
                                 Nothing -> EmptyNode
                                 Just n  -> getPath ps n

  modifyAtPath f EmptyPath       ns = ns
  modifyAtPath f (ConsPath p ps) ns = ns & ix p %~ modifyAtPath f ps



------------------------------------
------ Reducing equality constraints
------------------------------------

reduceEqConstraint :: EqConstraint -> [Node] -> [Node]
reduceEqConstraint (EqConstraint p1 p2) ns = modifyAtPath (intersect n1) p2 $
                                             modifyAtPath (intersect n2) p1 $
                                             ns
  where
    n1 = getPath p1 ns
    n2 = getPath p2 ns


------------------------------------
------ Denotation
------------------------------------

denotation :: Node -> [Term]
denotation n = go n
  where
    -- | TODO: This is unused. It is needed for the more efficient implementation of this, as well as for efficient counting
    descendMap :: Map Path Term -> Int -> Map Path Term
    descendMap mp p = Map.fromList $ map (_1 %~ pathTailUnsafe) $ filter ((== p) . pathHeadUnsafe . fst) $ Map.toList mp

    ecSatisfied :: Term -> EqConstraint -> Bool
    ecSatisfied t (EqConstraint p1 p2) = getPath p1 t == getPath p2 t

    go :: Node -> [Term]
    go n = case n of
             EmptyNode -> []
             Node es -> do
               Edge s ns ecs <- es

               -- Very inefficient here, but easy to code
               children <- sequence $ map go ns

               let res = Term s children
               guard (all (ecSatisfied res) ecs)
               return res



