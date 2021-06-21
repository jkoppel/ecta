{-# LANGUAGE OverloadedStrings #-}

-- | Equality-constrained deterministic finite tree automata
--
-- Specialized to DAGs

module ECDFTA (
    Symbol(Symbol)
  , Term(..)
  , Path
  , path
  , Pathable(..)
  , EqConstraint(EqConstraint)
  , Edge(Edge)
  , mkEdge
  , Node(Node, EmptyNode)

  -- * Operations
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

import Control.Monad ( guard )
import Control.Monad.State ( evalState, State, MonadState(..), modify )
import Data.Function ( on )
import Data.List ( sort, nub, intercalate )
import           Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes )
import Data.Monoid ( Monoid(..), Sum(..) )
import Data.Semigroup ( Max(..) )
import           Data.Set ( Set )
import qualified Data.Set as Set
import Data.String (IsString(..) )
import Data.Text ( Text )
import qualified Data.Text as Text

import GHC.Generics ( Generic )

import Control.Lens ( (&), ix, _1, (^?), (%~) )

import qualified Data.Graph.Inductive as Fgl
import Data.Hashable ( Hashable, hashWithSalt )
import qualified Data.Interned as OrigInterned
import Data.Interned.Text ( InternedText, internedTextId )
import Data.List.Index ( imap )

import qualified Language.Dot.Syntax as Dot

--import Data.Interned ( Interned(..), unintern, Id, Cache, mkCache )
import Data.Interned.Extended.HashTableBased
--import Data.Interned.Extended.SingleThreaded ( intern )
import Memo ( memo2 )

-------------------------------------------------------------------------------


---------------------------------------------------------------
---------------------- Misc / general -------------------------
---------------------------------------------------------------

fix :: (Eq a) => (a -> a) -> a -> a
fix f x = let x' = f x in
          if x' == x then
            x
          else
            fix f x'

class Pretty a where
  pretty :: a -> Text

---------------------------------------------------------------
-------------- Terms, the things being represented ------------
---------------------------------------------------------------


data Symbol = Symbol' {-# UNPACK #-} !InternedText
  deriving ( Eq, Ord )

pattern Symbol :: Text -> Symbol
pattern Symbol t <- Symbol' (OrigInterned.unintern -> t) where
  Symbol t = Symbol' (OrigInterned.intern t)

instance Pretty Symbol where
  pretty (Symbol t) = t

instance Show Symbol where
  show = Text.unpack . pretty

instance Hashable Symbol where
  hashWithSalt s (Symbol' t) = s `hashWithSalt` (internedTextId t)

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

instance Pretty Path where
  pretty (Path ps) = Text.intercalate "." (map (Text.pack . show) ps)

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

----------------------
----- Edges
----------------------

data EqConstraint = EqConstraint' !Path !Path
  deriving (Eq, Ord, Show, Generic)

instance Hashable EqConstraint

pattern EqConstraint :: Path -> Path -> EqConstraint
pattern EqConstraint p1 p2 <- EqConstraint' p1 p2 where
  EqConstraint p1 p2 = EqConstraint' (min p1 p2) (max p1 p2)

instance Pretty EqConstraint where
  pretty (EqConstraint p1 p2) = Text.concat [pretty p1, "=", pretty p2]

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
-- 3) Multiplied: Duplicates have been made of the hyperedge, and intersections performed, so that
--                it is guaranteed that, for each choice of term and the end of the left path,
--                there will be an equal term possible at the right edge. This enables
--                both efficient generation and counting.
--
-- The constraints being reduced is a property of the entire hyperedge, not of the individual constraints.
-- This is because reducing one constraint may result in another constraint becoming unreduced,
-- similar to how, in classic constraint propagation, one cannot process all constraints in a fixed linear order.
--
-- Example: Consider the hyperedge with children [{1,2,3}, {2,3,4}, {3,4,5}] and constraints
-- .0=.1, .1=.2. Reducing them in left-to-right order yields [{2, 3}, {3}, {3}]. The first
-- constraint would then need to be processed again to yield the fully-reduced edge [{3}, {3}, {3}].
data ECReduction = ECUnreduced | ECLeafReduced | ECMultiplied
  deriving (Eq, Ord, Show, Generic)

instance Hashable ECReduction

-- | This design has a violation of the representable/valid principle: If one constructs an FTA
-- which is already fully reduced, then reducing it will change the edgeReduction field, but leave
-- all edges the same. They will not be equal, even though the graph is identical.
data Edge = InternedEdge { edgeId        ::  !Id
                         , uninternedEdge :: !UninternedEdge
                         }

instance Show Edge where
  show e = "InternedEdge " ++ show (edgeId e) ++ " " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ " " ++ show (edgeEcs e) ++ " " ++ show (edgeReduction e)

edgeSymbol :: Edge -> Symbol
edgeSymbol = uEdgeSymbol . uninternedEdge

edgeChildren :: Edge -> [Node]
edgeChildren = uEdgeChildren . uninternedEdge

edgeEcs :: Edge -> [EqConstraint]
edgeEcs = uEdgeEcs . uninternedEdge

edgeReduction :: Edge -> ECReduction
edgeReduction = uEdgeReduction . uninternedEdge


instance Eq Edge where
  (InternedEdge {edgeId = n1}) == (InternedEdge {edgeId = n2}) = n1 == n2

instance Ord Edge where
  compare = compare `on` edgeId

instance Hashable Edge where
  hashWithSalt s e = s `hashWithSalt` (edgeId e)

----------------------
----- Nodes
----------------------

data Node = InternedNode {-# UNPACK #-} !Id ![Edge]
          | EmptyNode
  deriving ( Show )

instance Eq Node where
  (InternedNode n1 _) == (InternedNode n2 _) = n1 == n2
  EmptyNode           == EmptyNode           = True
  _                   == _                   = False

instance Ord Node where
  compare n1 n2 = compare (dropEdges n1) (dropEdges n2)
    where
      dropEdges :: Node -> Maybe Id
      dropEdges (InternedNode n _) = Just n
      dropEdges EmptyNode          = Nothing

instance Hashable Node where
  hashWithSalt s EmptyNode = s `hashWithSalt` (-1 :: Int)
  hashWithSalt s (InternedNode n _) = s `hashWithSalt` n


----------------------
------ Getters and setters
----------------------

nodeIdentity :: Node -> Id
nodeIdentity (InternedNode n _) = n

nodeEdges :: Node -> [Edge]
nodeEdges (Node es) = es
nodeEdges _         = []

setChildren :: Edge -> [Node] -> Edge
setChildren e ns = mkEdge (edgeSymbol e) ns (edgeEcs e)

-------------
------ Interning nodes
-------------

data UninternedNode = UninternedNode ![Edge]
                    | UninternedEmptyNode
  deriving ( Eq, Generic )

instance Hashable UninternedNode

instance Interned Node where
  type Uninterned  Node = UninternedNode
  data Description Node = DNode !UninternedNode
    deriving ( Eq, Generic )

  describe = DNode

  identify i (UninternedNode es) = InternedNode i es
  identify _ UninternedEmptyNode = EmptyNode

  cache = nodeCache

instance Hashable (Description Node)

nodeCache :: Cache Node
nodeCache = mkCache
{-# NOINLINE nodeCache #-}

-------------
------ Interning edges
-------------

data UninternedEdge = UninternedEdge { uEdgeSymbol    :: !Symbol
                                     , uEdgeChildren  :: ![Node]
                                     , uEdgeEcs       :: ![EqConstraint]
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

---------------------
------ Smart constructors
---------------------

pattern Edge :: Symbol -> [Node] -> Edge
pattern Edge s ns <- (InternedEdge _ (UninternedEdge s ns _ _)) where
  Edge s ns = intern $ UninternedEdge s ns [] ECUnreduced

mkEdge :: Symbol -> [Node] -> [EqConstraint] -> Edge
mkEdge s ns ecs = intern $ UninternedEdge s ns ecs ECUnreduced

{-# COMPLETE Node, EmptyNode #-}

pattern Node :: [Edge] -> Node
pattern Node es <- (InternedNode _ es) where
  Node es = case removeEmptyEdges es of
              []  -> EmptyNode
              es' -> intern $ UninternedNode $ nub $ sort es' -- TODO: Use sortUniq to eliminate a pass, ensure sort is fast for already sorted


collapseEmptyEdge :: Edge -> Maybe Edge
collapseEmptyEdge e@(Edge _ ns) = if any (== EmptyNode) ns then Nothing else Just e

---------------------------------------------------------------
------------------------- Operations --------------------------
---------------------------------------------------------------

-----------------------
------ Traversal
-----------------------

-- This name originates from the "crush" operator in the Stratego language. C.f.: the "crushtdT"
-- combinators in the KURE and compstrat libraries.
--
-- Although m is only constrained to be a monoid, crush makes no guarantees about ordering.
crush :: forall m. (Monoid m) => (Node -> m) -> Node -> m
crush f n = evalState (go n) Set.empty
  where
    go :: (Monoid m) => Node -> State (Set Id) m
    go EmptyNode = return mempty
    go n@(Node es) = do
      seen <- get
      let nId = nodeIdentity n
      if Set.member nId seen then
        return mempty
       else do
        modify (Set.insert nId)
        mappend (f n) <$> (mconcat <$> mapM (\(Edge _ ns) -> mconcat <$> mapM go ns) es)

-----------------------
------ Edge operations
-----------------------

removeEmptyEdges :: [Edge] -> [Edge]
removeEmptyEdges = filter (not . isEmptyEdge)

isEmptyEdge :: Edge -> Bool
isEmptyEdge e@(Edge _ ns) = any (== EmptyNode) ns


------------
------ Size operations
------------

nodeCount :: Node -> Int
nodeCount = getSum . crush (const $ Sum 1)

edgeCount :: Node -> Int
edgeCount = getSum . crush (\(Node es) -> Sum (length es))

------------
------ Intersect
------------

-- | NOTE: I believe there is an infinite loop lurking in this memoization, and am surprised
--   it has not yet manifested. An earlier implementation which abused the intern library
--   for memoization very much did experience this infinite loop.
--
-- The problem is in this code in memoIO:
--
--     let r = f x
--     writeIORef v (HashMap.insert x r m)
--
-- This puts the thunk "f x" as a value of the IORef v.
-- The problem is that "f x" in this case is doIntersect, which contains a recursive call to
-- intersect, which contains an unsafePerformIO of something that reads from this very same IORef.
-- There is hence an unwanted cycle in the reduction graph.

intersect :: Node -> Node -> Node
intersect = memo2 doIntersect

doIntersect :: Node -> Node -> Node
doIntersect EmptyNode _         = EmptyNode
doIntersect _         EmptyNode = EmptyNode
doIntersect n1@(Node es1) n2@(Node es2)
  | n1 == n2                            = n1
  | otherwise                           = case catMaybes [intersectEdge e1 e2 | e1 <- es1, e2 <- es2] of
                                            [] -> EmptyNode
                                            es -> Node es
  where
    intersectEdge :: Edge -> Edge -> Maybe Edge
    intersectEdge (Edge s1 _) (Edge s2 _)
      | s1 /= s2                                        = Nothing
    intersectEdge (Edge s children1) (Edge _ children2)
      | length children1 /= length children2            = error ("Different lengths encountered for children of symbol " ++ show s)
    intersectEdge e1                 e2                 =
        Just $ mkEdge (edgeSymbol e1)
                      (zipWith intersect (edgeChildren e1) (edgeChildren e2))
                      (edgeEcs e1 ++ edgeEcs e2)


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

requirePath :: Path -> Node -> Node
requirePath EmptyPath       n         = n
requirePath _               EmptyNode = EmptyNode
requirePath (ConsPath p ps) (Node es) = Node $ map (\e -> setChildren e (requirePathList (ConsPath p ps) (edgeChildren e)))
                                             $ filter (\e -> length (edgeChildren e) > p)
                                                      es

requirePathList :: Path -> [Node] -> [Node]
requirePathList EmptyPath       ns = ns
requirePathList (ConsPath p ps) ns = ns & ix p %~ requirePath ps

instance Pathable Node Node where
  getPath _                EmptyNode = EmptyNode
  getPath EmptyPath        n         = n
  getPath (ConsPath p ps) (Node es)  = union $ map (getPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns) = ns ^? ix p

  modifyAtPath f EmptyPath       n         = f n
  modifyAtPath _ _               EmptyNode = EmptyNode
  modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
    where
      goEdge :: Edge -> Edge
      goEdge e = setChildren e (edgeChildren e & ix p %~ modifyAtPath f ps)

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

---------------
--- Reduction
---------------

reducePartially :: Node -> Node
reducePartially = reduce ECLeafReduced

-- | TODO: Does reducing top-down result in a properly reduced FTA? Must one
--   reapply the top constraints? Top down is faster than bottom-up, right?
reduce :: ECReduction -> Node -> Node
reduce _   EmptyNode = EmptyNode
reduce ecr (Node es) = Node $ map (\e -> intern $ (uninternedEdge e) {uEdgeChildren = map (reduce ecr) (edgeChildren e)})
                            $ map (reduceEdgeTo ecr) es

reduceEdgeTo :: ECReduction -> Edge -> Edge
reduceEdgeTo ECUnreduced   e = e
reduceEdgeTo ECLeafReduced e = reduceEdgeIntersection e
reduceEdgeTo ECMultiplied  e = reduceEdgeMultiply e

reduceEdgeIntersection :: Edge -> Edge
reduceEdgeIntersection e | edgeReduction e == ECUnreduced = intern $ UninternedEdge (edgeSymbol e)
                                                                                    (fix (\ns' -> foldr reduceEqConstraint ns' (sort (edgeEcs e))) (edgeChildren e))
                                                                                    (edgeEcs e)
                                                                                    ECLeafReduced
reduceEdgeIntersection e                                  = e

reduceEqConstraint :: EqConstraint -> [Node] -> [Node]
reduceEqConstraint =  memo2 reduceEqConstraint'

reduceEqConstraint' :: EqConstraint -> [Node] -> [Node]
reduceEqConstraint' (EqConstraint p1 p2) ns = modifyAtPath (intersect n1) p2 $
                                              modifyAtPath (intersect n2) p1 $
                                              requirePathList p1 $
                                              requirePathList p2 $
                                              ns
  where
    n1 = getPath p1 ns
    n2 = getPath p2 ns

reduceEdgeMultiply :: Edge -> Edge
reduceEdgeMultiply = error "TODO: reduceEdgeMultiply"

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
               e <- es

               -- Very inefficient here, but easy to code
               children <- sequence $ map go (edgeChildren e)

               let res = Term (edgeSymbol e) children
               guard (all (ecSatisfied res) (edgeEcs e))
               return res




---------------------------------------------------------------
----------------------- Visualization -------------------------
---------------------------------------------------------------


data FglNodeLabel = IdLabel Id | TransitionLabel Symbol [EqConstraint]
  deriving ( Eq, Ord, Show )

toFgl :: Node -> Fgl.Gr FglNodeLabel ()
toFgl root = Fgl.mkGraph (nodeNodes ++ transitionNodes) (nodeToTransitionEdges ++ transitionToNodeEdges)
  where
    maxNodeOutdegree :: Int
    maxNodeOutdegree = getMax $ crush (\(Node es) -> Max (length es)) root

    fglNodeId :: Node -> Fgl.Node
    fglNodeId n = nodeIdentity n * (maxNodeOutdegree + 1)

    fglTransitionId :: Node -> Int -> Fgl.Node
    fglTransitionId n i = nodeIdentity n * (maxNodeOutdegree + 1) + (i + 1)

    nodeNodes, transitionNodes :: [Fgl.LNode FglNodeLabel]
    nodeNodes       = crush (\n@(Node _)  -> [(fglNodeId n, IdLabel $ nodeIdentity n)]) root
    transitionNodes = crush (\n@(Node es) -> imap (\i e -> (fglTransitionId n i, TransitionLabel (edgeSymbol e) (edgeEcs e))) es) root

    nodeToTransitionEdges, transitionToNodeEdges :: [Fgl.LEdge ()]
    nodeToTransitionEdges = crush (\n@(Node es) -> imap (\i _ -> (fglNodeId n, fglTransitionId n i, ())) es) root
    transitionToNodeEdges = crush (\n@(Node es) -> concat $
                                                     imap (\i e ->
                                                              map (\n' -> (fglTransitionId n i, fglNodeId n', ())) (edgeChildren e)
                                                           )
                                                           es)
                                  root

fglToDot :: Fgl.Gr FglNodeLabel () -> Dot.Graph
fglToDot g = Dot.Graph Dot.StrictGraph Dot.DirectedGraph Nothing (nodeStmts ++ edgeStmts)
  where
    nodeStmts :: [Dot.Statement]
    nodeStmts = map renderNode  $ Fgl.labNodes g

    edgeStmts :: [Dot.Statement]
    edgeStmts = map renderEdge $ Fgl.labEdges g

    renderNode :: Fgl.LNode FglNodeLabel -> Dot.Statement
    renderNode (fglId, l) = Dot.NodeStatement (Dot.NodeId (Dot.IntegerId $ toInteger fglId) Nothing)
                                              [ Dot.AttributeSetValue (Dot.NameId "label") (renderNodeLabel l)
                                              , Dot.AttributeSetValue (Dot.NameId "shape")
                                                                      (case l of
                                                                        IdLabel _           -> Dot.StringId "ellipse"
                                                                        TransitionLabel _ _ -> Dot.StringId "box")
                                              ]

    renderEdge :: Fgl.LEdge () -> Dot.Statement
    renderEdge (a, b, _) = Dot.EdgeStatement [ea, eb] []
      where
        ea = Dot.ENodeId Dot.NoEdge       (Dot.NodeId (Dot.IntegerId $ toInteger a) Nothing)
        eb = Dot.ENodeId Dot.DirectedEdge (Dot.NodeId (Dot.IntegerId $ toInteger b) Nothing)

    renderNodeLabel :: FglNodeLabel -> Dot.Id
    renderNodeLabel (IdLabel l)             = Dot.StringId ("q" ++ show l)
    renderNodeLabel (TransitionLabel s ecs) = Dot.StringId (Text.unpack (pretty s)
                                                            ++ Text.unpack (Text.concat $ map (Text.append "," . pretty) ecs))

-- | To visualize an FTA:
-- 1) Call `prettyPrintDot $ toDot fta` from GHCI
-- 2) Copy the output to viz-js.jom or another GraphViz implementation
toDot :: Node -> Dot.Graph
toDot = fglToDot . toFgl


---------------------------------------------------------------
------------------------- Debugging ---------------------------
---------------------------------------------------------------


-- | This should be the identity operation. If not, something has gone wrong.
refreshNode :: Node -> Node
refreshNode EmptyNode = EmptyNode
refreshNode (Node es) = Node (map refreshEdge es)

-- | This should be the identity operation. If not, something has gone wrong.
refreshEdge :: Edge -> Edge
refreshEdge e = reduceEdgeTo (edgeReduction e) $ setChildren e (map refreshNode (edgeChildren e))