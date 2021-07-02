{-# LANGUAGE OverloadedStrings #-}

module Internal.ECTA (
    Symbol(.., Symbol)

  , Term(..)

  , Edge(.., Edge)
  , mkEdge
  , emptyEdge
  , edgeChildren
  , edgeEcs
  , edgeSymbol
  , setChildren

  , Node(.., Node)
  , nodeEdges
  , createGloballyUniqueMu

  -- * Operations
  , pathsMatching
  , mapNodes
  , crush
  , nodeCount
  , edgeCount
  , union
  , intersect
  , intersectEdge
  , requirePath
  , requirePathList
  , denotation

  , reducePartially
  , reduce
  , reduceEdgeTo
  , reduceEdgeIntersection
  , reduceEqConstraints

  -- * Visualization / debugging
  , toDot
  , refreshNode
  , refreshEdge
  ) where

import Control.Monad ( guard, liftM )
import Control.Monad.State ( evalState, State, MonadState(..), modify, execState )
import Data.Function ( on )
import Data.List ( inits, intercalate, nub, sort, tails )
import           Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes, isJust, fromJust, maybeToList )
import Data.Monoid ( Monoid(..), Sum(..), First(..) )
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
import qualified Data.HashSet as HashSet
import qualified Data.Interned as OrigInterned
import Data.Interned.Text ( InternedText, internedTextId )
import Data.List.Index ( imap )

import qualified Language.Dot.Syntax as Dot

--import Data.Interned ( Interned(..), unintern, Id, Cache, mkCache )
import Data.Interned.Extended.HashTableBased
--import Data.Interned.Extended.SingleThreaded ( intern )

import Data.Memoization ( MemoCacheTag(..), memo2 )
import Paths
import Pretty
import Utilities

-------------------------------------------------------------------------------


---------------------------------------------------------------
---------------------- Misc / general -------------------------
---------------------------------------------------------------

square :: (Num a) => a -> a
square x = x * x

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
  show (Symbol it) = show it

instance Hashable Symbol where
  hashWithSalt s (Symbol' t) = s `hashWithSalt` (internedTextId t)

instance IsString Symbol where
  fromString = Symbol . fromString

data Term = Term Symbol [Term]
  deriving ( Eq, Ord, Show, Generic )

instance Hashable Term

instance Pretty Term where
  pretty (Term s []) = pretty s
  pretty (Term s ts) = pretty s <> "(" <> (Text.intercalate "," $ map pretty ts) <> ")"

---------------------
------ Term ops
---------------------

instance Pathable Term Term where
  type Emptyable Term = Maybe Term

  getPath EmptyPath       t           = Just t
  getPath (ConsPath p ps) (Term _ ts) = case ts ^? ix p of
                                          Nothing -> Nothing
                                          Just t  -> getPath ps t

  getAllAtPath p t = maybeToList $ getPath p t

  modifyAtPath f EmptyPath       t           = f t
  modifyAtPath f (ConsPath p ps) (Term s ts) = Term s (ts & ix p %~ modifyAtPath f ps)

---------------------------------------------------------------
------------------- Data type and interning -------------------
---------------------------------------------------------------

----------------------
----- Edges
----------------------


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
data Edge = InternedEdge { edgeId        ::  !Id
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

----------------------
----- Nodes
----------------------

-- | Super hacky and restricted implementation of cyclic terms:
-- Assumes a single globally unique recursive node
data Node = InternedNode {-# UNPACK #-} !Id ![Edge]
          | EmptyNode
          | Mu Node
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

nodeEdges :: Node -> [Edge]
nodeEdges (Node es) = es
nodeEdges (Mu n)    = nodeEdges (unfoldRec n)
nodeEdges _         = []

setChildren :: Edge -> [Node] -> Edge
setChildren e ns = mkEdge (edgeSymbol e) ns (edgeEcs e)

dropEcs :: Edge -> Edge
dropEcs e = Edge (edgeSymbol e) (edgeChildren e)

-------------
------ Interning nodes
-------------

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

-------------
------ Interning edges
-------------

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

---------------------
------ Smart constructors
---------------------

pattern Edge :: Symbol -> [Node] -> Edge
pattern Edge s ns <- (InternedEdge _ (UninternedEdge s ns _ _)) where
  Edge s ns = intern $ UninternedEdge s ns EmptyConstraints ECUnreduced

emptyEdge :: Edge
emptyEdge = Edge "" [EmptyNode]

mkEdge :: Symbol -> [Node] -> EqConstraints -> Edge
mkEdge s ns ecs
   | constraintsAreContradictory ecs = emptyEdge
mkEdge s ns ecs
   | otherwise                       = intern $ UninternedEdge s ns ecs ECUnreduced -- | TODO: Reduce work on nub/sort

{-# COMPLETE Node, EmptyNode, Mu, Rec #-}

pattern Node :: [Edge] -> Node
pattern Node es <- (InternedNode _ es) where
  Node es = case removeEmptyEdges es of
              []  -> EmptyNode
              es' -> intern $ UninternedNode $ nub $ sort es' -- TODO: Use sortUniq to eliminate a pass, ensure sort is fast for already sorted

createGloballyUniqueMu :: (Node -> Node) -> Node
createGloballyUniqueMu f = Mu (f Rec)

collapseEmptyEdge :: Edge -> Maybe Edge
collapseEmptyEdge e@(Edge _ ns) = if any (== EmptyNode) ns then Nothing else Just e

---------------------------------------------------------------
------------------------- Operations --------------------------
---------------------------------------------------------------

-----------------------
------ Traversal
-----------------------

-- | Warning: Linear in number of paths, exponential in size of graph.
--   Only use for very small graphs.
pathsMatching :: (Node -> Bool) -> Node -> [Path]
pathsMatching f   EmptyNode = []
pathsMatching f   (Mu _)    = [] -- | Unsound!
pathsMatching f n@(Node es) = (concat $ map pathsMatchingEdge es)
                              ++ if f n then [EmptyPath] else []
  where
    pathsMatchingEdge :: Edge -> [Path]
    pathsMatchingEdge (Edge _ ns) = concat $ imap (\i x -> map (ConsPath i) $ pathsMatching f x) ns

mapNodes :: (Node -> Node) -> Node -> Node
mapNodes f EmptyNode = f EmptyNode
mapNodes f (Node es) = f $ Node (map (\(Edge s ns) -> Edge s (map (mapNodes f) ns)) es)
mapNodes f (Mu n)    = f (Mu (mapNodes f n))
mapNodes f Rec       = f Rec

unfoldRec :: Node -> Node
unfoldRec n = mapNodes (\x -> if x == Rec then Mu n else x) n

-- This name originates from the "crush" operator in the Stratego language. C.f.: the "crushtdT"
-- combinators in the KURE and compstrat libraries.
--
-- Although m is only constrained to be a monoid, crush makes no guarantees about ordering.
crush :: forall m. (Monoid m) => (Node -> m) -> Node -> m
crush f n = evalState (go n) Set.empty
  where
    go :: (Monoid m) => Node -> State (Set Id) m
    go EmptyNode = return mempty
    go Rec       = return mempty
    go (Mu n)    = go n
    go n@(Node es) = do
      seen <- get
      let nId = nodeIdentity n
      if Set.member nId seen then
        return mempty
       else do
        modify (Set.insert nId)
        mappend (f n) <$> (mconcat <$> mapM (\(Edge _ ns) -> mconcat <$> mapM go ns) es)

annotate :: (m -> m -> m) -> (Symbol -> [m] -> m) -> Node -> Map.Map Node m
annotate merge f n = execState (go n) Map.empty
  where
    go EmptyNode = return ()
    go Rec       = return ()
    go (Mu n)    = go n
    go n@(Node es) = do
      seen <- get
      if Map.member n seen then return () else
        do
          value <-
            foldl1 merge <$>
            mapM (\(Edge s ns) -> do
                     mapM_ go ns
                     seen <- get
                     return (f s $ map (seen !) ns))
            es
          put $ Map.insert n value seen

-----------------------
------ Edge operations
-----------------------

removeEmptyEdges :: [Edge] -> [Edge]
removeEmptyEdges = filter (not . isEmptyEdge)

isEmptyEdge :: Edge -> Bool
isEmptyEdge e@(Edge _ ns) = any (== EmptyNode) ns

edgeSubsumed :: Edge -> Edge -> Bool
edgeSubsumed e1 e2 =    (dropEcs e1 == dropEcs e2)
                     && constraintsImply (edgeEcs e1) (edgeEcs e2)


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

intersect :: Node -> Node -> Node
intersect = memo2 (NameTag "intersect") doIntersect

doIntersect :: Node -> Node -> Node
doIntersect EmptyNode _         = EmptyNode
doIntersect _         EmptyNode = EmptyNode
doIntersect (Mu n)    (Mu _)    = Mu n -- | And here I use the crazy "globally unique mu" assumption
doIntersect (Mu n1)   n2        = doIntersect (unfoldRec n1) n2
doIntersect n1        (Mu n2)   = doIntersect n1             (unfoldRec n2)
doIntersect n1@(Node es1) n2@(Node es2)
  | n1 == n2                            = n1
  | otherwise                           = case catMaybes [intersectEdge e1 e2 | e1 <- es1, e2 <- es2] of
                                            [] -> EmptyNode
                                            es -> Node $ dropRedundantEdges es
  where
    dropRedundantEdges :: [Edge] -> [Edge]
    -- | TODO: WARNING WARNING DANGER WILL ROBINSON. This uses an internal detail
    -- about EqConstraints (being sorted lists) to know that, if ecs1 has a subset of the constraints of ecs2,
    -- then ecs1 < ecs2
    dropRedundantEdges es = dropRedundantEdges' $ reverse $ sort es
      where
        -- Optimization idea: Some of these equality checks are already done in sort
        dropRedundantEdges' (e:es) = if any (\e' -> e `edgeSubsumed` e') es then
                                       dropRedundantEdges es
                                     else
                                       e : dropRedundantEdges es
        dropRedundantEdges' []     = []

doIntersect n1 n2 = error ("Unexpected " ++ show n1 ++ " " ++ show n2)


intersectEdge :: Edge -> Edge -> Maybe Edge
intersectEdge (Edge s1 _) (Edge s2 _)
  | s1 /= s2                                        = Nothing
intersectEdge (Edge s children1) (Edge _ children2)
  | length children1 /= length children2            = error ("Different lengths encountered for children of symbol " ++ show s)
intersectEdge e1                 e2                 =
    Just $ mkEdge (edgeSymbol e1)
                  (zipWith intersect (edgeChildren e1) (edgeChildren e2))
                  (edgeEcs e1 `combineEqConstraints` edgeEcs e2)

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
requirePath p               (Mu n)    = requirePath p (unfoldRec n)
requirePath (ConsPath p ps) (Node es) = Node $ map (\e -> setChildren e (requirePathList (ConsPath p ps) (edgeChildren e)))
                                             $ filter (\e -> length (edgeChildren e) > p)
                                                      es

requirePathList :: Path -> [Node] -> [Node]
requirePathList EmptyPath       ns = ns
requirePathList (ConsPath p ps) ns = ns & ix p %~ requirePath ps

instance Pathable Node Node where
  type Emptyable Node = Node

  getPath _                EmptyNode = EmptyNode
  getPath p                (Mu n)    = getPath p (unfoldRec n)
  getPath EmptyPath        n         = n
  getPath (ConsPath p ps) (Node es)  = union $ map (getPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns) = ns ^? ix p

  getAllAtPath _               EmptyNode = []
  getAllAtPath p               (Mu n)    = getAllAtPath p (unfoldRec n)
  getAllAtPath EmptyPath       n         = [n]
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
reduce _   (Mu n)    = Mu n
reduce ecr (Node es) = Node $ map (\e -> intern $ (uninternedEdge e) {uEdgeChildren = map (reduce ecr) (edgeChildren e)})
                            $ map (reduceEdgeTo ecr) es

reduceEdgeTo :: ECReduction -> Edge -> Edge
reduceEdgeTo ECUnreduced   e = e
reduceEdgeTo ECLeafReduced e = reduceEdgeIntersection e
reduceEdgeTo ECMultiplied  e = reduceEdgeMultiply e

reduceEdgeIntersection :: Edge -> Edge
reduceEdgeIntersection e = mkEdge (edgeSymbol e)
                                  (reduceEqConstraints (edgeEcs e) (edgeChildren e))
                                  (edgeEcs e)

reduceEqConstraints :: EqConstraints -> [Node] -> [Node]
reduceEqConstraints = memo2 (NameTag "reduceEqConstraints") go
  where
    propagateEmptyNodes :: [Node] -> [Node]
    propagateEmptyNodes ns = if any (==EmptyNode) ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> [Node] -> [Node]
    go ecs origNs = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        eclasses = unsafeSubsumptionOrderedEclasses ecs

        withNeededChildren = foldr requirePathList origNs (concatMap unPathEClass eclasses)

        intersectList :: [Node] -> Node
        intersectList ns = foldr intersect (head ns) (tail ns)

        atPaths :: [Node] -> [Path] -> [Node]
        atPaths ns ps = map (\p -> getPath p ns) ps

        reduceEClass :: PathEClass -> [Node] -> [Node]
        reduceEClass pec ns = foldr (\(p, nsRestIntersected) ns' -> modifyAtPath (intersect nsRestIntersected) p ns')
                                    ns
                                    (zip ps (toIntersect ns ps))
          where
            ps = unPathEClass pec

        toIntersect :: [Node] -> [Path] -> [Node]
        toIntersect ns ps = map intersectList $ dropOnes $ map (flip getPath ns) ps

        -- | dropOnes [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]
        dropOnes :: [a] -> [[a]]
        dropOnes xs = zipWith (++) (inits xs) (tail $ tails xs)

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

    -- | Note that this code uses the decision that f(a,a) does not satisfy the constraint 0.0=1.0 because those paths are empty.
    --   It would be equally valid to say that it does.
    ecsSatisfied :: Term -> EqConstraints -> Bool
    ecsSatisfied t ecs = all (\ps -> all (\p' -> isJust (getPath (head ps) t) && getPath (head ps) t == getPath p' t) ps)
                             (map unPathEClass $ unsafeGetEclasses ecs)

    go :: Node -> [Term]
    go n = case n of
             EmptyNode -> []
             Mu _ -> [Term "Mu" []] -- | HAX!
             Node es -> do
               e <- es

               -- Very inefficient here, but easy to code
               children <- sequence $ map go (edgeChildren e)

               let res = Term (edgeSymbol e) children
               guard $ ecsSatisfied res (edgeEcs e)
               return res




---------------------------------------------------------------
----------------------- Visualization -------------------------
---------------------------------------------------------------


data FglNodeLabel = IdLabel Id | TransitionLabel Symbol EqConstraints
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

    fglNodeLabel :: Node -> Maybe (Fgl.LNode FglNodeLabel)
    fglNodeLabel n@(Node _) = Just (fglNodeId n, IdLabel $ nodeIdentity n)
    fglNodeLabel _          = Nothing

    onNormalNodes :: (Monoid a) => (Node -> a) -> (Node -> a)
    onNormalNodes f n@(Node _) = f n
    onNormalNodes f _          = mempty

    nodeNodes, transitionNodes :: [Fgl.LNode FglNodeLabel]
    nodeNodes       = crush (maybeToList . fglNodeLabel) root
    transitionNodes = crush (onNormalNodes $ \n@(Node es) -> imap (\i e -> (fglTransitionId n i, TransitionLabel (edgeSymbol e) (edgeEcs e))) es) root

    -- | Uses the globally-unique mu node assumption
    -- Does not work if root is the mu node
    muNodeLabel :: Maybe Fgl.Node
    muNodeLabel = getFirst $ crush (\(Node es) -> foldMap (\(Edge _ ns) -> foldMap muNodeToLabel ns) es) root
      where
        muNodeToLabel (Mu n) = First $ Just $ fglNodeId n
        muNodeToLabel _      = First Nothing

    nodeToTransitionEdges, transitionToNodeEdges :: [Fgl.LEdge ()]
    nodeToTransitionEdges = crush (onNormalNodes $ \n@(Node es) -> imap (\i _ -> (fglNodeId n, fglTransitionId n i, ())) es) root
    transitionToNodeEdges = crush (onNormalNodes $ \n@(Node es) -> concat $
                                                                      imap (\i e ->
                                                                              map (edgeTo n i) (edgeChildren e)
                                                                           )
                                                                           es)
                                  root
      where
        edgeTo :: Node -> Int -> Node -> Fgl.LEdge ()
        edgeTo n i n'@(Node _) = (fglTransitionId n i, fglNodeId n', ())
        edgeTo n i n'@(Mu _)   = (fglTransitionId n i, fromJust muNodeLabel, ())
        edgeTo n i    Rec      = (fglTransitionId n i, fromJust muNodeLabel, ())


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
    renderNodeLabel (TransitionLabel s ecs) =
         Dot.StringId (Text.unpack $ pretty s <> " (" <> pretty ecs <> ")")

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
refreshNode (Mu n)    = Mu (refreshNode n)
refreshNode Rec       = Rec

-- | This should be the identity operation. If not, something has gone wrong.
refreshEdge :: Edge -> Edge
refreshEdge e = reduceEdgeTo (edgeReduction e) $ setChildren e (map refreshNode (edgeChildren e))
