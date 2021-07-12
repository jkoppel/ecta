{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Data.ECTA.Internal.ECTA (
    nubById

  , Edge(.., Edge)
  , mkEdge
  , emptyEdge
  , edgeChildren
  , edgeEcs
  , edgeSymbol
  , setChildren

  , Node(.., Node)
  , nodeIdentity
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
  , dropRedundantEdges
  , intersectEdge

  , requirePath
  , requirePathList

  , TermFragment(..)
  , termFragToTruncatedTerm

  , SuspendedConstraint(..)
  , descendScs
  , UVarValue(..)

  , EnumerationState(..)
  , uvarCounter
  , uvarRepresentative
  , uvarValues
  , initEnumerationState


  , EnumerateM
  , getUVarRepresentative
  , assimilateUvarVal
  , mergeNodeIntoUVarVal
  , getUVarValue
  , getTermFragForUVar
  , runEnumerateM


  , enumerateNode
  , enumerateEdge
  , firstExpandableUVar
  , enumerateOutUVar
  , enumerateOutFirstExpandableUVar
  , enumerateFully
  , expandTermFrag
  , expandUVar

  , getAllTruncatedTerms
  , naiveDenotation

  , withoutRedundantEdges
  , reducePartially
  , reduceEdgeIntersection
  , reduceEqConstraints

  -- * Visualization / debugging
  , toDot
#ifdef PROFILE_CACHES
  , resetAllEctaCaches_BrokenDoNotUse
#endif
  , getSubnodeById
  ) where

import Control.Monad ( mzero, forM_, guard, void )
import Control.Monad.State.Strict ( StateT(..), evalState, State, MonadState(..), modify )
import Control.Monad.ST ( ST, runST )
import Control.Monad.Trans ( lift )
import Data.Foldable ( foldrM )
import Data.Function ( on )
import qualified Data.IntMap as IntMap
import Data.List ( inits, intercalate, nub, sort, tails )
import Data.Maybe ( catMaybes, fromMaybe, isJust, fromJust, maybeToList )
import Data.Monoid ( Any(..), Monoid(..), Sum(..), First(..) )
import Data.Semigroup ( Max(..) )
import Data.Sequence ( Seq((:<|), (:|>)) )
import qualified Data.Sequence as Sequence
import           Data.Set ( Set )
import qualified Data.Set as Set
import Data.Text ( Text )
import qualified Data.Text as Text
import Debug.Trace ( trace )

import GHC.Generics ( Generic )

import Control.Lens ( use, (&), ix, _1, (^?), (%~), (%=), (.=) )
import Control.Lens.TH ( makeLenses )

import qualified Data.Graph.Inductive as Fgl
import Data.Hashable ( Hashable(..) )
import qualified Data.HashSet as HashSet
import qualified Data.HashTable.ST.Basic as HT
import Data.List.Extra ( nubSort )
import Data.List.Index ( imap, imapM )

import qualified Language.Dot.Syntax as Dot

-- | Switch the comments on these lines to switch to ekmett's original `intern` library
--   instead of our single-threaded hashtable-based reimplementation.
import Data.Interned.Extended.HashTableBased as Interned
--import Data.Interned ( Interned(..), unintern, Id, Cache, mkCache )
--import Data.Interned.Extended.SingleThreaded ( intern )

import Data.ECTA.Paths
import Data.ECTA.Term
import Data.ECTA.Utilities
import Data.Memoization ( MemoCacheTag(..), memo, memo2 )
import qualified Data.Memoization as Memoization
import Data.Persistent.UnionFind ( UnionFind, UVar, uvarToInt, intToUVar, UVarGen )
import qualified Data.Persistent.UnionFind as UnionFind
import Data.Text.Extended.Pretty

-------------------------------------------------------------------------------


---------------------------------------------------------------
---------------------- Misc / general -------------------------
---------------------------------------------------------------

square :: (Num a) => a -> a
square x = x * x

traceFn :: (a -> String) -> a -> a
traceFn f x = trace (f x) x

----------
--- Hash join / clustering / nub
----------


-- | PRECONDITION: (h x == h y) => x == y
nubById :: (a -> Int) -> [a] -> [a]
nubById _ [x] = [x]
nubById h ls = runST $ do
    ht <- HT.newSized 101
    mapM_ (\x -> HT.insert ht (h x) x) ls
    HT.foldM (\res (_, v) -> return $ v : res) [] ht

nubByIdSinglePass :: forall a. (a -> Int) -> [a] -> [a]
nubByIdSinglePass _ [x] = [x]
nubByIdSinglePass h ls = runST (go ls [] =<< HT.new)
  where
    go :: [a] -> [a] -> HT.HashTable s Int Bool -> ST s [a]
    go []     acc    _  = return acc
    go (x:xs) acc ht = do alreadyPresent <- HT.mutate ht
                                                      (h x)
                                                      (\case Nothing -> (Just True, False)
                                                             Just _  -> (Just True, True))
                          if alreadyPresent then
                            go xs acc ht
                          else
                            go xs (x:acc) ht


maybeAddToHt :: v -> Maybe [v] -> (Maybe [v], ())
maybeAddToHt v = \case Nothing -> (Just [v], ())
                       Just vs -> (Just (v : vs), ())

-- This is testing slower than running clusterByHash and nubByIdSinglePass separately. How?
hashClusterIdNub :: (Interned a) => (a -> Int) -> (a -> Int) -> [a] -> [[a]]
hashClusterIdNub _ _ [x] = [[x]]
hashClusterIdNub hCluster hNub ls = runST $ do
    clusters <- HT.new
    seen <- HT.new

    forM_ ls $ \x -> do
      alreadyPresent <- HT.mutate seen
                                  (hNub x)
                                  (\case Nothing -> (Just True, False)
                                         Just _  -> (Just True, True))
      if alreadyPresent then
        return ()
       else do
        void $ HT.mutate clusters (hCluster x) (maybeAddToHt x)

    HT.foldM (\res (_, vs) -> return $ vs : res) [] clusters

clusterByHash :: (a -> Int) -> [a] -> [[a]]
clusterByHash h ls = runST $ do
    ht <- HT.new
    mapM_ (\x -> HT.mutate ht (h x) (maybeAddToHt x)) ls
    HT.foldM (\res (_, vs) -> return $ vs : res) [] ht

hashJoin :: (a -> Int) -> (a -> a -> b) -> [a] -> [a] -> [b]
hashJoin h j l1 l2 = runST $ do
    ht2 <- HT.new
    mapM_ (\x -> HT.mutate ht2 (h x) (maybeAddToHt x)) l2
    foldrM (\x res -> do maybeCluster <- HT.lookup ht2 (h x)
                         case maybeCluster of
                           Nothing  -> return res
                           Just vs2 -> return $ [j x v2 | v2 <- vs2] ++ res )
           []
           l1

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

----------------------
----- Nodes
----------------------

-- | Super hacky and restricted implementation of cyclic terms:
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
   | otherwise                       = intern $ UninternedEdge s ns ecs ECUnreduced

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

mapNodes ::(Node -> Node) -> Node -> Node
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
    go (Mu n)    = mappend (f (Mu n)) <$> go n
    go n@(Node es) = do
      seen <- get
      let nId = nodeIdentity n
      if Set.member nId seen then
        return mempty
       else do
        modify (Set.insert nId)
        mappend (f n) <$> (mconcat <$> mapM (\(Edge _ ns) -> mconcat <$> mapM go ns) es)

onNormalNodes :: (Monoid m) => (Node -> m) -> (Node -> m)
onNormalNodes f n@(Node _) = f n
onNormalNodes _ _          = mempty

-----------------------
------ Folding
-----------------------

unfoldRec :: Node -> Node
unfoldRec = memo (NameTag "unfoldRec") go
  where
    go n = mapNodes (\x -> if x == Rec then Mu n else x) n

refold :: Node -> Node
refold n = let muNode = getFirst $ crush (\case Mu x -> First (Just x)
                                                _    -> First Nothing)
                                         n
           in case muNode of
                Nothing     -> n
                Just m -> let unfoldedNode = unfoldRec m
                          in fixUnbounded (mapNodes (\x -> if x == unfoldedNode then Mu m else x)) n

unfoldBounded :: Int -> Node -> Node
unfoldBounded 0 = mapNodes (\case Mu _ -> EmptyNode
                                  n    -> n)
unfoldBounded k = unfoldBounded (k-1) . mapNodes (\case Mu n -> unfoldRec n
                                                        n    -> n)

-----------------------
------ Edge operations
-----------------------

removeEmptyEdges :: [Edge] -> [Edge]
removeEmptyEdges = filter (not . isEmptyEdge)

isEmptyEdge :: Edge -> Bool
isEmptyEdge e@(Edge _ ns) = any (== EmptyNode) ns

edgeSubsumed :: Edge -> Edge -> Bool
edgeSubsumed e1 e2 = intersectEdge e1 e2 == Just e1


------------
------ Size operations
------------

nodeCount :: Node -> Int
nodeCount = getSum . crush (onNormalNodes $ const $ Sum 1)

edgeCount :: Node -> Int
edgeCount = getSum . crush (onNormalNodes $ \(Node es) -> Sum (length es))

maxIndegree :: Node -> Int
maxIndegree = getMax . crush (onNormalNodes $ \(Node es) -> Max (length es))

------------
------ Membership
------------

nodeRepresents :: Node -> Term -> Bool
nodeRepresents EmptyNode _                      = False
nodeRepresents (Node es) t                      = any (\e -> edgeRepresents e t) es
nodeRepresents (Mu n)    t                      = nodeRepresents (unfoldRec n) t
nodeRepresents _         _                      = False

edgeRepresents :: Edge -> Term -> Bool
edgeRepresents e t@(Term s ts) =    s == edgeSymbol e
                                 && and (zipWith nodeRepresents (edgeChildren e) ts)
                                 && all (eclassSatisfied t) (unsafeGetEclasses $ edgeEcs e)
  where
    eclassSatisfied :: Term -> PathEClass -> Bool
    eclassSatisfied t pec = allTheSame $ map (\p -> getPath p t) $ unPathEClass pec

    allTheSame :: (Eq a) => [a] -> Bool
    allTheSame [] = True
    allTheSame ((!x):xs) = go x xs where
        go !x [] = True
        go !x (!y:ys) = (x == y) && (go x ys)
    {-# INLINE allTheSame #-}

------------
------ Intersect
------------

intersect :: Node -> Node -> Node
intersect = memo2 (NameTag "intersect") doIntersect
{-# NOINLINE intersect #-}


-- 7/4/21: The unrolling strategy for intersection totally does not generalize beyond
-- recursive nodes which have a self cycle.
--
-- The following will enter an infinite recursion:
--  > t = createGloballyUniqueMu (\n -> Node  [Edge "a" [Node [Edge "a" [n]]]])
--  > intersect t (Node [Edge "a" [t]])
doIntersect :: Node -> Node -> Node
doIntersect EmptyNode _         = EmptyNode
doIntersect _         EmptyNode = EmptyNode
doIntersect (Mu n)    (Mu _)    = Mu n -- | And here I use the crazy "globally unique mu" assumption
doIntersect (Mu n1)   n2        = doIntersect (unfoldRec n1) n2
doIntersect n1        (Mu n2)   = doIntersect n1             (unfoldRec n2)
doIntersect n1@(Node es1) n2@(Node es2)
  | n1 == n2                            = n1
  | n2 <  n1                            = intersect n2 n1
                                          -- | `hash` gives a unique ID of the symbol because they're interned
  | otherwise                           = let joined = hashJoin (hash . edgeSymbol) intersectEdgeSameSymbol es1 es2
                                          in Node joined
                                             --Node $ dropRedundantEdges joined
                                             --mkNodeAlreadyNubbed $ dropRedundantEdges joined
doIntersect n1 n2 = error ("doIntersect: Unexpected " ++ show n1 ++ " " ++ show n2)


nodeDropRedundantEdges :: Node -> Node
nodeDropRedundantEdges (Node es) = Node $ dropRedundantEdges es

data RuleOutRes = Keep | RuledOutBy Edge

dropRedundantEdges :: [Edge] -> [Edge]
dropRedundantEdges origEs = concatMap reduceCluster $ {- traceShow (map (\es -> (length es, edgeSymbol $ head es)) clusters, length $ concatMap reduceCluster clusters)-} clusters
  where
    clusters = map (nubByIdSinglePass edgeId) $ clusterByHash (hash . edgeSymbol) origEs

    reduceCluster :: [Edge] -> [Edge]
    reduceCluster []     = []
    reduceCluster (e:es) = case ruleOut e es of
                             -- Optimization: If e' > e, likely to be greater than other things;
                             -- move it to front and rule out more stuff next iteration.
                             --
                             -- No noticeable difference in overall wall clock time (7/2/21),
                             -- but a few % reduction in calls to intersectEdgeSameSymbol
                             (RuledOutBy e', es') -> reduceCluster (e':es')
                             (Keep, es') -> e : reduceCluster es'

    ruleOut :: Edge -> [Edge] -> (RuleOutRes, [Edge])
    ruleOut e []     = (Keep, [])
    ruleOut e (x:xs) = let e' = intersectEdgeSameSymbol e x in
                       if e' == x then
                         ruleOut e xs
                       else if e' == e then
                         (RuledOutBy x, xs)
                       else
                         let (res, notRuledOut) = ruleOut e xs
                         in (res, x : notRuledOut)

intersectEdge :: Edge -> Edge -> Maybe Edge
intersectEdge e1 e2
  | edgeSymbol e1 /= edgeSymbol e2 = Nothing
  | otherwise                      = Just $ intersectEdgeSameSymbol e1 e2

intersectEdgeSameSymbol :: Edge -> Edge -> Edge
intersectEdgeSameSymbol = memo2 (NameTag "intersectEdgeSameSymbol") go
  where
    go e1          e2
      | e2 < e1                                         = intersectEdgeSameSymbol e2 e1
#ifdef DEFENSIVE_CHECKS
    go (Edge s children1) (Edge _ children2)
      | length children1 /= length children2            = error ("Different lengths encountered for children of symbol " ++ show s)
#endif
    go e1                 e2                 =
        mkEdge (edgeSymbol e1)
               (zipWith intersect (edgeChildren e1) (edgeChildren e2))
               (edgeEcs e1 `combineEqConstraints` edgeEcs e2)
{-# NOINLINE intersectEdgeSameSymbol #-}

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
------ Reduction
------------------------------------

withoutRedundantEdges :: Node -> Node
withoutRedundantEdges n = mapNodes dropReds n
  where
    dropReds (Node es) = Node (dropRedundantEdges es)
    dropReds x         = x


---------------
--- Reducing Equality Constraints
---------------

reducePartially :: Node -> Node
reducePartially = memo (NameTag "reducePartially") go
  where
    go :: Node -> Node
    go EmptyNode  = EmptyNode
    go (Mu n)     = Mu n
    go n@(Node _) = modifyNode n $ \es -> map (\e -> intern $ (uninternedEdge e) {uEdgeChildren = map reducePartially (edgeChildren e)})
                                          $ map reduceEdgeIntersection es
{-# NOINLINE reducePartially #-}

reduceEdgeIntersection :: Edge -> Edge
reduceEdgeIntersection = memo (NameTag "reduceEdgeIntersection") go
  where
   go :: Edge -> Edge
   go e = mkEdge (edgeSymbol e)
                 (reduceEqConstraints (edgeEcs e) (edgeChildren e))
                 (edgeEcs e)
{-# NOINLINE reduceEdgeIntersection #-}

reduceEqConstraints :: EqConstraints -> [Node] -> [Node]
reduceEqConstraints = go
  where
    propagateEmptyNodes :: [Node] -> [Node]
    propagateEmptyNodes ns = if any (==EmptyNode) ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> [Node] -> [Node]
    go ecs origNs = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        eclasses = unsafeSubsumptionOrderedEclasses ecs

        -- | TODO: Replace with a "requirePathTrie"
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
        --toIntersect ns ps = replicate (length ps) $ intersectList $ map (nodeDropRedundantEdges . flip getPath ns) ps
        --toIntersect ns ps = map intersectList $ dropOnes $ map (nodeDropRedundantEdges . flip getPath ns) ps
        --toIntersect ns ps = replicate (length ps) $ intersectList $ map (flip getPath ns) ps
        toIntersect ns ps = map intersectList $ dropOnes $ map (flip getPath ns) ps

        -- | dropOnes [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]
        dropOnes :: [a] -> [[a]]
        dropOnes xs = zipWith (++) (inits xs) (tail $ tails xs)


------------------------------------
------ Denotation/enumeration
------------------------------------


---------------------
-------- Enumeration state
---------------------


data TermFragment = TermFragmentNode !Symbol ![TermFragment]
                  | TermFragmentUVar UVar
  deriving ( Eq, Ord, Show )

termFragToTruncatedTerm :: TermFragment -> Term
termFragToTruncatedTerm (TermFragmentNode s ts) = Term s (map termFragToTruncatedTerm ts)
termFragToTruncatedTerm (TermFragmentUVar uv)   = Term (Symbol $ "v" <> Text.pack (show $ uvarToInt uv)) []

data SuspendedConstraint = SuspendedConstraint !PathTrie !UVar
  deriving ( Eq, Ord, Show )

scGetPathTrie :: SuspendedConstraint -> PathTrie
scGetPathTrie (SuspendedConstraint pt _) = pt

scGetUVar :: SuspendedConstraint -> UVar
scGetUVar (SuspendedConstraint _ uv) = uv

descendScs :: Int -> Seq SuspendedConstraint -> Seq SuspendedConstraint
descendScs i scs = Sequence.filter (not . isEmptyPathTrie . scGetPathTrie)
                   $ fmap (\(SuspendedConstraint pt uv) -> SuspendedConstraint (pathTrieDescend pt i) uv)
                          scs

data UVarValue = UVarUnenumerated { contents    :: !(Maybe Node)
                                  , constraints :: !(Seq SuspendedConstraint)
                                  }
               | UVarEnumerated { termFragment :: !TermFragment }
               | UVarEliminated
  deriving ( Eq, Ord, Show )

intersectUVarValue :: UVarValue -> UVarValue -> UVarValue
intersectUVarValue (UVarUnenumerated mn1 scs1) (UVarUnenumerated mn2 scs2) =
  let newContents = case (mn1, mn2) of
                      (Nothing, x      ) -> x
                      (x,       Nothing) -> x
                      (Just n1, Just n2) -> Just (intersect n1 n2)
      newConstraints = scs1 <> scs2
  in UVarUnenumerated newContents newConstraints

intersectUVarValue UVarEliminated            _                         = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _                         UVarEliminated            = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _                         _                         = error "intersectUVarValue: Intersecting with enumerated value not implemented"


data EnumerationState = EnumerationState {
    _uvarCounter        :: UVarGen
  , _uvarRepresentative :: UnionFind
  , _uvarValues         :: Seq UVarValue
  }
  deriving ( Eq, Ord, Show )

makeLenses ''EnumerationState


initEnumerationState :: Node -> EnumerationState
initEnumerationState n = let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
                         in EnumerationState uvg
                                             (UnionFind.withInitialValues [uv])
                                             (Sequence.singleton (UVarUnenumerated (Just n) Sequence.Empty))


---------------------
-------- Enumeration monad and operations
---------------------


type EnumerateM = StateT EnumerationState []

runEnumerateM :: EnumerateM a -> EnumerationState -> [(a, EnumerationState)]
runEnumerateM = runStateT

nextUVar :: EnumerateM UVar
nextUVar = do c <- use uvarCounter
              let (c', uv) = UnionFind.nextUVar c
              uvarCounter .= c'
              return uv

addUVarValue :: Maybe Node -> EnumerateM UVar
addUVarValue x = do uv <- nextUVar
                    uvarValues %= (:|> (UVarUnenumerated x Sequence.Empty))
                    return uv

getUVarValue :: UVar -> EnumerateM UVarValue
getUVarValue uv = do uv' <- getUVarRepresentative uv
                     let idx = uvarToInt uv'
                     values <- use uvarValues
                     return $ Sequence.index values idx

getTermFragForUVar :: UVar -> EnumerateM TermFragment
getTermFragForUVar uv =  termFragment <$> getUVarValue uv

getUVarRepresentative :: UVar -> EnumerateM UVar
getUVarRepresentative uv = do uf <- use uvarRepresentative
                              let (uv', uf') = UnionFind.find uv uf
                              uvarRepresentative .= uf'
                              return uv'


assimilateUvarVal :: UVar -> SuspendedConstraint -> EnumerateM ()
assimilateUvarVal uvTarg (SuspendedConstraint pt uvSrc)
                                | uvTarg == uvSrc      = return ()
                                | otherwise            = do
  values <- use uvarValues
  let srcVal  = Sequence.index values (uvarToInt uvSrc)
  let targVal = Sequence.index values (uvarToInt uvTarg)
  case srcVal of
    UVarEliminated -> return () -- Happens from duplicate constraints
    _              -> do
      let v = intersectUVarValue srcVal targVal
      guard (contents v /= Just EmptyNode)
      uvarValues.(ix $ uvarToInt uvTarg) .= v
      uvarValues.(ix $ uvarToInt uvSrc)  .= UVarEliminated


mergeNodeIntoUVarVal :: UVar -> Node -> Seq SuspendedConstraint -> EnumerateM ()
mergeNodeIntoUVarVal uv n scs = do
  uv' <- getUVarRepresentative uv
  let idx = uvarToInt uv'
  uvarValues.(ix idx) %= intersectUVarValue (UVarUnenumerated (Just n) scs)
  newValues <- use uvarValues
  guard (contents (Sequence.index newValues idx) /= Just EmptyNode)

pecToSuspendedConstraint :: PathEClass -> EnumerateM SuspendedConstraint
pecToSuspendedConstraint pec = do uv <- addUVarValue Nothing
                                  return $ SuspendedConstraint (getPathTrie pec) uv

-- A full traversal; definitely not the most efficient.
-- | TODO: Why does this exist again? Was this added from a phase before I was proper about not touching eliminated uvars?
refreshReferencedUVars :: EnumerateM ()
refreshReferencedUVars = do
  values <- use uvarValues
  updated <- traverse (\case UVarUnenumerated n scs ->
                               UVarUnenumerated n <$>
                                   mapM (\sc -> SuspendedConstraint (scGetPathTrie sc)
                                                                       <$> getUVarRepresentative (scGetUVar sc))
                                        scs

                             x                      -> return x)
                      values

  uvarValues .= updated


---------------------
-------- Enumeration algorithm
---------------------

enumerateNode :: Seq SuspendedConstraint -> Node -> EnumerateM TermFragment
enumerateNode scs n =
  let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
  in case hereConstraints of
       Sequence.Empty -> case n of
                           Mu _    -> TermFragmentUVar <$> addUVarValue (Just n)

                           Node es -> enumerateEdge scs =<< lift es

       (x :<| xs)     -> do forM_ xs $ \sc -> uvarRepresentative %= UnionFind.union (scGetUVar x) (scGetUVar sc)
                            uv <- getUVarRepresentative (scGetUVar x)
                            mapM_ (assimilateUvarVal uv) hereConstraints
                            mergeNodeIntoUVarVal uv n descendantConstraints

                            return $ TermFragmentUVar uv

enumerateEdge :: Seq SuspendedConstraint -> Edge -> EnumerateM TermFragment
enumerateEdge scs e = do
  let highestConstraintIndex = getMax $ foldMap (\sc -> Max $ fromMaybe (-1) $ getMaxNonemptyIndex $ scGetPathTrie sc) scs
  guard $ highestConstraintIndex < length (edgeChildren e)

  newScs <- Sequence.fromList <$> mapM pecToSuspendedConstraint (unsafeGetEclasses $ edgeEcs e)
  let scs' = scs <> newScs
  TermFragmentNode (edgeSymbol e) <$> imapM (\i n -> enumerateNode (descendScs i scs') n) (edgeChildren e)

data ExpandableUVarResult = ExpansionStuck | ExpansionDone | ExpansionNext !UVar

-- Can speed this up with bitvectors
firstExpandableUVar :: EnumerateM ExpandableUVarResult
firstExpandableUVar = do
    values <- use uvarValues
    let candidates = Sequence.foldMapWithIndex
                      (\i -> \case (UVarUnenumerated (Just (Mu _)) Sequence.Empty) -> IntMap.empty
                                   (UVarUnenumerated (Just (Mu _)) _             ) -> IntMap.singleton i (Any False)
                                   (UVarUnenumerated (Just _)      _)              -> IntMap.singleton i (Any False)
                                   _                                               -> IntMap.empty)
                      values

    if IntMap.null candidates then
      return ExpansionDone
     else do
      let ruledOut = foldMap
                      (\case (UVarUnenumerated _ scs) -> foldMap
                                                             (\sc -> IntMap.singleton (uvarToInt $ scGetUVar sc) (Any True))
                                                             scs

                             _                         -> IntMap.empty)
                      values

      let unconstrainedCandidateMap = IntMap.filter (not . getAny) (ruledOut <> candidates)
      case IntMap.lookupMin unconstrainedCandidateMap of
        Nothing     -> return ExpansionStuck
        Just (i, _) -> return $ ExpansionNext $ intToUVar i



enumerateOutUVar :: UVar -> EnumerateM TermFragment
enumerateOutUVar uv = do UVarUnenumerated (Just n) scs <- getUVarValue uv
                         uv' <- getUVarRepresentative uv

                         t <- case n of
                                Mu x -> enumerateNode scs (unfoldRec x)
                                _    -> enumerateNode scs n


                         uvarValues.(ix $ uvarToInt uv') .= UVarEnumerated t
                         refreshReferencedUVars
                         return t

enumerateOutFirstExpandableUVar :: EnumerateM ()
enumerateOutFirstExpandableUVar = do
  muv <- firstExpandableUVar
  case muv of
    ExpansionNext uv -> void $ enumerateOutUVar uv
    ExpansionDone    -> mzero
    ExpansionStuck   -> mzero

enumerateFully :: EnumerateM ()
enumerateFully = do
  muv <- firstExpandableUVar
  case muv of
    ExpansionStuck   -> mzero
    ExpansionDone    -> return ()
    ExpansionNext uv -> do UVarUnenumerated (Just n) scs <- getUVarValue uv
                           if scs == Sequence.Empty then
                             case n of
                               Mu _ -> return ()
                               _    -> enumerateOutUVar uv >> enumerateFully
                            else
                             enumerateOutUVar uv >> enumerateFully

expandTermFrag :: TermFragment -> EnumerateM Term
expandTermFrag (TermFragmentNode s ts) = Term s <$> mapM expandTermFrag ts
expandTermFrag (TermFragmentUVar uv)   = do val <- getUVarValue uv
                                            case val of
                                              UVarEnumerated t                 -> expandTermFrag t
                                              UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
                                              _                                -> error "expandTermFrag: Non-recursive, unenumerated node encountered"


expandUVar :: UVar -> EnumerateM Term
expandUVar uv = do UVarEnumerated t <- getUVarValue uv
                   expandTermFrag t


---------------------
-------- Full enumeration
---------------------

getAllTruncatedTerms :: Node -> [Term]
getAllTruncatedTerms n = map (termFragToTruncatedTerm . fst) $
                         flip runEnumerateM (initEnumerationState n) $ do
                           enumerateFully
                           getTermFragForUVar (intToUVar 0)


-- | This works, albeit very inefficiently, for ECTAs without a Mu node
naiveDenotation :: Node -> [Term]
naiveDenotation n = go n
  where
    -- | Note that this code uses the decision that f(a,a) does not satisfy the constraint 0.0=1.0 because those paths are empty.
    --   It would be equally valid to say that it does.
    ecsSatisfied :: Term -> EqConstraints -> Bool
    ecsSatisfied t ecs = all (\ps -> all (\p' -> isJust (getPath (head ps) t) && getPath (head ps) t == getPath p' t) ps)
                             (map unPathEClass $ unsafeGetEclasses ecs)

    go :: Node -> [Term]
    go n = case n of
             EmptyNode -> []
             Mu _ -> [Term "Mu" []] -- | Does not really work
             Node es -> do
               e <- es

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
    maxNodeIndegree :: Int
    maxNodeIndegree = maxIndegree root

    fglNodeId :: Node -> Fgl.Node
    fglNodeId n = nodeIdentity n * (maxNodeIndegree + 1)

    fglTransitionId :: Node -> Int -> Fgl.Node
    fglTransitionId n i = nodeIdentity n * (maxNodeIndegree + 1) + (i + 1)

    fglNodeLabel :: Node -> Maybe (Fgl.LNode FglNodeLabel)
    fglNodeLabel n@(Node _) = Just (fglNodeId n, IdLabel $ nodeIdentity n)
    fglNodeLabel _          = Nothing

    onNormalNodes :: (Monoid a) => (Node -> a) -> (Node -> a)
    onNormalNodes f n@(Node _) = f n
    onNormalNodes f _          = mempty

    nodeNodes, transitionNodes :: [Fgl.LNode FglNodeLabel]
    nodeNodes       = crush (onNormalNodes $ (maybeToList . fglNodeLabel)) root
    transitionNodes = crush (onNormalNodes $ \n@(Node es) -> imap (\i e -> (fglTransitionId n i, TransitionLabel (edgeSymbol e) (edgeEcs e))) es) root

    -- | Uses the globally-unique mu node assumption
    -- Does not work if root is the mu node
    muNodeLabel :: Maybe Fgl.Node
    muNodeLabel = getFirst $ crush (onNormalNodes $ \(Node es) -> foldMap (\(Edge _ ns) -> foldMap muNodeToLabel ns) es) root
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

#ifdef PROFILE_CACHES
resetAllEctaCaches_BrokenDoNotUse :: IO ()
resetAllEctaCaches_BrokenDoNotUse = do
  Memoization.resetAllCaches
  Interned.resetCache (cache @Node)
  Interned.resetCache (cache @Edge)
#endif


getSubnodeById :: Node -> Id -> Maybe Node
getSubnodeById n i = getFirst $ crush (onNormalNodes $ \x -> if nodeIdentity x == i then First (Just x) else First Nothing) n