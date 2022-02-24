{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

-- For the 'Pathable' instance for 'Node'
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.ECTA.Internal.ECTA.Operations (
  -- * Traversal
    pathsMatching
  , mapNodes
  , crush
  , onNormalNodes

  -- * Unfolding
  , unfoldOuterRec
  , refold
  , nodeEdges
  , unfoldBounded

  -- * Size operations
  , nodeCount
  , edgeCount
  , maxIndegree

  -- * Union
  , union

  -- * Membership
  , nodeRepresents
  , edgeRepresents

  -- * Intersection
  , intersect
  , dropRedundantEdges
  , intersectEdge

  -- * Path operations
  , requirePath
  , requirePathList

  -- * Reduction
  , withoutRedundantEdges
  , reducePartially
  , reduceEdgeIntersection
  , reduceEqConstraints

  -- * Debugging
  , getSubnodeById
  ) where


import Control.Monad.State.Strict ( evalState, State, MonadState(..), modify' )
import Data.Hashable ( hash, Hashable(..) )
import           Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HashMap
import Data.List ( inits, tails )
import Data.Maybe ( catMaybes )
import Data.Monoid ( Sum(..), First(..) )
import Data.Semigroup ( Max(..) )
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

import Control.Lens ( (&), ix, (^?), (%~) )
import Data.List.Index ( imap )

import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term

--   Switch the comments on these lines to switch to ekmett's original `intern` library
--   instead of our single-threaded hashtable-based reimplementation.
import Data.Interned.Extended.HashTableBased
--import Data.Interned ( Interned(..), unintern, Id, Cache, mkCache )
--import Data.Interned.Extended.SingleThreaded ( intern )

import Data.Memoization ( MemoCacheTag(..), memo, memo2 )
import Utility.Fixpoint
import Utility.HashJoin

------------------------------------------------------------------------------------


-----------------------
------ Traversal
-----------------------

-- | Warning: Linear in number of paths, exponential in size of graph.
--   Only use for very small graphs.
pathsMatching :: (Node -> Bool) -> Node -> [Path]
pathsMatching _   EmptyNode = []
pathsMatching _   (Mu _)    = [] -- Unsound!
pathsMatching f n@(Node es) = (concat $ map pathsMatchingEdge es)
                              ++ if f n then [EmptyPath] else []
  where
    pathsMatchingEdge :: Edge -> [Path]
    pathsMatchingEdge (Edge _ ns) = concat $ imap (\i x -> map (ConsPath i) $ pathsMatching f x) ns
pathsMatching _   (Rec _)   = error $ "pathsMatching: unexpected Rec"

-- | Precondition: For all i, f (Rec i) is either a Rec node meant to represent
--                 the enclosing Mu, or contains no Rec node not beneath another Mu.
mapNodes :: (Node -> Node) -> Node -> Node
mapNodes f = go
  where
    -- | Memoized separately for each mapNodes invocation
    go :: Node -> Node
    go = memo (NameTag "mapNodes") go'
    {-# NOINLINE go #-}

    go' :: Node -> Node
    go' EmptyNode = EmptyNode
    go' (Node es) = f $ (Node $ map (\e -> setChildren e $ (map go (edgeChildren e))) es)
    go' (Mu n)    = f $ Mu (go . n)
    go' (Rec i)   = f $ Rec i

-- This name originates from the "crush" operator in the Stratego language. C.f.: the "crushtdT"
-- combinators in the KURE and compstrat libraries.
--
-- Although m is only constrained to be a monoid, crush makes no guarantees about ordering.
crush :: forall m. (Monoid m) => (Node -> m) -> Node -> m
crush f = \n -> evalState (go n) Set.empty
  where
    go :: (Monoid m) => Node -> State (Set Id) m
    go EmptyNode             = return mempty
    go (Rec _)               = return mempty
    go n@(InternedMu mu)     = mappend (f n) <$> go (internedMuBody mu)
    go n@(InternedNode node) = do
      seen <- get
      let nId = nodeIdentity n
      if Set.member nId seen then
        return mempty
       else do
        modify' (Set.insert nId)
        mappend (f n) <$> (mconcat <$> mapM (\(Edge _ ns) -> mconcat <$> mapM go ns) (internedNodeEdges node))

onNormalNodes :: (Monoid m) => (Node -> m) -> (Node -> m)
onNormalNodes f n@(Node _) = f n
onNormalNodes _ _          = mempty

-----------------------
------ Folding
-----------------------

unfoldOuterRec :: Node -> Node
unfoldOuterRec n@(Mu x) = x n
unfoldOuterRec _        = error "unfoldOuterRec: Must be called on a Mu node"

nodeEdges :: Node -> [Edge]
nodeEdges (Node es) = es
nodeEdges n@(Mu _)  = nodeEdges (unfoldOuterRec n)
nodeEdges _         = []

refold :: Node -> Node
refold n = if HashMap.null muNodeMap then
             n
           else
             fixUnbounded tryUnfold n
  where
    muNodeMap :: HashMap Node Node
    muNodeMap = crush (\case x@(Mu _) -> HashMap.singleton (unfoldOuterRec x) x
                             _        -> HashMap.empty)
                      n

    tryUnfold :: Node -> Node
    tryUnfold x = case HashMap.lookup x muNodeMap of
                    Just y  -> y
                    Nothing -> x

unfoldBounded :: Int -> Node -> Node
unfoldBounded 0 = mapNodes (\case Mu _ -> EmptyNode
                                  n    -> n)
unfoldBounded k = unfoldBounded (k-1) . mapNodes (\case n@(Mu _) -> unfoldOuterRec n
                                                        n        -> n)


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
nodeRepresents n@(Mu _)  t                      = nodeRepresents (unfoldOuterRec n) t
nodeRepresents _         _                      = False

edgeRepresents :: Edge -> Term -> Bool
edgeRepresents e = \t@(Term s ts) -> s == edgeSymbol e
                                  && and (zipWith nodeRepresents (edgeChildren e) ts)
                                  && all (eclassSatisfied t) (unsafeGetEclasses $ edgeEcs e)
  where
    eclassSatisfied :: Term -> PathEClass -> Bool
    eclassSatisfied t pec = allTheSame $ map (\p -> getPath p t) $ unPathEClass pec

    allTheSame :: (Eq a) => [a] -> Bool
    allTheSame =
        \case
          []   -> True
          x:xs -> go x xs
      where
        go !_ []      = True
        go !x (!y:ys) = (x == y) && (go x ys)
    {-# INLINE allTheSame #-}

------------
------ Intersect
------------

intersect :: Node -> Node -> Node
intersect a b =
    let (IS f) = intersectDom (a, b)
    in f ()

------ Intersection internals

-- | Once we have computed the intersection, we just need to know the 'Id's assigned to the resulting shape
--
-- We separate these two things out, because the shape can be memoized independent of the 'Id's.
newtype IntersectionShape a = IS { isInEnv :: () -> a }

-- | Commute @[]@ and 'IntersectionShape'
sequenceIntersectionShape :: [IntersectionShape a] -> IntersectionShape [a]
sequenceIntersectionShape is = IS $ \env -> map (`isInEnv` env) is

constEmpty :: () -> Node
{-# NOINLINE constEmpty #-}
constEmpty _ = EmptyNode

-- | Compute intersection in the given domain
--
-- Contract: the resulting intersection shape must be applied to a map with 'idRecInt' as its domain.
intersectDom :: (Node, Node) -> IntersectionShape Node
intersectDom = memo (NameTag "IntersectionDom") (\(l, r) -> onNode l r)
  where
    onNode :: Node -> Node -> IntersectionShape Node
    onNode l r =
        case (l, r) of
          -- Rule out empty cases first
          -- This justifies the use of nodeIdentity (@i@, @j@) for the other cases
          (EmptyNode, _) -> IS $ constEmpty
          (_, EmptyNode) -> IS $ constEmpty

          -- When encountering a 'Mu', extend the domain in two ways:
          --
          -- 1. Entry in 'idRecInt': if we see the exact same intersection problem again, we can refer back to the Mu
          --    node we create here.
          -- 2. Entry in 'idFree'': we need to know the value of the free variable if we need to unroll
          --
          -- We make sure here to force the recursive call before constructing the final function so that the shape is
          -- fully computed.
          (InternedMu l', InternedMu r') ->
            -- let !dom'   = extendEnv [(i, l), (j, r)]
            --     ~(IS f) = intersectDom (dom', internedMuBody l', internedMuBody r')
            -- in IS $ \env -> Mu $ \recNode -> f (Map.insert (i, j) recNode env)
            IS $ \_ -> l
          (InternedMu l', _) ->
            let -- !dom'   = extendEnv [(i, l)]
                ~(IS f) = intersectDom (unfoldOuterRec l, r)
            -- in IS $ \env -> Mu $ \recNode -> f (Map.insert (i, j) recNode env)
            in IS $ f
          (_, InternedMu r') ->
            let -- !dom'   = extendEnv [(j, r)]
                ~(IS f) = intersectDom (l, unfoldOuterRec r) -- internedMuBody r')
            -- in IS $ \env -> Mu $ \recNode -> f (Map.insert (i, j) recNode env)
            in IS $ f

           -- When encountering a free variable, look up the corresponding value in the environment.
          (Rec l', _) -> error "uhoh"
          (_, Rec r') -> error "uhoh"

          -- Finally, the real intersection work happens here
          (InternedNode l', InternedNode r') ->
             let ~(IS f) = sequenceIntersectionShape $ hashJoin (hash . edgeSymbol)
                                                                (\e e' -> intersectDomEdge (e, e'))
                                                                (internedNodeEdges l')
                                                                (internedNodeEdges r')
             in IS $ Node . f

intersectDomEdge :: (Edge, Edge) -> IntersectionShape Edge
{-# NOINLINE intersectDomEdge #-}
intersectDomEdge = memo (NameTag "IntersectionDomEdge") (\(l, r) -> onEdge l r)
  where
    onEdge :: Edge -> Edge -> IntersectionShape Edge
    onEdge l r =
        let ~(IS f) = sequenceIntersectionShape $ zipWith (\a b -> intersectDom (a, b)) (edgeChildren l) (edgeChildren r)
        in IS $ \env -> mkEdge (edgeSymbol l)
                               (f env)
                               (edgeEcs l `combineEqConstraints` edgeEcs r)

------ Additional intersection utility

_nodeDropRedundantEdges :: Node -> Node
_nodeDropRedundantEdges (Node es) = Node $ dropRedundantEdges es
_nodeDropRedundantEdges node      = error $ "nodeDropRedundantEdges: unexpected node " <> show node

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
    ruleOut _ []     = (Keep, [])
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
      | length children1 /= length children2            = error $ "Different lengths encountered for children of symbol " <> show s
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
requirePath p               n@(Mu _)  = requirePath p (unfoldOuterRec n)
requirePath (ConsPath p ps) (Node es) = Node $ map (\e -> setChildren e (requirePathList (ConsPath p ps) (edgeChildren e)))
                                             $ filter (\e -> length (edgeChildren e) > p)
                                                      es
requirePath _               (Rec _)   = error "requirePath: unexpected Rec"

requirePathList :: Path -> [Node] -> [Node]
requirePathList EmptyPath       ns = ns
requirePathList (ConsPath p ps) ns = ns & ix p %~ requirePath ps

instance Pathable Node Node where
  type Emptyable Node = Node

  getPath _                EmptyNode = EmptyNode
  getPath p                n@(Mu _)  = getPath p (unfoldOuterRec n)
  getPath EmptyPath        n         = n
  getPath (ConsPath p ps) (Node es)  = union $ map (getPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns) = ns ^? ix p
  getPath p                n         = error $ "getPath: unexpected path " <> show p <> " for node " <> show n

  getAllAtPath _               EmptyNode = []
  getAllAtPath p               n@(Mu _)  = getAllAtPath p (unfoldOuterRec n)
  getAllAtPath EmptyPath       n         = [n]
  getAllAtPath (ConsPath p ps) (Node es) = concatMap (getAllAtPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns) = ns ^? ix p
  getAllAtPath p               n         = error $ "getAllAtPath: unexpected path " <> show p <> " for node " <> show n

  modifyAtPath f EmptyPath       n         = f n
  modifyAtPath _ _               EmptyNode = EmptyNode
  modifyAtPath f p               n@(Mu _)  = modifyAtPath f p (unfoldOuterRec n)
  modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
    where
      goEdge :: Edge -> Edge
      goEdge e = setChildren e (edgeChildren e & ix p %~ modifyAtPath f ps)
  modifyAtPath _ p               n         = error $ "modifyAtPath: unexpected path " <> show p <> " for node " <> show n

instance Pathable [Node] Node where
  type Emptyable Node = Node

  getPath EmptyPath       ns = union ns
  getPath (ConsPath p ps) ns = case ns ^? ix p of
                                 Nothing -> EmptyNode
                                 Just n  -> getPath ps n

  getAllAtPath EmptyPath       _  = []
  getAllAtPath (ConsPath p ps) ns = case ns ^? ix p of
                                      Nothing -> []
                                      Just n  -> getAllAtPath ps n

  modifyAtPath _ EmptyPath       ns = ns
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
    go n@(Mu _)   = n
    go n@(Node _) = modifyNode n $ \es -> map (\e -> intern $ (uninternedEdge e) {uEdgeChildren = map reducePartially (edgeChildren e)})
                                          $ map reduceEdgeIntersection es
    go (Rec _)    = error "reducePartially: unexpected Rec"
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

        _atPaths :: [Node] -> [Path] -> [Node]
        _atPaths ns ps = map (\p -> getPath p ns) ps

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

---------------
--- Debugging
---------------

getSubnodeById :: Node -> Id -> Maybe Node
getSubnodeById n i = getFirst $ crush (onNormalNodes $ \x -> if nodeIdentity x == i then First (Just x) else First Nothing) n