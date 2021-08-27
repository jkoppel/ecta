{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.ECTA.Internal.ECTA.Operations (
  -- * Traversal
    pathsMatching
  , mapNodes
  , crush
  , onNormalNodes

  -- * Unfolding
  , unfoldRec
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
import Data.Hashable ( hash )
import Data.List ( inits, tails )
import Data.Maybe ( catMaybes )
import Data.Monoid ( Sum(..), First(..) )
import Data.Semigroup ( Max(..) )
import           Data.Set ( Set )
import qualified Data.Set as Set

import Control.Lens ( (&), ix, (^?), (%~) )
import Data.List.Index ( imap )

import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term
import Data.Interned.Extended.HashTableBased ( Id, intern )
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
        modify' (Set.insert nId)
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


nodeEdges :: Node -> [Edge]
nodeEdges (Node es) = es
nodeEdges (Mu n)    = nodeEdges (unfoldRec n)
nodeEdges _         = []

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
    propagateEmptyNodes ns = if EmptyNode `elem` ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> [Node] -> [Node]
    go ecs origNs = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        eclasses = unsafeSubsumptionOrderedEclasses ecs

        -- | TODO: Replace with a "requirePathTrie"
        withNeededChildren = foldr requirePathList origNs (concatMap unPathEClass eclasses)

        intersectList :: [Node] -> Node
        intersectList ns = foldr intersect (head ns) (tail ns)

        atPaths :: [Node] -> [Path] -> [Node]
        atPaths ns ps = map (`getPath` ns) ps

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
        toIntersect ns ps = map intersectList $ dropOnes $ map (`getPath` ns) ps

        -- | dropOnes [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]
        dropOnes :: [a] -> [[a]]
        dropOnes xs = zipWith (++) (inits xs) (tail $ tails xs)

---------------
--- Debugging
---------------

getSubnodeById :: Node -> Id -> Maybe Node
getSubnodeById n i = getFirst $ crush (onNormalNodes $ \x -> if nodeIdentity x == i then First (Just x) else First Nothing) n