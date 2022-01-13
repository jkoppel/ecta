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
import Data.Hashable ( hash )
import           Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HashMap
import Data.List ( inits, tails )
import Data.List.Extra ( nubOrd )
import Data.Maybe ( catMaybes )
import Data.Monoid ( Sum(..), First(..) )
import Data.Semigroup ( Max(..) )
import           Data.Set ( Set )
import qualified Data.Set as Set

import Control.Lens ( (&), ix, (^?), (%~) )
import Data.List.Index ( imap )
import Language.Dot.Pretty
import Debug.Trace
import Data.Aeson (encode)
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.ByteString.Lazy as BS

import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term

--   Switch the comments on these lines to switch to ekmett's original `intern` library
--   instead of our single-threaded hashtable-based reimplementation.
import Data.Interned.Extended.HashTableBased ( Id, intern )
-- import Data.Interned ( Interned(..), unintern, Id, Cache, mkCache )
-- import Data.Interned.Extended.SingleThreaded ( intern )
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
intersect = memo2 (NameTag "intersect") (\n1 n2 -> let n = refold $ nodeDropRedundantEdges $ doIntersect n1 n2
                                                    in n)
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
doIntersect n@(Mu _)  (Mu _)    = n -- TODO: Update for multiple Mu's
doIntersect n1@(Mu _) n2        = doIntersect (unfoldOuterRec n1) n2
doIntersect n1        n2@(Mu _) = doIntersect n1                  (unfoldOuterRec n2)
doIntersect n1@(Node es1) n2@(Node es2)
  | n1 == n2                            = n1
  | n2 <  n1                            = intersect n2 n1
                                          -- `hash` gives a unique ID of the symbol because they're interned
  | otherwise                           = let joined = hashJoin (hash . edgeSymbol) intersectEdgeSameSymbol es1 es2
                                          in Node joined
                                             --Node $ dropRedundantEdges joined
                                             --mkNodeAlreadyNubbed $ dropRedundantEdges joined
doIntersect n1 n2 = error $ "doIntersect: Unexpected " <> show n1 <> " " <> show n2


nodeDropRedundantEdges :: Node -> Node
nodeDropRedundantEdges (Node es) = Node $ dropRedundantEdges es
nodeDropRedundantEdges n = n

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
  getPath p                (Mu n)    = getPath p (unfoldRec n)
  getPath (ConsPath p ps) (Node es)  = union $ map (getPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns) = ns ^? ix p
  getPath p                n         = error $ "getPath: unexpected path " <> show p <> " for node " <> show n

  getAllAtPath _               EmptyNode = []
  getAllAtPath p               n@(Mu _)  = getAllAtPath p (unfoldOuterRec n)
  getAllAtPath EmptyPath       n         = [n]
  getAllAtPath p               (Mu n)    = getAllAtPath p (unfoldRec n)
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

-- | check whether the intersection result equals to any ancestors
occursCheck :: [Node] -> Node -> [Path] -> Bool
occursCheck oldNodes newNode ps = any hasOverlap (nodeGroups (getPrefixNodes ps))
  where
    -- | inits excluding empty and itself
    pathStrictInits :: Path -> [Path]
    pathStrictInits (Path ps) = map Path (init (tail (inits ps)))

    getPrefixPaths :: [Path] -> [Path]
    getPrefixPaths = nubOrd . concatMap pathStrictInits

    getPrefixNodes :: [Path] -> [(Path, Node)]
    getPrefixNodes ps = map (\p -> (p, getPath p oldNodes)) (getPrefixPaths ps)

    -- only do this for nodes that is not a Mu
    nodeGroups :: [(Path, Node)] -> [[(Path, Node)]]
    nodeGroups ns = let res = clusterByHash (hash . snd) ns
                     in res

    hasOverlap :: [(Path, Node)] -> Bool
    hasOverlap ng = newNode `elem` (map snd ng)

---------------
--- Reducing Equality Constraints
---------------

reducePartially :: EqConstraints -> Node -> Node
reducePartially ecs = memo (NameTag "reducePartially") $ \n -> nodeDropRedundantEdges (go n)
                                                                --  in if flag && nodeCount n' > nodeCount n then unsafePerformIO (BS.writeFile "reduceError2.pkl" (encode n) >> error "stop")  -- trace (show (nodeCount n' - nodeCount n) ++ "\n" ++ show (edgeCount n' - edgeCount n) ++ "\n" ++ show n ++ "\n\n\n" ++ show n') (error "stop")
                                                                --                        else n'
  where
    go :: Node -> Node
    go EmptyNode  = EmptyNode
    go (Mu n)     = Mu n
    go n@(Node _) = modifyNode n $ \es -> map (\e -> intern $ (uninternedEdge e) {uEdgeChildren = reduceChildren (createConstraints e) (edgeChildren e)})
                                          $ map (reduceEdgeIntersection ecs) es

    createConstraints :: Edge -> EqConstraints
    createConstraints e = ecs `combineEqConstraints` edgeEcs e

    ithPath :: [[[Path]]] -> Int -> [[Path]]
    ithPath pss i
      | length pss <= i = []
      | otherwise       = pss !! i

    reduceChildrenAt :: [PathTrie] -> Int -> Node -> Node
    reduceChildrenAt ptrees i n = reducePartially (mkEqConstraints $ map (\t -> fromPathTrie $ pathTrieDescend t i) ptrees) n

    reduceChildren :: EqConstraints -> [Node] -> [Node]
    -- reduceChildren _ children = map (reducePartially EmptyConstraints) children
    reduceChildren EqContradiction ns = map (const EmptyNode) ns
    reduceChildren ecs children = 
      zipWith (reduceChildrenAt (propagateConstraint (ecsGetPaths ecs))) 
              [0..length children]
              children

    -- addPathAt :: [Path] -> [[Path]] -> [[Path]]
    -- addPathAt [] pss = pss
    -- addPathAt (EmptyPath:ps) pss = addPathAt ps pss
    -- addPathAt ((ConsPath ph pt):ps) pss
    --   | length pss <= ph = addPathAt ((ConsPath ph pt):ps) (pss ++ [[]])
    --   | otherwise       = let pss' = pss & ix ph %~ (\x -> if pt == EmptyPath then x else pt:x)
    --                       in addPathAt ps pss'
  
    -- propagateConstraint :: [[Path]] -> [[[Path]]]
    -- propagateConstraint = \pss ->  transpose (map (`addPathAt` []) pss)

    propagateConstraint :: [[Path]] -> [PathTrie]
    propagateConstraint pss = map toPathTrie pss

{-# NOINLINE reducePartially #-}

reduceEdgeIntersection :: EqConstraints -> Edge -> Edge
reduceEdgeIntersection = memo2 (NameTag "reduceEdgeIntersection") go
  where
   go :: EqConstraints -> Edge -> Edge
   go ecs e = mkEdge (edgeSymbol e)
                     (reduceEqConstraints (edgeEcs e) ecs (edgeChildren e))
                     (edgeEcs e)
{-# NOINLINE reduceEdgeIntersection #-}

reduceEqConstraints :: EqConstraints -> EqConstraints -> [Node] -> [Node]
reduceEqConstraints = go
  where
    propagateEmptyNodes :: [Node] -> [Node]
    propagateEmptyNodes ns = if EmptyNode `elem` ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> EqConstraints -> [Node] -> [Node]
    go ecs extraEcs origNs 
      | constraintsAreContradictory (combineEqConstraints ecs extraEcs) = map (const EmptyNode) origNs
      | otherwise = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        eclasses = unsafeSubsumptionOrderedEclasses ecs

        -- | TODO: Replace with a "requirePathTrie"
        withNeededChildren = foldr requirePathList origNs (concatMap unPathEClass eclasses)

        intersectList :: [Node] -> Node
        intersectList ns = foldr intersect (head ns) (tail ns)

        _atPaths :: [Node] -> [Path] -> [Node]
        _atPaths ns ps = map (\p -> getPath p ns) ps

        reduceEClass :: PathEClass -> [Node] -> [Node]
        reduceEClass pec ns = foldr (\(p, nsRestIntersected) ns' -> modifyAtPath (\n -> let intersected = intersect nsRestIntersected n
                                                                                        --  in if occursCheck ns' intersected ps then trace ("occurs check found a cycle at " ++ show p) EmptyNode else trace ("reduction gets " ++ show intersected ++ " at " ++ show p)intersected) p ns')
                                                                                         in intersected) p ns')
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