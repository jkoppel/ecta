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
import qualified Data.HashMap.Strict as HashMap
import Data.List ( inits, tails )
import Data.Maybe ( catMaybes )
import Data.Monoid ( Sum(..), First(..) )
import Data.Semigroup ( Max(..) )
import           Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

import Control.Lens ( (&), ix, (^?), (%~) )
import Data.List.Index ( imap )

import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term

--   Switch the comments on these lines to switch to ekmett's original `intern` library
--   instead of our single-threaded hashtable-based reimplementation.
import Data.Interned.Extended.HashTableBased ( Id )
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
refold = memo (NameTag "refold") go
  where
    go :: Node -> Node
    go n = if HashMap.null muNodeMap
             then n
             else fixUnbounded (mapNodes tryUnfold) n
      where
        muNodeMap = crush (\case x@(Mu _) -> HashMap.singleton (unfoldOuterRec x) x
                                 _        -> HashMap.empty)
                          n

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

_oldIntersect :: Node -> Node -> Node
_oldIntersect = memo2 (NameTag "intersect") go
  where
    go :: Node -> Node -> Node
    go n1 n2 = refold (nodeDropRedundantEdges (doIntersect n1 n2))
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
nodeDropRedundantEdges n         = n

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
------ New intersection
------------

intersect :: Node -> Node -> Node
intersect l r = intersectOpen (emptyIntersectionDom, l, r)

------ Intersection internals

-- | Intersection domain
--
-- Information required to compute the intersection of open terms.
data IntersectionDom = ID {
      -- | Value of all free variables inside the term (so that we can unfold when necessary)
      idFree :: Map Id Node

      -- | Intersection problems we encountered previously (to avoid infinite unrolling)
    , idRecInt :: Set IntersectId
    }
  deriving (Show, Eq)

instance Hashable IntersectionDom where
  -- Implementation notes:
  --
  -- - Both `Map.toList` and `Set.toList` return elements in key-order, which is a suitable canonical form for hashing.
  -- - The cost of the hashing is linear in the size of the domain. If this becomes a concern, we could cache the hash.
  hashWithSalt s (ID free recInt) = hashWithSalt s (Map.toList free, Set.toList recInt)

emptyIntersectionDom :: IntersectionDom
emptyIntersectionDom = ID Map.empty Set.empty

intersectOpen :: (IntersectionDom, Node, Node) -> Node
{-# NOINLINE intersectOpen #-}
intersectOpen = memo (NameTag "intersectOpen") (\(dom, l, r) -> refold $ nodeDropRedundantEdges $ onNode dom l r)
  where
    onNode :: IntersectionDom -> Node -> Node -> Node
    onNode !dom l r =
        case (l, r) of
          -- Rule out empty cases first
          -- This justifies the use of nodeIdentity (@i@, @j@) for the other cases
          (EmptyNode, _) -> EmptyNode
          (_, EmptyNode) -> EmptyNode

          -- For closed terms, improve memoization performance by using the empty environment
          _ | Set.null (freeVars l), Set.null (freeVars r), not (Map.null (idFree dom)) -> intersect l r

          -- Special case for self-intersection (equality check is cheap of course: just uses the interned 'Id')
          _ | l == r, Set.null (freeVars l) -> l

          -- Always intersect nodes in the same order. This is important for two reasons:
          --
          -- 1. It will increase the probability of a cache hit (i.e., improve memoization)
          -- 2. It will increase the probability of being able to use 'ieRecInt'
          _ | l > r -> intersectOpen (dom, r, l)

          -- If we have seen this exact problem before, refer to enclosing Mu.
          _ | Set.member (IntersectId i j) (idRecInt dom) -> Rec (RecIntersect (IntersectId i j))

          -- When encountering a 'Mu', extend the domain appropriately.
          (InternedMu l' , InternedMu r') -> maybeMu $ intersectOpen (extendEnv [(i, l), (j, r)] , internedMuBody l' , internedMuBody r')
          (InternedMu l' , _            ) -> maybeMu $ intersectOpen (extendEnv [(i, l)        ] , internedMuBody l' ,                r )
          (_             , InternedMu r') -> maybeMu $ intersectOpen (extendEnv [        (j, r)] ,                l  , internedMuBody r')

           -- When encountering a free variable, look up the corresponding value in the environment.
           -- (Recall that the case for already-seen intersection problems is are handled above.)
          (Rec l' , _     ) -> intersectOpen (dom , findFreeVar l' ,             r )
          (_      , Rec r') -> intersectOpen (dom ,             l  , findFreeVar r')

          -- Finally, the real intersection work happens here
          (InternedNode l', InternedNode r') ->
            Node $ hashJoin (hash . edgeSymbol)
                            (\e e' -> intersectOpenEdge (dom, e, e'))
                            (internedNodeEdges l')
                            (internedNodeEdges r')
      where
        -- Node identities (should only be used (forced) if previously established the nodes are not empty)
        i, j :: Id
        i = nodeIdentity l
        j = nodeIdentity r

        -- Extend domain when we encounter a 'Mu'
        -- We might see one or two 'Mu's (if we happen to see a 'Mu' on both sides at once)
        extendEnv :: [(Id, Node)] -> IntersectionDom
        extendEnv bindings = ID {
              idFree   = Map.union (Map.fromList bindings) (idFree dom)
            , idRecInt = Set.insert (IntersectId i j) (idRecInt dom)
            }

        -- Find value of free variables in the terms
        -- Since we assume the input terms are fully interned, we only deal with 'RecInt'.
        findFreeVar :: RecNodeId -> Node
        findFreeVar (RecInt intId) | Just n <- Map.lookup intId (idFree dom) = n
        findFreeVar recId = error $ "findFreeVar: unexpected " <> show recId

        -- We only insert a 'Mu' node when necessary.
        maybeMu :: Node -> Node
        maybeMu n
          | RecIntersect (IntersectId i j) `Set.member` freeVars n
          = Mu $ \recNode -> substFree (RecIntersect (IntersectId i j)) recNode n

          | otherwise
          = n

-- | Auxiliary to 'intersectOpen'.
intersectOpenEdge :: (IntersectionDom, Edge, Edge) -> Edge
{-# NOINLINE intersectOpenEdge #-}
intersectOpenEdge = memo (NameTag "intersectOpenEdge") (\(dom, l, r) -> onEdge dom l r)
  where
    onEdge :: IntersectionDom -> Edge -> Edge -> Edge
    onEdge !dom l r =
         mkEdge (edgeSymbol l)
                (zipWith (\a b -> intersectOpen (dom, a, b)) (edgeChildren l) (edgeChildren r))
                (edgeEcs l `combineEqConstraints` edgeEcs r)

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
  getPath EmptyPath        n         = n
  getPath p                n@(Mu _)  = getPath p (unfoldOuterRec n)
  getPath (ConsPath p ps) (Node es)  = union $ map (getPath ps) (catMaybes (map goEdge es))
    where
      goEdge :: Edge -> Maybe Node
      goEdge (Edge _ ns) = ns ^? ix p
  getPath p                n         = error $ "getPath: unexpected path " <> show p <> " for node " <> show n

  getAllAtPath _               EmptyNode = []
  getAllAtPath EmptyPath       n         = [n]
  getAllAtPath p               n@(Mu _)  = getAllAtPath p (unfoldOuterRec n)
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
reducePartially = reducePartially' EmptyConstraints

reducePartially' :: EqConstraints -> Node -> Node
reducePartially' = memo2 (NameTag "reducePartially'") go
  where
    go :: EqConstraints -> Node -> Node
    go _            EmptyNode  = EmptyNode
    go _            (Mu n)     = Mu n
    go inheritedEcs n@(Node _) = modifyNode n $ \es -> map (reduceChildren inheritedEcs)
                                                       $ map (reduceEdgeIntersection inheritedEcs) es
    go _            (Rec _)    = error "reducePartially: unexpected Rec"

    reduceChildren :: EqConstraints -> Edge -> Edge
    reduceChildren inheritedEcs e = setChildren e $ reduceWithInheritedEcs (inheritedEcs `combineEqConstraints` edgeEcs e) (edgeChildren e)

    -- | Reduce children with inherited constraints
    --
    -- This function is used to avoid infinite unfolding of recursive nodes,
    -- and we do this by passing constraints from the current edge and ancestors to descendants.
    -- For example, let `tau` be "any" node, and we define
    --
    -- > let n1 = Node [ mkEdge "Pair" [tau, tau] (mkEqConstraints [[path [0, 0], path [0, 1], path [1]]])]
    -- > let n2 = Node [ Edge "Pair" [tau, tau] ]
    -- > let n  = Node [ mkEdge "Pair" [n1, n2]   (mkEqConstraints [[path [0, 0], path [0, 1], path [1]]])]
    --
    -- We notice that, if we call `reducePartially n` without propagating constraints down to its children `n1` or `n2`,
    -- the `tau` can be infinitely expanded between rounds of reduction.
    --
    -- To break such cycles, we actively pass constraints down to children.
    -- In this example, we first call `reducePartially' EmptyConstraints n` at the top level, where the inherited constraint is empty,
    -- so we only need to consider the constraints from the current edge.
    -- Then, we pass the constraints `0.0=0.1=1` down to its children, and `n1` receives `0=1` and `n2` receives nothing.
    -- Next, we reduce the children of `n` by calling `reducePartially' (mkEqConstraints [[path [0], path [1]]]) n1`.
    -- At this node, we will have to combine the inherited constraints `0=1` and the local constraints `0.0=0.1=1`.
    -- Now, we can see that these two constraints contain a contradiction that requires `0=0.0=0.1`, so we can drop the edge.
    --
    -- TODO: this approach does not solve all cases of cycles. See the test case `loop2` in `src/Application/TermSearch/Utils.hs`.
    reduceWithInheritedEcs :: EqConstraints -> [Node] -> [Node]
    reduceWithInheritedEcs EqContradiction children = map (const EmptyNode) children
    reduceWithInheritedEcs inheritedEcs    children = zipWith (\i -> reducePartially' (eqConstraintsDescend inheritedEcs i)) [0..] children

{-# NOINLINE reducePartially' #-}

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
    go ecs inheritedEcs origNs
      | constraintsAreContradictory (ecs `combineEqConstraints` inheritedEcs) = map (const EmptyNode) origNs
      | otherwise                                                             = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
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
        toIntersect ns ps = map intersectList $ dropOnes $ map (`getPath` ns) ps

        -- | dropOnes [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]
        dropOnes :: [a] -> [[a]]
        dropOnes xs = zipWith (++) (inits xs) (tail $ tails xs)

---------------
--- Debugging
---------------

getSubnodeById :: Node -> Id -> Maybe Node
getSubnodeById n i = getFirst $ crush (onNormalNodes $ \x -> if nodeIdentity x == i then First (Just x) else First Nothing) n
