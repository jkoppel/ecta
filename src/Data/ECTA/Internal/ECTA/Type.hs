{-# LANGUAGE MultiWayIf        #-}
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
  , InternedNode(..)
  , InternedMu(..)
  , UninternedNode(..)
  , nodeIdentity
  , numNestedMu
  , modifyNode
  , createMu
  , stronglyIsomorphic
  ) where

import Data.Function ( on )
import Data.Hashable ( Hashable(..) )
import Data.List ( sort )
import           Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import Data.Maybe ( fromMaybe )
import           Data.Set ( Set )
import qualified Data.Set as Set

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

data RecNodeId =
    -- | Reference to the 'Id' of an interned 'Mu' node
    RecInt !Id

    -- | Reference to an as-yet uninterned 'Mu' node, for which the 'Id' is not yet known
    --
    -- The 'Int' argument is used to distinguish between multiple nested 'Mu' nodes.
    --
    -- NOTE: This is intentionally not an 'Id': it does not refer to the 'Id' of any interned node.
  | RecUnint Int

    -- | Placeholder variable that we use /only/ for depth calculations
    --
    -- The invariant that this is used /only/ for depth calculations, along with the observation that depth calculation
    -- does not depend on the exact choice of variable, justifies subtituting any other variable for 'RecDepth' in terms
    -- containing 'RecDepth' in all contexts.
  | RecDepth
  deriving ( Eq, Ord, Show, Generic )

instance Hashable RecNodeId

-----------------------------------------------------------------
----------------------------- Edges -----------------------------
-----------------------------------------------------------------

data Edge = InternedEdge { edgeId         :: !Id
                         , uninternedEdge :: !UninternedEdge
                         }

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
      -- >    substFree internedMuId (Rec (RecUnint (numNestedMu internedMuBody)) internedMuBody
      -- > == internedMuShape
    , internedMuShape :: !Node
    }
  deriving (Show)

data InternedNode = MkInternedNode {
      -- | The 'Id' of the node itself
      internedNodeId :: {-# UNPACK #-} !Id

      -- | All outgoing edges
    , internedNodeEdges :: ![Edge]

      -- | Maximum Mu nesting depth in the term
    , internedNodeNumNestedMu :: !Int
    }
  deriving (Show)

data Node = InternedNode {-# UNPACK #-} !InternedNode
          | EmptyNode
          | InternedMu {-# UNPACK #-} !InternedMu
          | Rec !RecNodeId

instance Eq Node where
  InternedNode l == InternedNode r = internedNodeId l == internedNodeId r
  InternedMu   l == InternedMu   r = internedMuId   l == internedMuId   r
  Rec          l == Rec          r =                l ==                r
  EmptyNode      == EmptyNode      = True
  _              == _              = False

instance Show Node where
  show (InternedNode node) = "(Node " <> show (internedNodeEdges node) <> ")"
  show EmptyNode           = "EmptyNode"
  show (InternedMu mu)     = "(Mu " <> show (internedMuBody mu) <> ")"
  show (Rec n)             = "(Rec " <> show n <> ")"

instance Ord Node where
  compare n1 n2 = compare (nodeDescriptorInt n1) (nodeDescriptorInt n2)
    where
      nodeDescriptorInt :: Node -> Int
      nodeDescriptorInt EmptyNode           = -1
      nodeDescriptorInt (InternedNode node) = 3*i
        where
          i = internedNodeId node
      nodeDescriptorInt (InternedMu mu)     = 3*i + 1
        where
          i = internedMuId mu
      nodeDescriptorInt (Rec recId)         = 3*i + 2
        where
          i = case recId of
                RecInt nid -> nid
                _otherwise -> error $ "compare: unexpected " <> show recId


instance Hashable Node where
  hashWithSalt s EmptyNode           = s `hashWithSalt` (-1 :: Int)
  hashWithSalt s (InternedMu mu)     = s `hashWithSalt` (-2 :: Int) `hashWithSalt` i
    where
      i = internedMuId mu
  hashWithSalt s (Rec i)             = s `hashWithSalt` (-3 :: Int) `hashWithSalt` i
  hashWithSalt s (InternedNode node) = s `hashWithSalt` i
    where
      i = internedNodeId node

-- | Maximum number of nested Mus in the term
--
-- @O(1) provided that there are no unbounded Mu chains in the term.
numNestedMu :: Node -> Int
numNestedMu EmptyNode           = 0
numNestedMu (InternedNode node) = internedNodeNumNestedMu node
numNestedMu (InternedMu   mu)   = 1 + numNestedMu (internedMuBody mu)
numNestedMu (Rec _)             = 0

-- | Check if two nodes are strongly isomorphic
--
-- Checks that two nodes have the exact same structure, modulo node 'Id's and modulo redundant 'Mu' nodes
-- (but not modulo unrolling, hence "strongly").
--
-- This function is only used in testing.
--
-- TODO: Ideally, two nodes that are strongly isomorphic would be /equal/. Something isn't going quite right in
-- interning.
stronglyIsomorphic :: Node -> Node -> Bool
stronglyIsomorphic = onNode Set.empty
  where
    onNode :: Set (Id, Id) -> Node -> Node -> Bool
    -- Nodes that are equal are definitely strongly isomorphic (currently sadly not the other way around, see above)
    onNode _ l r | l == r = True

    -- Order the nodes so that the environment always contains the lower Id first
    onNode env l r | l > r = onNode env r l

    -- One case for each of the constructors (if the constructors don't match, the terms are not strongly isomorphic)
    onNode !_    EmptyNode         EmptyNode        = True
    onNode !env (InternedNode l)  (InternedNode r)  = and $ zipWith (onEdge env) (internedNodeEdges l) (internedNodeEdges r)
    onNode !env (InternedMu   l)  (InternedMu   r)  = onNode (Set.insert (internedMuId l, internedMuId r) env) (internedMuBody l) (internedMuBody r)
    onNode !env (InternedMu   l)                r   = onNode                                              env  (internedMuBody l)                 r
    onNode !env               l   (InternedMu   r)  = onNode                                              env                  l  (internedMuBody r)
    onNode !env (Rec (RecInt  l)) (Rec  (RecInt r)) = (l, r) `Set.member` env
    onNode !_   (Rec          l)  (Rec          r)  = l == r
    onNode !_   _                 _                 = False

    onEdge :: Set (Id, Id) -> Edge -> Edge -> Bool
    onEdge !env l r = and [
          edgeSymbol l == edgeSymbol r
        , edgeEcs    l == edgeEcs    r
        , and $ zipWith (onNode env) (edgeChildren l) (edgeChildren r)
        ]

----------------------
------ Getters and setters
----------------------

nodeIdentity :: Node -> Id
nodeIdentity (InternedMu   mu)   = internedMuId mu
nodeIdentity (InternedNode node) = internedNodeId node
nodeIdentity (Rec (RecInt i))    = i
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
      -- > substFree i (Rec j) (f i) == f j
      --
      -- See 'shape' for additional discussion.
    | UninternedMu !(RecNodeId -> Node)

instance Eq UninternedNode where
  UninternedNode es   == UninternedNode es'  = es == es'
  UninternedEmptyNode == UninternedEmptyNode = True
  UninternedMu mu     == UninternedMu mu'    = shape mu == shape mu'
  _                   == _                   = False

instance Hashable UninternedNode where
  hashWithSalt salt = go
    where
      go :: UninternedNode -> Int
      go  UninternedEmptyNode = hashWithSalt salt (0 :: Int, ())
      go (UninternedNode es)  = hashWithSalt salt (1 :: Int, es)
      go (UninternedMu mu)    = hashWithSalt salt (2 :: Int, shape mu)

instance Interned Node where
  type Uninterned  Node = UninternedNode
  data Description Node = DNode !UninternedNode
    deriving ( Eq, Generic )

  describe = DNode

  identify i (UninternedNode es) = InternedNode $ MkInternedNode {
        internedNodeId          = i
      , internedNodeEdges       = es
      , internedNodeNumNestedMu = maximum (0 : concatMap (map numNestedMu . edgeChildren) es) -- depth is always >= 0
      }
  identify _ UninternedEmptyNode = EmptyNode
  identify i (UninternedMu n)    = InternedMu $ MkInternedMu {
        internedMuId    = i
      , internedMuBody  = n (RecInt i)

        -- In order to establish the invariant for internedMuNoId, we need to know
        --
        -- >    substFree internedMuId (Rec (RecUnint (numNestedMu internedMuBody)) internedMuBody
        -- > == internedMuShape
        --
        -- This follows from parametricity:
        --
        -- >    internedMuShape
        -- >      -- { definition of internedMuShape }
        -- > == shape n
        -- >      -- { definition of shape }
        -- > == n (RecUnint (numNestedMu (n RecDepth)))
        -- >      -- { by parametricity, depth is independent of the variable number }
        -- > == n (RecUnint (numNestedMu (n (RecInt i))))
        -- >      -- { parametricity again }
        -- > == substFree i (Rec (RecUnint (numNestedMu (n (RecInt i)))) (n (RecInt i))
        -- >      -- { definition of internedMuId and internedMuBody }
        -- > == substFree internedMuId (Rec (RecUnint (numNestedMu internedMuBody))) internedMuBody
        --
        -- QED.
      , internedMuShape = shape n
      }

  cache = nodeCache

instance Hashable (Description Node)

nodeCache :: Cache Node
nodeCache = unsafePerformIO freshCache
{-# NOINLINE nodeCache #-}

-- | Compute the " shape " of the body of a 'Mu'
--
-- During interning we need to know the shape of the body of a 'Mu' node /before/ we know the 'Id' of that node. We do
-- this by replacing any 'Rec' nodes in the node by placeholders. We have to be careful here however to correctly assign
-- placeholders in the presence of nested 'Mu' nodes. For example, if the user writes a term such as
--
-- > -- f (f (f ... (g (g (g ... a)))))
-- > Mu $ \r -> Node [
-- >     Edge "f" [r]
-- >   , Edge "g" [ Mu $ \r' -> Node [
-- >                    Edge "g" [r']
-- >                  , Edge "a" []
-- >                  ]
-- >              ]
-- >   ]
--
-- we should be careful not to accidentially identify @r@ and @r'@.
--
-- Precondition: the function must be parametric in the choice of variable names:
--
-- > substFree i (Rec j) (f i) == f j
--
-- Put another way, we must rule out /exotic terms/: in our case, exotic terms would be uninterned @Mu@ nodes that
-- have one shape when given one variable, and another shape when given a different variable. We do not have such terms.
-- (Of course, a function such as substitution /does/ do one thing if it sees one variable and another thing when it
-- sees a different variable, but this is okay: substitution is a function /on/ terms, mapping non-exotic terms to
-- non-exotic terms.)
--
-- Implementation note: We are calling the function twice: once to compute the depth of the node, and then a second time
-- to give it the right placeholder variable. Some observations:
--
-- o Semantically, this is okay; if we were working with a first order representation, it would be the equivalent of
--   first executing some kind of function @Node -> Int@, followed by some kind of substitution @Node -> Node@. It's the
--   same with the higher order representation, except that in /principle/ the function could do entirely different
--   things when given 'RecDepth' versus some other kind of placeholder; the parametricity precondition rules this out.
-- o It's slightly inefficient, but since this lives at the user interface boundary only, performance here is not
--   critical: internally we work with interned nodes only, and this function is not relevant.
-- o It /is/ important that the placeholder we pick here is uniquely determined by the node itself: this is what
--   justifies using 'shape' during interning.
shape :: (RecNodeId -> Node) -> Node
shape f = f (RecUnint (numNestedMu (f RecDepth)))

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
mkEdge _ _  ecs
   | constraintsAreContradictory ecs = emptyEdge
mkEdge s ns ecs
   | otherwise                       = intern $ UninternedEdge s ns ecs


-------------------
------ Node constructors
-------------------

{-# COMPLETE Node, EmptyNode, Mu, Rec #-}

pattern Node :: [Edge] -> Node
pattern Node es <- (InternedNode (internedNodeEdges -> es))
  where
    Node = mkNode

mkNode :: [Edge] -> Node
mkNode es = case removeEmptyEdges es of
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
-- > foo (InternedMu mu) = let f = \n' ->
-- >                          if | n' == Rec (RecUnint (numNestedMu (internedMuBody mu))) ->
-- >                                internedMuShape mu
-- >                            | n' == Rec RecDepth ->
-- >                                internedMuShape mu
-- >                            | otherwise ->
-- >                                substFree (internedMuId mu) n' (internedMuBody mu)
-- >                       in createMu f
-- >   -- { definition of createMu }
-- > foo (InternedMu mu) = intern $ UninternedMu (f . Rec)
--
-- At this point, `intern` will call `shape (f . Rec)`, which will call `f . Rec` twice: once with `RecDepth` to compute
-- the depth, and then once again with that depth to substitute a placeholder. Both of these special cases will use
-- 'internedMuShape' (and moreover, the depth calculation on 'internedMuShape' is @O(1)@).
pattern Mu :: (Node -> Node) -> Node
pattern Mu f <- (matchMu -> Just f)
  where
    Mu = createMu

-- | Construct recursive node
--
-- Implementation note: 'createMu' and 'matchMu' interact in non-trivial ways; see docs of the 'Mu' pattern synonym
-- for performance considerations.
createMu :: (Node -> Node) -> Node
createMu f = intern $ UninternedMu (f . Rec)

-- | Match on a 'Mu' node
--
-- Implementation note: 'createMu' and 'matchMu' interact in non-trivial ways; see docs of the 'Mu' pattern synonym
-- for performance considerations.
matchMu :: Node -> Maybe (Node -> Node)
matchMu (InternedMu mu) = Just $ \n' ->
    if | n' == Rec (RecUnint (numNestedMu (internedMuBody mu))) ->
          -- Special case justified by the invariant on 'internedMuShape'
          internedMuShape mu
       | n' == Rec RecDepth ->
          -- The use of 'RecDepth' implies that we are computing a depth:
          --
          -- >    numNestedMu (substFree (internedMuId mu) (Rec RecDepth)) (internedMuBody mu))
          -- >      -- { depth calculation does not depend on choice of variable }
          -- > == numNestedMu (substFree (internedMuId mu) Rec (RecUnint (numNestedMu (internedMuBody mu)))) (internedMuBody mu))
          -- >      -- { invariant of internedMuShape }
          -- > == numNestedMu internedMuShape
          internedMuShape mu
       | otherwise  ->
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
substFree old new n = substFree' n $ Map.singleton old new

-- | Generalization of 'substFree' to arbitrary number of substitutions
--
-- The somewhat unusual ordering the arguments is to facilitate memoization; see below.
substFree' :: Node -> Map Id Node -> Node
substFree' = onNode
  where
    -- Substitution is defined entirely by the term. This means that we can memoize independent of the environment.
    onNode :: Node -> Map Id Node -> Node
    onNode = memo (NameTag "substFree'.onNode") onNode'
    {-# NOINLINE onNode #-}

    onNode' :: Node -> Map Id Node -> Node
    onNode' EmptyNode            !_   = EmptyNode
    onNode' (InternedNode node)  !env = mkNode $ map ((\e -> onEdge e env)) (internedNodeEdges node)
    onNode' (InternedMu mu)      !env = createMu $ \r -> onNode (internedMuBody mu) (Map.insert (internedMuId mu) r env)
    onNode' n@(Rec (RecInt nid)) !env = fromMaybe n (Map.lookup nid env)
    onNode' (Rec recId)          !_   = Rec recId

    onEdge :: Edge -> Map Id Node -> Edge
    onEdge = memo (NameTag "substFree'.onEdge") onEdge'
    {-# NOINLINE onEdge #-}

    onEdge' :: Edge -> Map Id Node -> Edge
    onEdge' e env = setChildren e $ map (\n -> onNode n env) (edgeChildren e)

