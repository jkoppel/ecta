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
  , IntersectId -- opaque
  , pattern IntersectId
  , nodeIdentity
  , numNestedMu
  , substFree
  , freeVars
  , modifyNode
  , createMu
  ) where

import Data.Function ( on )
import Data.Hashable ( Hashable(..) )
import Data.List ( sort )
import Data.Maybe ( fromMaybe )
import           Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
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

    -- | Refer to Mu-node-to-be-constructed during intersection
    --
    -- TODO: It is obviously not very elegant to have a constructor here specifically for one algorithm. Ideally, we
    -- would parameterize 'Node' with the type of the identifiers in it. This might be useful also to rule out many
    -- other cases (specifically, most of the time we are dealing with fully interned nodes, and so the only
    -- constructor we expect is 'RecInt').
  | RecIntersect IntersectId
  deriving ( Eq, Ord, Show, Generic )

-- | Context-free references to a 'Mu' node introduced by 'intersect'
--
-- Background: This is a generalization of the idea to be able to refer to the "immediately enclosing binder", and then
-- only deal with graphs with the property that we never need to refer past that enclosing binder. This too would allow
-- us to refer to a 'Mu' node without knowing its 'Id', at the cost of requiring a substitution when we discover that
-- 'Id' to return this into a 'RecInt'. The generalization is that all we need to /some/ way to refer to that 'Mu' node
-- concretely, without 'Id', but we can: intersection introduces 'Mu' whenever it encounters a 'Mu' on the left or the
-- right, /and will then not introduce another 'Mu' for that same intersection problem (at least, not in the same
-- scope). This means that the 'Id' of the left and right operand will indeed uniquely identify the 'Mu' node to be
-- constructed by 'intersect'.
--
-- Furthermore, since we cache the free variables in a term, we have a cheap check to see if we need the 'Mu' node at
-- all. This means that /if/ the input graphs satisfy the property that there are references past 'Mu' nodes, the output
-- should too: we will not introduce redundant 'Mu' nodes.
--
-- NOTE: Although intersect has three cases in which it introduces 'Mu' nodes ('Mu' in both operands, 'Mu' in the left,
-- or 'Mu' in the right), we don't need that distinction here: we just need to know the 'Id' of the two operands, so
-- that if we see a call to intersect again /with those same two operands/ (no matter what kind of nodes they are), we
-- can refer to the newly constructed 'Mu' node.
data IntersectId =
     -- Invariant: the two 'Id's should be ordered (guaranteed by the pattern synonym constructor)
     UnsafeIntersectId !Id !Id
  deriving ( Eq, Ord, Show, Generic )

pattern IntersectId :: Id -> Id -> IntersectId
pattern IntersectId i j <- (UnsafeIntersectId i j)
  where
    IntersectId i j | i <= j    = UnsafeIntersectId i j
                    | otherwise = UnsafeIntersectId j i

instance Hashable RecNodeId
instance Hashable IntersectId

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

      -- | Free variables in the term
    , internedNodeFree :: !(Set RecNodeId)
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

-- | Free variables in the term
--
-- @O(1) in the size of the graph, provided that there are no unbounded Mu chains in the term.
-- @O(log n)@ in the number of free variables in the graph, which we expect to be orders of magnitude smaller than the
-- size of the graph (indeed, we don't expect more than a handful).
freeVars :: Node -> Set RecNodeId
freeVars EmptyNode           = Set.empty
freeVars (InternedNode node) = internedNodeFree node
freeVars (InternedMu   mu)   = Set.delete (RecInt (internedMuId mu)) (freeVars (internedMuBody mu))
freeVars (Rec i)             = Set.singleton i

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
      , internedNodeFree        = Set.unions (concatMap (map freeVars . edgeChildren) es)
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
pattern Node es <- (InternedNode (internedNodeEdges -> es)) where
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
          substFree (RecInt (internedMuId mu)) n' (internedMuBody mu)

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
substFree :: RecNodeId -> Node -> Node -> Node
substFree old new = substFree' (Map.singleton old new)

-- | Generalization of 'substFree' to multiple binders.
substFree' :: Map RecNodeId Node -> Node -> Node
substFree' env node = case template node of
                        Template f -> f env

------ Substitution internals

-- | The template of a something is that something with holes for as-yet unknown 'Id's
--
-- This datatype should satisfy two properties for 'template' to work correctly:
--
-- 1. Forcing the 'Template' to WHNF should not result in any recursive calls
--    (so that the recursion isn't totally unrolled before memoization can happen).
-- 2. But forcing the /function inside/ the 'Template' to WHNF /should/ result in all recursive calls to happen,
--    (/before/ the function is executed: executing the function should /not/ cause further calls to 'template').
--
-- The idea here is that a function returning a 'Template', the application of that 'Template' should not result in
-- further recursive calls to that function, so that any expensive computation done by that function is not repeated,
-- but is done independently of the environment (the 'Map') that we provide to the 'Template'. Put another way: the
-- function can be memoized independently of that environment. For substitution this may not matter very much, but for
-- other functions it could. Note however that the resulting 'Template' does build the graph on each invocation; this
-- may still be prohibitively expensive. See 'intersect' for an example of how we can avoid an environment altogether.
-- (This is not an option for substitution of course, where the environment is part of the API of the function.)
data Template a = Template (Map RecNodeId Node -> a)

-- | Commute @[]@ and 'Template'
--
-- Forces all elements in the list
sequenceTemplate :: [Template a] -> Template [a]
sequenceTemplate = Template . go []
  where
    go :: [Map RecNodeId Node -> a] -> [Template a] -> Map RecNodeId Node -> [a]
    go acc []               = \env -> reverse (map ($ env) acc)
    go acc (Template !f:fs) = go (f:acc) fs

-- | Extract the shape from a term
--
-- Somewhat serendipitously (or does this point to some deeper truth?) this also serves as a definition of substitution:
-- any free variables in the original node will become " holes " in the 'Template'.
--
-- We do not use the pattern synonyms here, because 'template' is used (through 'substFree') to /define/ those
-- pattern synonyms.
template :: Node -> Template Node
{-# NOINLINE template #-}
template = memo (NameTag "template") onNode
  where
    onNode :: Node -> Template Node
    onNode n = Template $
        case n of
          EmptyNode         -> \_ -> EmptyNode
          InternedNode node -> case sequenceTemplate $ map templateEdge (internedNodeEdges node) of
                                      Template !f -> \env -> mkNode (f env)
          InternedMu mu     -> case onNode (internedMuBody mu) of
                                      Template !f -> \env -> createMu $ \r -> f (Map.insert (RecInt (internedMuId mu)) r env)
          Rec i             -> \env -> fromMaybe n (Map.lookup i env)

-- | Internal auxiliary to 'template'
templateEdge :: Edge -> Template Edge
{-# NOINLINE templateEdge #-}
templateEdge = memo (NameTag "templateEdge") onEdge
  where
    onEdge :: Edge -> Template Edge
    onEdge e =
        Template $ case sequenceTemplate (map template (edgeChildren e)) of
                  Template !f -> setChildren e . f
