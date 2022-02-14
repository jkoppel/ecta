{-# LANGUAGE OverloadedStrings #-}

module Data.ECTA.Internal.ECTA.Visualization (
    toDot
  ) where

import Data.Maybe ( fromJust, maybeToList )
import Data.Monoid ( First(..) )
import qualified Data.Text as Text

import qualified Data.Graph.Inductive as Fgl
import Data.List.Index ( imap, imapM )
import qualified Language.Dot.Syntax as Dot


import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths ( EqConstraints )
import Data.ECTA.Internal.Term
import Data.Interned.Extended.HashTableBased ( Id )
import Data.Text.Extended.Pretty

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
    fglNodeId (InternedNode i _)  = i * (maxNodeIndegree + 1)
    fglNodeId (InternedMu mu)     = i * (maxNodeIndegree + 1)
      where
        i = internedMuId mu
    fglNodeId (Rec (RecNodeId i)) = i * (maxNodeIndegree + 1)
    fglNodeId EmptyNode           = error "fglNodeId: unexpected input"

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
        muNodeToLabel n@(Mu _) = First $ Just $ fglNodeId n
        muNodeToLabel _        = First Nothing

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
        edgeTo n i n' = (fglTransitionId n i, fglNodeId n', ())

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

