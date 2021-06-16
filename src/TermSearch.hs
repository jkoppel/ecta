{-# LANGUAGE OverloadedStrings #-}

module TermSearch (
    uptoDepth4
  ) where

import ECDFTA

------------------------------------------------------------------------------

tau :: Node
tau = Node [Edge "tau" []]

maybeType :: Node -> Node
maybeType n = Node [Edge "Maybe" [n]]

listType :: Node -> Node
listType n = Node [Edge "[]" [n]]

theArrowNode :: Node
theArrowNode = Node [Edge "(->)" []]

arrowType :: Node -> Node -> Node
arrowType n1 n2 = Node [Edge "->" [theArrowNode, n1, n2]]

constFunc :: Symbol -> Node -> Edge
constFunc s t = Edge s [t]

app :: Node -> Node -> Node
app n1 n2 = Node [mkEdge "app" [getPath (path [0, 2]) n1, theArrowNode, n1, n2]
                               [ EqConstraint (path [1])      (path [2, 0, 0])
                               , EqConstraint (path [2,0, 1]) (path [3, 0])
                               , EqConstraint (path [0])      (path [2, 0, 2])]
                 ]

f1, f2, f3, f4, f5, f6, f7 :: Edge
f1 = constFunc "Nothing" (maybeType tau)
f2 = constFunc "Just" (arrowType tau (maybeType tau))
f3 = constFunc "fromMaybe" (arrowType tau (arrowType (maybeType tau) tau))
f4 = constFunc "listToMaybe" (arrowType (listType tau) (maybeType tau))
f5 = constFunc "maybeToList" (arrowType (maybeType tau) (listType tau))
f6 = constFunc "catMaybes" (arrowType (listType (maybeType tau)) (listType tau))
f7 = constFunc "mapMaybe" (arrowType (arrowType tau (maybeType tau)) (arrowType (listType tau) (listType tau)))

arg1, arg2 :: Edge
arg1 = constFunc "def" tau
arg2 = constFunc "mbs" (listType (maybeType tau))

anyArg :: Node
anyArg = Node [arg1, arg2]

anyFunc :: Node
anyFunc = Node [f1, f2, f3, f4, f5, f6, f7]

size1, size2, size3, size4, size5, size6 :: Node
size1 = union [anyArg, anyFunc]
size2 = app size1 size1
size3 = union [app size2 size1, app size1 size2]
size4 = union [app size3 size1, app size2 size2, app size1 size3]
size5 = union [app size4 size1, app size3 size2, app size2 size3, app size1 size4]
size6 = union [app size5 size1, app size4 size2, app size3 size3, app size2 size4, app size1 size5]

uptoSize6UniqueRep :: Node
uptoSize6UniqueRep = union [size1, size2, size3, size4, size5, size6]

uptoDepth2 :: Node
uptoDepth2 = union [size1, app size1 size1]

uptoDepth3 :: Node
uptoDepth3 = union [uptoDepth2, app uptoDepth2 uptoDepth2]

uptoDepth4 :: Node
uptoDepth4 = union [uptoDepth3, app uptoDepth3 uptoDepth3]

filterType :: Node -> Node -> Node
filterType n t = Node [mkEdge "filter" [t, n] [EqConstraint (path [0]) (path [1, 0])]]

prettyTerm :: Term -> Term
prettyTerm (Term "app" [_, _, a, b]) = Term "app" [prettyTerm a, prettyTerm b]
prettyTerm (Term "filter" [_, a])    = prettyTerm a
prettyTerm (Term s [_]) = Term s []

dropTypes :: Node -> Node
dropTypes (Node es) = Node (map dropEdgeTypes es)
  where
    dropEdgeTypes (Edge "app"    [_, _, a, b]) = Edge "app" [dropTypes a, dropTypes b]
    dropEdgeTypes (Edge "filter" [_, a]      ) = Edge "filter" [dropTypes a]
    dropEdgeTypes (Edge s        [_]         ) = Edge s []
