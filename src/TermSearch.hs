{-# LANGUAGE OverloadedStrings #-}

module TermSearch (

  ) where

import ECDFTA

------------------------------------------------------------------------------

tau :: Node
tau = Node [Edge "tau" [] []]

maybeType :: Node -> Node
maybeType n = Node [Edge "Maybe" [n] []]

listType :: Node -> Node
listType n = Node [Edge "[]" [n] []]

theArrowNode :: Node
theArrowNode = Node [Edge "(->)" [] []]

arrowType :: Node -> Node -> Node
arrowType n1 n2 = Node [Edge "->" [theArrowNode, n1, n2] []]

constFunc :: Symbol -> Node -> Edge
constFunc s t = Edge s [t] []

app :: Node -> Node -> Node
app n1 n2 = Node [Edge "app" [getPath (path [0, 2]) n1, theArrowNode, n1, n2]
                             [ EqConstraint (path [1]) (path [2, 0, 0])
                             , EqConstraint (path [2,0, 1]) (path [3, 0])
                             , EqConstraint (path [0]) (path [2, 0, 2])]
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

any1 :: Node
any1 = union [anyArg, anyFunc]

any2 :: Node
any2 = union [any1, app any1 any1]

any3 :: Node
any3 = union [any2, app any2 any2]

any4 :: Node
any4 = union [any3, app any3 any3]

filterType :: Node -> Node -> Node
filterType n t = Node [Edge "filter" [t, n] [EqConstraint (path [0]) (path [1, 0])]]

prettyTerm :: Term -> Term
prettyTerm (Term "app" [_, _, a, b]) = Term "app" [prettyTerm a, prettyTerm b]
prettyTerm (Term "filter" [_, a])    = prettyTerm a
prettyTerm (Term s [_]) = Term s []

