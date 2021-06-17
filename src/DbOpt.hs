{-# LANGUAGE OverloadedStrings #-}

module DbOpt where
  
import ECDFTA
import qualified Data.List as List
import qualified Data.Maybe as Maybe

binary :: Symbol -> Node -> Node -> Node
binary name x y = Node [Edge name [x, y]]

unary :: Symbol -> Node -> Node 
unary name x = Node [Edge name [x]]

const' name = Node [Edge name []]

func name xs = Node [Edge name xs]

filter' = binary "filter"
eq = binary "eq"
dot = binary "dot"
name = const'
relation = const'
scope = const'
hidx x y z = func "hidx" [x, y, z]

data Pattern =
  App Symbol [Pattern]
  | Var Int
  deriving ( Eq, Ord, Show )

data PatternMatch = PatternMatch { root :: Node
                                 , pat :: Pattern
                                 , subst :: [(Int, Node)]
                                 }
  deriving ( Show )

matchRoot :: Pattern -> Node -> [PatternMatch]
matchRoot p n =
  List.map (\s -> PatternMatch { root = n, pat = p, subst = s }) $ matches p n
  where
    matches :: Pattern -> Node -> [[(Int, Node)]]
    matches p n =
      case p of
        (App sym args) ->
          List.concatMap (\pats ->
                            (List.map concat $ mapM (uncurry matches) pats :: [[(Int, Node)]])) $
          List.map (\(Edge _ nodes) -> zip args nodes) $
          List.filter (\(Edge sym' _) -> sym == sym') $
          nodeEdges n
        (Var idx) -> [[(idx, n)]]

match :: Pattern -> Node -> [PatternMatch]
match p = crush (matchRoot p)

atNode :: Node -> Node -> (Node -> Node) -> Node
atNode n n' f =
  if n == n' then f n else
    Node (List.map (\(Edge sym args) -> Edge sym $ List.map (\n -> atNode n n' f) args) es)
    where (Node es) = n

rewrite :: PatternMatch -> Pattern -> Node -> Node
rewrite PatternMatch { root, subst } pat n =
  atNode n root (\(Node ns) -> Node (ns ++ ns'))
  where
    liftPat subst pat =
      case pat of
        (App sym args) -> func sym $ List.map (liftPat subst) args
        (Var idx) -> Maybe.fromJust $ List.lookup idx subst
    (Node ns') = liftPat subst pat

testTerm = filter' (eq (name "x") (name "x'")) (relation "test")
testPat = App "filter" [App "eq" [Var 0, Var 1], Var 2]

data Rule = Rule { lhs :: Pattern
                 , rhs :: Pattern
                 , constrs :: [EqConstraint]
                 }
  deriving ( Show )

filterToHidx = (lhs, rhs, constrs)
  where
    lhs = App "filter" [App "eq" [Var 0, Var 1], Var 2]
    rhs = App "hidx" [App "select" [Var 0, Var 2], scope, App "filter" [App "eq" [Var 0, App "dot" [scope, Var 0]], Var 2, Var 1]]
    constrs = []
