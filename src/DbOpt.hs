{-# LANGUAGE OverloadedStrings #-}

module DbOpt where

import ECDFTA
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Language.Dot.Pretty as Dot

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
scope = const' "k"
hidx x y z = func "hidx" [x, y, z]

data Pattern =
  App Symbol [Pattern]
  | Var Int
  | NodePat Node
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
        (NodePat n') -> if n == n' then [[]] else []

match :: Pattern -> Node -> [PatternMatch]
match p = crush (matchRoot p)

atNode :: Node -> Node -> (Node -> Node) -> Node
atNode n n' f =
  if n == n' then f n else
    Node (List.map (\(Edge sym args) -> Edge sym $ List.map (\n -> atNode n n' f) args) es)
    where (Node es) = n

rewriteMatch :: PatternMatch -> Pattern -> Node -> Node
rewriteMatch PatternMatch { root, subst } pat n =
  atNode n root (\(Node ns) -> Node (ns ++ ns'))
  where
    liftPat subst pat =
      case pat of
        (App sym args) -> func sym $ List.map (liftPat subst) args
        (Var idx) -> Maybe.fromJust $ List.lookup idx subst
        (NodePat n) -> n
    (Node ns') = liftPat subst pat

testTerm = filter' (binary "and" (eq (name "x") (name "x'")) (name "y")) (relation "test")

data Rule = Rule { lhs :: Pattern
                 , rhs :: Pattern
                 , constrs :: [EqConstraint]
                 }
  deriving ( Show )

findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap f [] = Nothing
findMap f (x : xs) = case f x of
                       Just x' -> Just x'
                       Nothing -> findMap f xs

rewriteFirst :: Rule -> Node -> Maybe Node
rewriteFirst Rule {lhs, rhs, constrs} root =
  findMap (\m ->
             let root' = rewriteMatch m rhs root in
              if root == root' then Nothing else Just root')
  $ match lhs root

try :: (Node -> Maybe Node) -> Node -> Maybe Node
try r n =
  case r n of
    Just n' -> Just n'
    Nothing -> Just n

andThen :: (Node -> Maybe Node) -> (Node -> Maybe Node) -> Node -> Maybe Node
andThen r r' n =
  case r n of
    Just n' -> r' n'
    Nothing -> Nothing

repeat' :: Int -> (Node -> Maybe Node) -> Node -> Maybe Node
repeat' i r n =
  if i <= 0 then Just n else
  case r n of
    Nothing -> Just n
    Just n' -> repeat' (i - 1) r n'

filterToHidx = Rule {lhs, rhs, constrs}
  where
    lhs = App "filter" [App "eq" [Var 0, Var 1], Var 2]
    rhs = App "hidx" [App "select" [Var 0, Var 2], NodePat scope, App "filter" [App "eq" [Var 0, App "dot" [NodePat scope, Var 0]], Var 2, Var 1]]
    constrs = []

splitFilter = Rule {lhs, rhs, constrs}
  where
    lhs = App "filter" [App "and" [Var 0, Var 1], Var 2]
    rhs = App "filter" [Var 0, App "filter" [Var 1, Var 2]]
    constrs = []

mergeFilter = Rule {lhs, rhs, constrs}
  where
    lhs = App "filter" [Var 0, App "filter" [Var 1, Var 2]]
    rhs = App "filter" [App "and" [Var 0, Var 1], Var 2]
    constrs = []

flipBinop op = Rule {lhs, rhs, constrs}
  where
    lhs = App op [Var 0, Var 1]
    rhs = App op [Var 1, Var 0]
    constrs = []

flipEq = flipBinop "eq"
flipAnd = flipBinop "and"

rewrite = repeat' 20
          $ andThen (try $ rewriteFirst splitFilter)
          $ andThen (try $ rewriteFirst mergeFilter)
          $ (try $ rewriteFirst filterToHidx)
          
dumpDot (Just x) = Dot.prettyPrintDot $ toDot x
