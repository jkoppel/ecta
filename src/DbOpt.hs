{-# LANGUAGE OverloadedStrings #-}

module DbOpt where

import ECDFTA
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Language.Dot.Pretty as Dot

trinary :: Symbol -> Node -> Node -> Node -> Node
trinary name x y z = Node [Edge name [x, y, z]]

binary :: Symbol -> Node -> Node -> Node
binary name x y = Node [Edge name [x, y]]

unary :: Symbol -> Node -> Node
unary name x = Node [Edge name [x]]

const' name = Node [Edge name []]
consts names = Node $ List.map (\n -> Edge n []) names

func name xs = Node [Edge name xs]

none = const "none"
filter' = binary "filter"
join = trinary "join"
depjoin = trinary "depjoin"
eq = binary "eq"
lt = binary "lt"
dot = binary "dot"
name = const'
relation = const'
scope = consts ["k1", "k2", "k3"]
hidx x y z = func "hidx" [x, y, z]
meta = unary "meta"

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
    Node (List.map (\e -> mkEdge (edgeSymbol e) (List.map (\n -> atNode n n' f) $ edgeChildren e) (edgeEcs e)) es)
    where (Node es) = n

data Rule = Rule { lhs :: Pattern
                 , rhs :: Pattern
                 , pred :: Node -> Bool
                 , constrs :: [EqConstraint]
                 }

instance Show Rule where
  show Rule { lhs, rhs, constrs } = show (lhs, rhs, constrs)

rewriteMatch :: PatternMatch -> Rule -> Node -> Node
rewriteMatch PatternMatch { root, subst } rule n =
  atNode n root (\(Node ns) -> Node (ns ++ ns''))
  where
    liftPat subst pat =
      case pat of
        (App sym args) -> func sym $ List.map (liftPat subst) args
        (Var idx) -> Maybe.fromJust $ List.lookup idx subst
        (NodePat n) -> n
    (Node ns') = liftPat subst (rhs rule)
    ns'' = List.map (\e -> mkEdge (edgeSymbol e) (edgeChildren e) (constrs rule)) ns'

testTerm = filter' (binary "and" (eq (name "x") (name "x'")) (name "y")) (relation "test")

findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap f [] = Nothing
findMap f (x : xs) = case f x of
                       Just x' -> Just x'
                       Nothing -> findMap f xs

rewriteFirst :: Rule -> Node -> Maybe Node
rewriteFirst rule root =
  findMap (\m ->
             let root' = rewriteMatch m rule root in
              if root == root' then Nothing else Just root')
  $ match (lhs rule) root

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
    Just n' ->
      if n == n' then Just n else repeat' (i - 1) r n'

eqConstr p p' =
  EqConstraint (path p) (path p')

alwaysRule lhs rhs constrs = Rule { lhs, rhs, DbOpt.pred = const True, constrs }

filterToHidx = alwaysRule lhs rhs constrs
  where
    ckey = Var 0
    rkey = Var 1
    rel = Var 2
    lhs = App "filter" [App "eq" [ckey, rkey], rel]
    rhs = App "hidx" [App "select" [ckey, rel], NodePat scope, App "filter" [App "eq" [ckey, App "dot" [NodePat scope, ckey]], rel, rkey]]
    constrs = [ eqConstr [1] [2, 0, 1, 0] ]

filterToOidx = alwaysRule lhs rhs constrs
  where
    ckey = Var 0
    rkey1 = Var 1
    rkey2 = Var 2
    rel = Var 3
    lhs = App "filter" [App "and" [App "lt" [rkey1, ckey], App "lt" [ckey, rkey2]], rel]
    rhs = App "oidx" [ App "select" [ckey, rel],
                       NodePat scope,
                       App "filter" [App "eq" [ckey, App "dot" [NodePat scope, ckey]], rel, rkey1, rkey2]]
    constrs = [ eqConstr [1] [2, 0, 1, 0] ]

filterToOidx1 = alwaysRule lhs rhs constrs
  where
    ckey = Var 0
    rkey = Var 1
    rel = Var 2
    lhs = App "filter" [App "lt" [ckey, rkey], rel]
    rhs = App "oidx" [ App "select" [ckey, rel],
                       NodePat scope,
                       App "filter" [App "eq" [ckey, App "dot" [NodePat scope, ckey]], rel, App "none" [], rkey]]
    constrs = [ eqConstr [1] [2, 0, 1, 0] ]

filterToOidx2 = alwaysRule lhs rhs constrs
  where
    ckey = Var 0
    rkey = Var 1
    rel = Var 2
    lhs = App "filter" [App "lt" [rkey, ckey], rel]
    rhs = App "oidx" [ App "select" [ckey, rel],
                       NodePat scope,
                       App "filter" [App "eq" [ckey, App "dot" [NodePat scope, ckey]], rel, rkey, App "none" []]]
    constrs = [ eqConstr [1] [2, 0, 1, 0] ]

splitFilter = alwaysRule lhs rhs constrs
  where
    lhs = App "filter" [App "and" [Var 0, Var 1], Var 2]
    rhs = App "filter" [Var 0, App "filter" [Var 1, Var 2]]
    constrs = []

mergeFilter = alwaysRule lhs rhs constrs
  where
    lhs = App "filter" [Var 0, App "filter" [Var 1, Var 2]]
    rhs = App "filter" [App "and" [Var 0, Var 1], Var 2]
    constrs = []

hoistFilter = alwaysRule lhs rhs constrs
  where
    lhs = App "join" [Var 0, App "filter" [Var 1, Var 2], Var 3]
    rhs = App "filter" [Var 1, App "join" [Var 0, Var 2, Var 3]]
    constrs = []

toDepjoin = alwaysRule lhs rhs constrs
  where
    lhs = App "join" [Var 0, Var 1, Var 2]
    rhs = App "depjoin" [Var 1, NodePat scope, App "filter" [Var 0, Var 2]]
    constrs = []

flipJoin = alwaysRule lhs rhs constrs
  where
    lhs = App "join" [Var 0, Var 1, Var 2]
    rhs = App "join" [Var 0, Var 2, Var 1]
    constrs = []

flipBinop op = alwaysRule lhs rhs constrs
  where
    lhs = App op [Var 0, Var 1]
    rhs = App op [Var 1, Var 0]
    constrs = []

flipEq = flipBinop "eq"
flipAnd = flipBinop "and"

rewrite =
  repeat' 5 $
  try (rewriteFirst splitFilter) `andThen`
  try (rewriteFirst mergeFilter) `andThen`
  try (rewriteFirst hoistFilter) `andThen`
  try (rewriteFirst filterToOidx) `andThen`
  try (rewriteFirst filterToOidx1) `andThen`
  try (rewriteFirst filterToOidx2) `andThen`
  try (rewriteFirst filterToHidx) `andThen`
  try (rewriteFirst toDepjoin) `andThen`
  try (rewriteFirst flipAnd) `andThen`
  try (rewriteFirst flipEq) `andThen`
  try (rewriteFirst flipJoin)

relationSchema "orders" = ["o_orderkey", "o_custkey", "o_orderstatus", "o_totalprice", "o_orderdate", "o_orderpriority", "o_clerk", "o_shippriority", "o_comment"]
relationSchema "customer" = ["c_custkey", "c_name", "c_address", "c_nationkey", "c_phone", "c_acctbal", "c_mktsegment", "c_comment"]
relationSchema "lineitem" = ["l_orderkey", "l_partkey", "l_suppkey", "l_linenumber", "l_quantity", "l_extendedprice", "l_discount", "l_tax", "l_returnflag", "l_linestatus", "l_shipdate", "l_commitdate", "l_receiptdate", "l_shipinstruct", "l_shipmode", "l_comment"]

schema n = undefined

tpch3 = join (eq (name "c_custkey") (name "o_custkey"))
        (join (eq (name "l_orderkey") (name "o_orderkey"))
          (filter' (lt (name "o_orderdate") (name "param1")) (relation "orders"))
          (filter' (lt (name "param1") (name "l_shipdate")) (relation "lineitem")))
        (filter' (eq (name "c_mktsegment") (name "param0")) (relation "customer"))

dumpDot (Just x) = Dot.prettyPrintDot $ toDot x
