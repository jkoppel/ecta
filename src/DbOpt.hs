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

funcC name xs cs = Node [mkEdge name xs cs]

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

data Pattern p =
  App Symbol [p]
  | Var Int
  | NodePat Node
  deriving ( Eq, Ord, Show )

newtype ConstrPattern = ConstrPattern (Pattern ConstrPattern, [EqConstraint])
  deriving ( Eq, Ord, Show )

data PatternMatch = PatternMatch { root :: Node
                                 , pat :: ConstrPattern
                                 , subst :: [(Int, Node)]
                                 }
  deriving ( Show )

matchRoot :: ConstrPattern -> Node -> [PatternMatch]
matchRoot p n =
  List.map (\s -> PatternMatch { root = n, pat = p, subst = s }) $ matches p n
  where
    matches :: ConstrPattern -> Node -> [[(Int, Node)]]
    matches (ConstrPattern (p, eqs)) n =
      case p of
        (App sym args) ->
          List.concatMap (\pats ->
                             (List.map concat $
                              mapM (uncurry matches) pats :: [[(Int, Node)]])) $
          List.map (\(Edge _ nodes) -> zip args nodes) $
          List.filter (\(Edge sym' _) -> sym == sym') $
          nodeEdges n
        (Var idx) -> [[(idx, n)]]
        (NodePat n') -> if n == n' then [[]] else []

match :: ConstrPattern -> Node -> [PatternMatch]
match p = crush (matchRoot p)

atNode :: Node -> Node -> (Node -> Node) -> Node
atNode n n' f =
  if n == n' then f n else
    Node (List.map (\e -> mkEdge (edgeSymbol e) (List.map (\n -> atNode n n' f) $ edgeChildren e) (edgeEcs e)) es)
    where (Node es) = n

data Rule = Rule { lhs :: ConstrPattern
                 , rhs :: ConstrPattern
                 , pred :: Node -> Bool
                 }

instance Show Rule where
  show Rule { lhs, rhs } = show (lhs, rhs)

rewriteMatch :: PatternMatch -> Rule -> Node -> Node
rewriteMatch PatternMatch { root, subst } rule n =
  atNode n root (\(Node ns) -> Node (ns ++ ns'))
  where
    liftPat subst (ConstrPattern (pat, constrs)) =
      case pat of
        (App sym args) -> funcC sym (List.map (liftPat subst) args) constrs
        (Var idx) -> Maybe.fromJust $ List.lookup idx subst
        (NodePat n) -> n
    (Node ns') = liftPat subst (rhs rule)

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

alwaysRule lhs rhs = Rule { lhs, rhs, DbOpt.pred = const True }

var x = ConstrPattern (Var x, [])
app f xs = ConstrPattern (App f xs, [])
appC f xs c = ConstrPattern (App f xs, c)
nodePat n = ConstrPattern (NodePat n, [])

filterToHidx = alwaysRule lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = app "filter" [app "eq" [ckey, rkey], rel]
    rhs = appC "hidx" [app "select" [ckey, rel], nodePat scope, app "filter" [app "eq" [ckey, app "dot" [nodePat scope, ckey]], rel, rkey]] [ eqConstr [1] [2, 0, 1, 0] ]

filterToOidx = alwaysRule lhs rhs 
  where
    ckey = var 0
    rkey1 = var 1
    rkey2 = var 2
    rel = var 3
    lhs = app "filter" [app "and" [app "lt" [rkey1, ckey], app "lt" [ckey, rkey2]], rel]
    rhs = app "oidx" [ app "select" [ckey, rel],
                       nodePat scope,
                       app "filter" [app "eq" [ckey, app "dot" [nodePat scope, ckey]], rel, rkey1, rkey2]]
    constrs = [ eqConstr [1] [2, 0, 1, 0] ]

filterToOidx1 = alwaysRule lhs rhs 
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = app "filter" [app "lt" [ckey, rkey], rel]
    rhs = app "oidx" [ app "select" [ckey, rel],
                       nodePat scope,
                       app "filter" [app "eq" [ckey, app "dot" [nodePat scope, ckey]], rel, app "none" [], rkey]]
    constrs = [ eqConstr [1] [2, 0, 1, 0] ]

filterToOidx2 = alwaysRule lhs rhs 
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = app "filter" [app "lt" [rkey, ckey], rel]
    rhs = app "oidx" [ app "select" [ckey, rel],
                       nodePat scope,
                       app "filter" [app "eq" [ckey, app "dot" [nodePat scope, ckey]], rel, rkey, app "none" []]]
    constrs = [ eqConstr [1] [2, 0, 1, 0] ]

splitFilter = alwaysRule lhs rhs 
  where
    lhs = app "filter" [app "and" [var 0, var 1], var 2]
    rhs = app "filter" [var 0, app "filter" [var 1, var 2]]

mergeFilter = alwaysRule lhs rhs 
  where
    lhs = app "filter" [var 0, app "filter" [var 1, var 2]]
    rhs = app "filter" [app "and" [var 0, var 1], var 2]

hoistFilter = alwaysRule lhs rhs 
  where
    lhs = app "join" [var 0, app "filter" [var 1, var 2], var 3]
    rhs = app "filter" [var 1, app "join" [var 0, var 2, var 3]]

toDepjoin = alwaysRule lhs rhs 
  where
    lhs = app "join" [var 0, var 1, var 2]
    rhs = app "depjoin" [var 1, nodePat scope, app "filter" [var 0, var 2]]

flipJoin = alwaysRule lhs rhs 
  where
    lhs = app "join" [var 0, var 1, var 2]
    rhs = app "join" [var 0, var 2, var 1]

flipBinop op = alwaysRule lhs rhs
  where
    lhs = app op [var 0, var 1]
    rhs = app op [var 1, var 0]

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
