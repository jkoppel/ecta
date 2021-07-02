{-# LANGUAGE OverloadedStrings #-}

module DbOpt where

import Debug.Trace
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Language.Dot.Pretty as Dot

import ECTA
import Paths

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
tNode = const' "T"
fNode = const' "F"

data Pattern p =
  App Symbol [p]
  | Var Int
  | NodePat Node
  deriving ( Eq, Ord, Show )

newtype ConstrPattern = ConstrPattern (Pattern ConstrPattern, EqConstraints)
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

rewriteRoot :: Rule -> Node -> Maybe Node
rewriteRoot rule root =
  Just $
  foldl (\r m -> rewriteMatch m rule r) root
  $ matchRoot (lhs rule) root

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

alwaysRule lhs rhs = Rule { lhs, rhs, DbOpt.pred = const True }

var x = ConstrPattern (Var x, EmptyConstraints)
varC x c = ConstrPattern (Var x, c)
app f xs = ConstrPattern (App f xs, EmptyConstraints)
appC f xs c = ConstrPattern (App f xs, c)
nodePat n = ConstrPattern (NodePat n, EmptyConstraints)

andConstr p p' =
  (nodePat node, constr)
  where
    node = Node [mkEdge "=" [tNode, tNode, tNode] EmptyConstraints,
                 mkEdge "=" [fNode, tNode, fNode] EmptyConstraints,
                 mkEdge "=" [fNode, fNode, tNode] EmptyConstraints,
                 mkEdge "=" [fNode, fNode, fNode] EmptyConstraints
                ]
    constr = mkEqConstraints [[path [0, 1], p], [path [0, 2], p']]

tEdge = mkEdge "=" [tNode] EmptyConstraints
fEdge = mkEdge "=" [fNode] EmptyConstraints

copyConstr p =
  (nodePat node, constr)
  where
    node = Node [ tEdge, fEdge ]
    constr = mkEqConstraints [[path [0, 0], p]]
    
bothT name x y = appC name [metaNode, x, y] constrs
  where
    (metaNode, constrs) = andConstr (path [1, 0, 0]) (path [2, 0, 0])

firstT name x y = appC name [metaNode, x, y] constrs
  where
    (metaNode, constrs) = copyConstr $ path [1, 0, 0]

secondT name x y = appC name [metaNode, x, y] constrs
  where
    (metaNode, constrs) = copyConstr $ path [2, 0, 0]

filterT = secondT "filter"
eqT = bothT "eq"
andT = bothT "and"
ltT = bothT "lt"
selectT = secondT "select"
dotT x y = app "dot" [x, y]

rtimeT = nodePat $ Node [tEdge]
ctimeT = nodePat $ Node [fEdge]

cscopeT = ctimeT
rscopeT = rtimeT

relationT n = app n [rtimeT] -- should be ctime (later)
nameT = relationT
joinT p r r' = app "join" [ctimeT, p, r, r']
depjoinT r r' = appC "depjoin" [metaNode, r, nodePat scope, r'] constrs
  where
    (metaNode, constrs) = andConstr (path [1, 0, 0]) (path [3, 0, 0])

addConstr c = combineEqConstraints (mkEqConstraints c)

idxT name xs = appC name (metaNode : xs) constrs
  where
    (metaNode, constrs) = copyConstr (path [3, 0, 0])
    
hidxT = idxT "hidx"
oidxT = idxT "oidx"

filterP x y = app "filter" [var (-1), x, y]
andP x y = app "and" [var (-1), x, y]
ltP x y = app "lt" [var (-1), x, y]
eqP x y = app "eq" [var (-1), x, y]
dotP x y = app "dot" [var (-1), x, y]
joinP x y z = app "join" [var (-1), x, y, z]

filterToHidx = alwaysRule lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (eqP ckey rkey) rel
    rhs = hidxT [selectT ckey rel, cscopeT, filterT (eqT ckey (nodePat scope `dotT` ckey)) rel, rkey]

filterToOidx = alwaysRule lhs rhs 
  where
    ckey = var 0
    rkey1 = var 1
    rkey2 = var 2
    rel = var 3
    lhs = filterP ((rkey1 `ltP` ckey) `andP` (ckey `ltP` rkey2)) rel
    rhs = oidxT [ selectT ckey rel,
                  cscopeT,
                  filterT (ckey `eqT` (nodePat scope `dotT` ckey)) rel,
                  rkey1, rkey2
                ]

filterToOidx1 = alwaysRule lhs rhs 
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (ckey `ltP` rkey) rel
    rhs = oidxT [ selectT ckey rel,
                  cscopeT,
                  filterT (ckey `eqT` (nodePat scope `dotT` ckey)) rel,
                  app "none" [], rkey]

filterToOidx2 = alwaysRule lhs rhs 
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (rkey `ltP` ckey) rel
    rhs = oidxT [ selectT ckey rel,
                  nodePat scope,
                  filterT (ckey `eqT` (nodePat scope `dotT` ckey)) rel,
                  rkey, app "none" []]

splitFilter = alwaysRule lhs rhs 
  where
    lhs = filterP (var 0 `andP` var 1) (var 2)
    rhs = filterT (var 0) $ filterT (var 1) (var 2)

mergeFilter = alwaysRule lhs rhs 
  where
    lhs = filterP (var 0) $ filterP (var 1) (var 2)
    rhs = filterT (var 0 `andT` var 1) (var 2)

hoistFilter = alwaysRule lhs rhs 
  where
    lhs = joinP (var 0) (filterP (var 1) (var 2)) (var 3)
    rhs = filterT (var 1) $ joinT (var 0) (var 2) (var 3)

elimJoin = alwaysRule lhs rhs 
  where
    lhs = joinP (var 0) (var 1) (var 2)
    rhs = depjoinT (var 1) (filterT (var 0) (var 2))

flipJoin = alwaysRule lhs rhs 
  where
    lhs = joinP (var 0) (var 1) (var 2)
    rhs = joinT (var 0) (var 2) (var 1)

flipBinop op = alwaysRule lhs rhs
  where
    lhs = app op [var 0, var 1]
    rhs = app op [var 1, var 0]

inject :: ConstrPattern -> Rule
inject = alwaysRule (var 0)

forceRtime = alwaysRule (var 0) (appC "constrained" [rtimeT, var 0] (mkEqConstraints [[path [0, 0], path [1, 0, 0]]]))

flipEq = flipBinop "eq"
flipAnd = flipBinop "and"

dummyNode = Node [mkEdge "?" [] EmptyConstraints]

rewrite t =
  fmap reducePartially $
  (rewriteFirst $ inject t) `andThen`
  (repeat' 5 $
  try (rewriteFirst splitFilter) `andThen`
  try (rewriteFirst mergeFilter) `andThen`
  try (rewriteFirst hoistFilter) `andThen`
  try (rewriteFirst filterToOidx) `andThen`
  try (rewriteFirst filterToOidx1) `andThen`
  try (rewriteFirst filterToOidx2) `andThen`
  try (rewriteFirst filterToHidx) `andThen`
  try (rewriteFirst elimJoin) `andThen`
  try (rewriteFirst flipAnd) `andThen`
  try (rewriteFirst flipEq) `andThen`
  try (rewriteFirst flipJoin)) `andThen`
  (rewriteRoot forceRtime) $ dummyNode

rewriteTest t =
  fmap reducePartially $
  (rewriteFirst $ inject t)
  `andThen` (repeat' 5 $
             try (rewriteFirst elimJoin)
             `andThen` try (rewriteFirst filterToHidx)
             -- `andThen` try (rewriteFirst flipJoin) `andThen`
             -- try (rewriteFirst splitFilter) `andThen`
             -- -- try (rewriteFirst mergeFilter) `andThen`
             -- try (rewriteFirst hoistFilter)
             -- -- `andThen` try (rewriteFirst filterToHidx)
            )
  `andThen` (rewriteRoot forceRtime)
  $ dummyNode

rewriteTestNoReduce t =
  (rewriteFirst $ inject t)
  -- `andThen` (repeat' 5 $
  --            try (rewriteFirst elimJoin) `andThen`
  --            try (rewriteFirst flipJoin) `andThen`
  --            try (rewriteFirst splitFilter) `andThen`
  --            -- try (rewriteFirst mergeFilter) `andThen`
  --            try (rewriteFirst hoistFilter) `andThen`
  --            try (rewriteFirst filterToHidx))
  $ dummyNode

rewriteTestAlwaysReduce t =
  (reduce (rewriteFirst $ inject t))
  `andThen` (
             reduce (try (rewriteFirst elimJoin))
             -- `andThen` reduce (try (rewriteFirst filterToHidx))
             -- `andThen` reduce (try (rewriteFirst flipJoin)) `andThen`
             -- reduce (try (rewriteFirst splitFilter)) `andThen`
             -- -- try (rewriteFirst mergeFilter) `andThen`
             -- reduce (try (rewriteFirst hoistFilter))
             -- -- `andThen` reduce (try (rewriteFirst filterToHidx))
            )
  $ dummyNode
  where reduce tf n = reducePartially <$> tf n

schema "orders" _ = ["o_orderkey", "o_custkey", "o_orderstatus", "o_totalprice", "o_orderdate", "o_orderpriority", "o_clerk", "o_shippriority", "o_comment"]
schema "customer" _ = ["c_custkey", "c_name", "c_address", "c_nationkey", "c_phone", "c_acctbal", "c_mktsegment", "c_comment"]
schema "lineitem" _ = ["l_orderkey", "l_partkey", "l_suppkey", "l_linenumber", "l_quantity", "l_extendedprice", "l_discount", "l_tax", "l_returnflag", "l_linestatus", "l_shipdate", "l_commitdate", "l_receiptdate", "l_shipinstruct", "l_shipmode", "l_comment"]
schema "filter" [_, s] = s
schema "oidx" [_, _, _, v, _, _] = v
schema "hidx" [_, _, _, v, _, _] = v
schema "join" [_, _, a, b] = a++b
schema "depjoin" [_, _, _, v] = v

tpch3 = joinT (eqT (nameT "c_custkey") (nameT "o_custkey"))
        (joinT (eqT (nameT "l_orderkey") (nameT "o_orderkey"))
          (filterT (ltT (nameT "o_orderdate") (nameT "param1")) (relationT "orders"))
          (filterT (ltT (nameT "param1") (nameT "l_shipdate")) (relationT "lineitem")))
        (filterT (eqT (nameT "c_mktsegment") (nameT "param0")) (relationT "customer"))

dumpDot (Just x) = Dot.prettyPrintDot $ toDot x

ntuples :: Symbol -> [Int] -> Int
ntuples "filter" [_, _, n] = n
ntuples "select" [_, _, n] = n
ntuples "oidx" [_, k, _, v, _, _] = ((v `div` k) * 30)
ntuples "hidx" [_, k, _, v, _, _] = (v `div` k)
ntuples "join" [_, _, a, b] = (max (a) (b))
ntuples "depjoin" [_, k, _, v] = (max (k) (v))
ntuples "lineitem" _ = 6000000
ntuples "orders" _ = 1500000
ntuples "customer" _ = 150000
ntuples "constrained" xs = minimum xs
ntuples _ _ = 0
