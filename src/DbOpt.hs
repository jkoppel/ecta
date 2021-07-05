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
tNode = const' "T"
fNode = const' "F"

data Pattern p =
  App Symbol [p]
  | Meta p
  | As (p, Int)
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
    matches (ConstrPattern (p, _)) n =
      case p of
        (App sym args) ->
          matchArgs args $
          List.filter (\(Edge sym' _) -> sym == sym') $
          nodeEdges n
        (As (p, idx)) -> List.map (\m -> (idx, n) : m) $ matches p n
        (Meta p) -> matchMeta p $ nodeEdges n
        (Var idx) -> [[(idx, n)]]
        (NodePat n') -> if n == n' then [[]] else []

    matchArgs args edges =
      concatMap ((List.map concat . mapM (uncurry matches))
                 . (\(Edge _ nodes) -> zip args nodes)) edges

    matchMeta pat edges =
      concatMap ((List.map concat . mapM (uncurry matches))
                 . (\(Edge _ nodes) -> [(pat, head nodes)])) edges


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

liftPat subst (ConstrPattern (pat, constrs)) =
  case pat of
    (App sym args) -> funcC sym (List.map (liftPat subst) args) constrs
    (Var idx) -> Maybe.fromJust $ List.lookup idx subst
    (NodePat n) -> n
    (As _) -> error "Cannot lift As"
    (Meta _) -> error "Cannot lift Meta"

liftClosedPat = liftPat []

rewriteMatch :: PatternMatch -> Rule -> Node -> Node
rewriteMatch PatternMatch { root, subst } rule n =
  atNode n root (\(Node ns) -> Node (ns ++ ns'))
  where
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

rewriteAll :: Rule -> Node -> Maybe Node
rewriteAll rule root =
  let root' = foldl (\root m -> rewriteMatch m rule root) root
              $ match (lhs rule) root in
    if root == root' then Nothing else Just root'

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

rule lhs rhs = Rule { lhs, rhs, DbOpt.pred = const True }

var x = ConstrPattern (Var x, EmptyConstraints)
varC x c = ConstrPattern (Var x, c)
app f xs = ConstrPattern (App f xs, EmptyConstraints)
appC f xs c = ConstrPattern (App f xs, c)
nodePat n = ConstrPattern (NodePat n, EmptyConstraints)
meta p = ConstrPattern (Meta p, EmptyConstraints)
as p i = ConstrPattern (As (p, i), EmptyConstraints)

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

filterToHidx = rule lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (eqP ckey rkey) rel
    rhs = hidxT [selectT ckey rel, cscopeT, filterT (eqT ckey (nodePat scope `dotT` ckey)) rel, rkey]

filterToOidx = rule lhs rhs
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

filterToOidx1 = rule lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (ckey `ltP` rkey) rel
    rhs = oidxT [ selectT ckey rel,
                  cscopeT,
                  filterT (ckey `eqT` (nodePat scope `dotT` ckey)) rel,
                  app "none" [], rkey]

filterToOidx2 = rule lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (rkey `ltP` ckey) rel
    rhs = oidxT [ selectT ckey rel,
                  nodePat scope,
                  filterT (ckey `eqT` (nodePat scope `dotT` ckey)) rel,
                  rkey, app "none" []]

splitFilter = rule lhs rhs
  where
    lhs = filterP (var 0 `andP` var 1) (var 2)
    rhs = filterT (var 0) $ filterT (var 1) (var 2)

mergeFilter = rule lhs rhs
  where
    lhs = filterP (var 0) $ filterP (var 1) (var 2)
    rhs = filterT (var 0 `andT` var 1) (var 2)

hoistFilter = rule lhs rhs
  where
    lhs = joinP (var 0) (filterP (var 1) (var 2)) (var 3)
    rhs = filterT (var 1) $ joinT (var 0) (var 2) (var 3)

elimJoin = rule lhs rhs
  where
    lhs = joinP (var 0) (var 1) (var 2)
    rhs = depjoinT (var 1) (filterT (var 0) (var 2))

flipJoin = rule lhs rhs
  where
    lhs = joinP (var 0) (var 1) (var 2)
    rhs = joinT (var 0) (var 2) (var 1)

flipBinop op = rule lhs rhs
  where
    lhs = app op [var 0, var 1]
    rhs = app op [var 1, var 0]

forceRtime = rule (var 0) (appC "constrained" [rtimeT, var 0] (mkEqConstraints [[path [0, 0], path [1, 0, 0]]]))

flipEq = flipBinop "eq"
flipAnd = flipBinop "and"

-- rewrite t =
--   fmap reducePartially $
--   (repeat' 5 $
--   try (rewriteAll splitFilter) `andThen`
--   try (rewriteAll mergeFilter) `andThen`
--   try (rewriteAll hoistFilter) `andThen`
--   try (rewriteAll filterToOidx) `andThen`
--   try (rewriteAll filterToOidx1) `andThen`
--   try (rewriteAll filterToOidx2) `andThen`
--   try (rewriteAll filterToHidx) `andThen`
--   try (rewriteAll elimJoin) `andThen`
--   try (rewriteAll flipAnd) `andThen`
--   try (rewriteAll flipEq) `andThen`
--   try (rewriteAll flipJoin)) `andThen`
--   (rewriteRoot forceRtime) $ liftClosedPat t

rewriteNoReduce t =
  fmap reducePartially
  $ (repeat' 5 $
     try (rewriteAll elimJoin)
     `andThen` try (rewriteAll filterToHidx)
    )
  `andThen` rewriteRoot forceRtime
  $ liftClosedPat t

rewrite t = reducePartially <$> rewriteNoReduce t

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

rtimeE = app "runtime" []
ctimeE = app "comptime" []
relationE n = app n [rtimeE]
joinE p r r' = app "join" [ctimeT, p, r, r']
nameE n = app n [rtimeE]
eqE t p p' = app "eq" [t, p, p']
ltE t p p' = app "lt" [t, p, p']
dotE t p p' = app "dot" [t, p, p']
filterE t p q = app "filter" [t, p, q]
depjoinE t p q = app "depjoin" [t, p, q]
hidxE t p s q k = app "hidx" [t, p, s, q, k]
selectE t p q = app "select" [t, p, q]
cscopeE = app "k" [ctimeE]
rscopeE = app "k" [rtimeE]

tpch3E = joinE (eqE rtimeE (nameE "c_custkey") (nameE "o_custkey"))
        (joinE (eqE rtimeE (nameE "l_orderkey") (nameE "o_orderkey"))
          (filterE rtimeE (ltE rtimeE (nameE "o_orderdate") (nameE "param1")) (relationE "orders"))
          (filterE rtimeE (ltE rtimeE (nameE "param1") (nameE "l_shipdate")) (relationE "lineitem")))
        (filterE rtimeE (eqE rtimeE (nameE "c_mktsegment") (nameE "param0")) (relationE "customer"))

elimJoinE = rule lhs rhs
  where
    lhs = joinP (var 0) (var 1) (var 2)
    rhs = depjoinE ctimeE (var 1) (filterE ctimeE (var 0) (var 2))

depjoinStageE = rule lhs rhs
  where
    lhs = depjoinE (var 0) (meta rtimeE `as` 1) (meta rtimeE `as` 2)
    rhs = depjoinE rtimeE (var 1) (var 2)

filterStageE = rule lhs rhs
  where
    lhs = filterP (meta rtimeE `as` 1) (meta rtimeE `as` 2)
    rhs = filterE rtimeE (var 1) (var 2)

eqStageE = rule lhs rhs
  where
    lhs = eqP (meta rtimeE `as` 1) (meta rtimeE `as` 2)
    rhs = eqE rtimeE (var 1) (var 2)

hidxStageE = rule lhs rhs
  where
    lhs = hidxE (var 0) (var 1) (var 2) (meta rtimeE `as` 3) (var 4)
    rhs = hidxE rtimeE (var 1) (var 2) (var 3) (var 4)

filterToHidxE = rule lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (eqP ckey rkey) rel
    rhs = hidxE ctimeE (selectE ctimeE ckey rel) cscopeE (filterE ctimeE (eqE ctimeE ckey (dotE ctimeE cscopeE ckey)) rel) rkey

rewriteEgraph t =
  repeat' 5
  (
    try (rewriteAll elimJoinE)
    `andThen` try (rewriteAll filterToHidxE)
    `andThen` try (rewriteAll depjoinStageE)
    `andThen` try (rewriteAll filterStageE)
    `andThen` try (rewriteAll eqStageE)
    `andThen` try (rewriteAll hidxStageE)
  ) $ liftClosedPat t
