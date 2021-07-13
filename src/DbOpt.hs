{-# LANGUAGE OverloadedStrings #-}

module DbOpt where

import Debug.Trace
import Control.Monad.State
import Term
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Language.Dot.Pretty as Dot
import Data.Memoization ( MemoCacheTag(..), memo2 )
import Data.Hashable ( Hashable, hashWithSalt )
import GHC.Generics (Generic)
import Data.Monoid

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

tEdge = Edge "T" []
fEdge = Edge "F" []
tNode = Node [tEdge]
fNode = Node [fEdge]
tfNode = Node [tEdge, fEdge]

data Pattern p =
    App Symbol [p]
  | Meta p
  | As (p, Int)
  | Var Int
  | NodePat Node
  deriving ( Eq, Ord, Show, Generic )

instance Hashable p => Hashable (Pattern p)

newtype ConstrPattern = ConstrPattern (Pattern ConstrPattern, EqConstraints)
  deriving ( Eq, Ord, Show, Generic )

instance Hashable ConstrPattern

newtype Subst = Subst [(Int, Node)]
  deriving ( Show )

instance Semigroup Subst where
  (<>) (Subst s) (Subst s') = Subst $ s ++ s'

instance Monoid Subst where
  mempty = Subst []

mkSubst :: [(Int, Node)] -> Subst
mkSubst = Subst

bindSubst :: Int -> Node -> Subst -> Subst
bindSubst i n (Subst s) = Subst $ (i, n) : s

lookupSubst :: Int -> Subst -> Node
lookupSubst x (Subst s) =
  case List.lookup x s of
    Just v -> v
    Nothing -> error $ "no binding for " ++ show x ++ " in " ++ show (fmap fst s)

data PatternMatch = PatternMatch { root :: Node
                                 , pat :: ConstrPattern
                                 , subst :: Subst
                                 }
  deriving ( Show )

matchRoot :: ConstrPattern -> Node -> [PatternMatch]
matchRoot p n =
  List.map (\s -> PatternMatch { root = n, pat = p, subst = s }) $ matches p n
  where
    matches :: ConstrPattern -> Node -> [Subst]
    matches (ConstrPattern (p, _)) n =
      case p of
        (App sym args) ->
          matchArgs args $
          List.filter (\(Edge sym' _) -> sym == sym') $
          nodeEdges n
        (As (p, idx)) -> List.map (bindSubst idx n) $ matches p n
        (Meta p) -> matchMetas p $ nodeEdges n
        (Var idx) -> [mkSubst [(idx, n)]]
        (NodePat n') -> if n == n' then [mempty] else []

    matchEdge :: [ConstrPattern] -> Edge -> [Subst]
    matchEdge pats edge =
      let children = edgeChildren edge in
      if length pats /= length children then [] else
        mconcat <$> zipWithM matches pats children

    matchArgs :: [ConstrPattern] -> [Edge] -> [Subst]
    matchArgs args = concatMap (matchEdge args)

    matchMeta :: ConstrPattern -> Edge -> [Subst]
    matchMeta pat edge =
      case edgeChildren edge of
        [] -> []
        (n : _) -> matches pat n

    matchMetas :: ConstrPattern -> [Edge] -> [Subst]
    matchMetas pat = concatMap (matchMeta pat)


match :: ConstrPattern -> Node -> [PatternMatch]
match p = crush (matchRoot p)

atNode :: Node -> Node -> (Node -> Node) -> Node
atNode n n' f = mapNodes (\n'' -> if n'' == n' then f n' else n'') n

data RuleRhs =
  FuncRhs (Subst -> Maybe ConstrPattern)
  | PatternRhs ConstrPattern

data Rule = Rule { lhs :: ConstrPattern
                 , rhs :: RuleRhs
                 , ruleName :: String }

liftPat' :: Subst -> ConstrPattern -> Node
liftPat' subst (ConstrPattern (pat, constrs)) =
  case pat of
    (App sym args) -> funcC sym (List.map (liftPat subst) args) constrs
    (Var idx) -> lookupSubst idx subst
    (NodePat n) -> n
    (As _) -> error "Cannot lift As"
    (Meta _) -> error "Cannot lift Meta"

liftPat = liftPat'
-- liftPat :: Subst -> ConstrPattern -> Node
-- liftPat = memo2 (NameTag "liftPat") liftPat'

liftClosedPat = liftPat mempty

rewriteMatch :: PatternMatch -> Rule -> Node -> Maybe Node
rewriteMatch PatternMatch { root, subst } Rule { lhs, rhs = PatternRhs rhs } n =
  return $ atNode n root (\(Node ns) -> Node (ns ++ ns'))
  where
    (Node ns') = liftPat subst rhs
rewriteMatch PatternMatch { root, subst } Rule { rhs = FuncRhs rhs } n = do
  (Node ns') <- liftPat subst <$> rhs subst
  return $ atNode n root (\(Node ns) -> Node (ns ++ ns'))

testTerm = filter' (binary "and" (eq (name "x") (name "x'")) (name "y")) (relation "test")

findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap f [] = Nothing
findMap f (x : xs) = case f x of
                       Just x' -> Just x'
                       Nothing -> findMap f xs

rewriteFirst :: Rule -> Node -> Maybe Node
rewriteFirst rule root =
  findMap (\m -> do
              root' <- rewriteMatch m rule root
              if root == root' then Nothing else return root')
  $ match (lhs rule) root

rewriteAll :: Rule -> Node -> Maybe Node
rewriteAll rule root = do
  traceM ("running " ++ ruleName rule)
  let matches = match (lhs rule) root
  traceM ("found " ++ show (length matches) ++ " matches")
  root' <- foldM (\root (i, m) ->
                    let root' = (try $ rewriteMatch m rule) root in
                      trace ("processed " ++ show i ++ " " ++ show (nodeCount <$> root')) root')
           root
           $ zip [0..] matches
  if root == root' then Nothing else return root'

rewriteRoot :: Rule -> Node -> Maybe Node
rewriteRoot rule root =
  foldM (\r m -> rewriteMatch m rule r) root
  $ matchRoot (lhs rule) root

try :: (Node -> Maybe Node) -> Node -> Maybe Node
try r n =
  case r n of
    Just n' -> Just n'
    Nothing -> Just n

andThen :: (Node -> Maybe Node) -> (Node -> Maybe Node) -> Node -> Maybe Node
andThen r r' n = r' =<< r n

repeat' :: Int -> (Node -> Maybe Node) -> Node -> Maybe Node
repeat' i r n =
  if i <= 0 then Just n else
  case r n of
    Nothing -> Just n
    Just n' ->
      if n == n' then Just n else repeat' (i - 1) r n'

rule' name lhs rhs = Rule { lhs, rhs = PatternRhs rhs, ruleName = name }
rule = rule' ""
frule' name lhs rhs = Rule { lhs, rhs = FuncRhs rhs, ruleName = name }
frule = frule' ""

var x = ConstrPattern (Var x, EmptyConstraints)
varC x c = ConstrPattern (Var x, c)
app f xs = ConstrPattern (App f xs, EmptyConstraints)
appC f xs c = ConstrPattern (App f xs, c)
nodePat n = ConstrPattern (NodePat n, EmptyConstraints)
meta p = ConstrPattern (Meta p, EmptyConstraints)
as p i = ConstrPattern (As (p, i), EmptyConstraints)

compIdx = 0
runIdx = 1

idxPath idx p = path (unPath p ++ [0, idx, 0])
compPath = idxPath compIdx
runPath = idxPath runIdx

andConstr' idx ps =
  (children, constr)
  where
    children = Node [ mkEdge "and" (tNode : map (const tNode) ps) EmptyConstraints
                    , mkEdge "and" (fNode : map (const tfNode) ps) EmptyConstraints
                    ]
    constr = mkEqConstraints [[path [0, idx, i], p] | (i, p) <- zip [1..] ps]

andConstr idx ps = andConstr' idx $ map (idxPath idx) ps

cAndRConstr name idx p q =
  (children, constr)
  where
    children = Node [ mkEdge "candr" [tNode, tNode, tNode] EmptyConstraints
                    , mkEdge "candr" [fNode, tfNode, tfNode] EmptyConstraints
                    ]
    constr = mkEqConstraints [[path [0, idx, 1], compPath p], [path [0, idx, 2], runPath p]]

notConstr idx p =
  (children, constr)
  where
    children = Node [ mkEdge "not" [tNode, fNode] EmptyConstraints
                    , mkEdge "not" [fNode, tNode] EmptyConstraints
                    ]
    constr = mkEqConstraints [[path [0, idx, 1], idxPath idx p]]

eqConstr idx p =
  (children, constr)
  where
    children = Node [ mkEdge "eq" [tNode] EmptyConstraints
                    , mkEdge "eq" [fNode] EmptyConstraints
                    ]
    constr = mkEqConstraints [[path [0, idx, 0], idxPath idx p]]

compConstr name idx p =
  (children, constr)
  where
    children = Node [ mkEdge "comp" [tNode] EmptyConstraints
                    , mkEdge "comp" [fNode] EmptyConstraints
                    ]
    constr = mkEqConstraints [[path [0, idx, 0], compPath p]]

bothT name p q = appC name [metaNode, p, q] $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = andConstr compIdx [path [1], path [2]]
    (run, cs') = andConstr runIdx [path [1], path [2]]

firstT name p q = appC name [metaNode, p, q] $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = eqConstr compIdx $ path [1]
    (run, cs') = eqConstr runIdx $ path [1]

filterT = bothT "filter"
eqT = bothT "eq"
andT = bothT "and"
ltT = bothT "lt"
selectT = bothT "select"

listT p q = appC "list" [metaNode, p, cscopeT, q] $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = andConstr compIdx [path [1], path [3]]
    (run, cs') = andConstr' runIdx [compPath $ path [1], runPath $ path [3]]

tupleT ts = appC "tuple" (metaNode : ts) $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = andConstr compIdx [path [i] | i <- [1..length ts]]
    (run, cs') = andConstr runIdx [path [i] | i <- [1..length ts]]

scalarT x = appC "scalar" [metaNode, x] $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = eqConstr compIdx (path [1])
    (run, cs') = compConstr "run" runIdx (path [1])

ctimeT = app "meta" [app "comp" [nodePat tNode], app "run" [nodePat fNode]]
rtimeT = app "meta" [app "comp" [nodePat fNode], app "run" [nodePat tNode]]
rctimeT = app "meta" [app "comp" [nodePat tNode], app "run" [nodePat tNode]]

rscopeT = app "scope" [rtimeT]
cscopeT = app "scope" [ctimeT]

dotT = firstT "dot"

relationT n = app n [ctimeT]

nameT n = app n [rctimeT]

noneT = nameT "none"

paramT n = app n [rtimeT]

joinT p r r' = app "join" [ctimeT, p, r, r']

simpleListT r = appC "simpleList" [metaNode, r] $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = eqConstr compIdx $ path [1]
    (run, cs') = compConstr "run" runIdx $ path [1]

depjoinT r r' = appC "depjoin" [metaNode, r, rscopeT, r'] $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = andConstr compIdx [path [1], path [3]]
    (run, cs') = andConstr runIdx [path [1], path [3]]

hidxT r r' k = appC "hidx" [metaNode, r, cscopeT, r', k] $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = andConstr compIdx [path [1], path [3], path[4]]
    (run, cs') = andConstr' runIdx [compPath $ path [1], runPath $ path [3], runPath $ path [4]]

oidxT r r' k k' = appC "oidx" [metaNode, r, cscopeT, r', k, k'] $ combineEqConstraints cs cs'
  where
    metaNode = app "meta" [nodePat comp, nodePat run]
    (comp, cs) = andConstr compIdx [path [1], path [3], path[4], path [5]]
    (run, cs') = andConstr' runIdx [compPath $ path [1], runPath $ path [3], runPath $ path [4], runPath $ path [5]]

filterP x y = app "filter" [var (-1), x, y]
andP x y = app "and" [var (-1), x, y]
ltP x y = app "lt" [var (-1), x, y]
eqP x y = app "eq" [var (-1), x, y]
dotP x y = app "dot" [var (-1), x, y]
joinP x y z = app "join" [var (-1), x, y, z]

filterToHidx = rule' "filter-to-hidx" lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (eqP ckey rkey) rel
    rhs = hidxT (selectT ckey rel) (filterT (eqT ckey (cscopeT `dotT` ckey)) rel) rkey

-- filterToOidx = rule' "filter-to-oidx" lhs rhs
--   where
--     ckey = var 0
--     rkey1 = var 1
--     rkey2 = var 2
--     rel = var 3
--     lhs = filterP ((rkey1 `ltP` ckey) `andP` (ckey `ltP` rkey2)) rel
--     rhs = oidxT (selectT ckey rel) (filterT (ckey `eqT` (cscopeT `dotT` ckey)) rel) rkey1 rkey2

filterToOidx1 = rule' "filter-to-oidx1" lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (ckey `ltP` rkey) rel
    rhs = oidxT (selectT ckey rel) (filterT (ckey `eqT` (cscopeT `dotT` ckey)) rel) noneT rkey

filterToOidx2 = rule' "filter-to-oidx2" lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterP (rkey `ltP` ckey) rel
    rhs = oidxT (selectT ckey rel) (filterT (ckey `eqT` (cscopeT `dotT` ckey)) rel) rkey noneT

splitFilter = rule' "split-filter" lhs rhs
  where
    lhs = filterP (var 0 `andP` var 1) (var 2)
    rhs = filterT (var 0) $ filterT (var 1) (var 2)

mergeFilter = rule' "merge-filter" lhs rhs
  where
    lhs = filterP (var 0) $ filterP (var 1) (var 2)
    rhs = filterT (var 0 `andT` var 1) (var 2)

hoistFilter = rule' "hoist-filter" lhs rhs
  where
    lhs = joinP (var 0) (filterP (var 1) (var 2)) (var 3)
    rhs = filterT (var 1) $ joinT (var 0) (var 2) (var 3)

elimJoin = rule' "elim-join" lhs rhs
  where
    lhs = joinP (var 0) (var 1) (var 2)
    rhs = depjoinT (var 1) (filterT (var 0) (var 2))

flipJoin = rule' "flip-join" lhs rhs
  where
    lhs = joinP (var 0) (var 1) (var 2)
    rhs = joinT (var 0) (var 2) (var 1)

flipBinop op = rule lhs rhs
  where
    lhs = app op [var 0, var 1]
    rhs = app op [var 1, var 0]

bothEq x y = if x == y then x else error ("expected equal " ++ show x ++ " " ++ show y)

schema' :: Symbol -> [[Symbol]] -> [Symbol]
schema' "orders" _ = ["o_orderkey", "o_custkey", "o_orderstatus", "o_totalprice", "o_orderdate", "o_orderpriority", "o_clerk", "o_shippriority", "o_comment"]
schema' "customer" _ = ["c_custkey", "c_name", "c_address", "c_nationkey", "c_phone", "c_acctbal", "c_mktsegment", "c_comment"]
schema' "lineitem" _ = ["l_orderkey", "l_partkey", "l_suppkey", "l_linenumber", "l_quantity", "l_extendedprice", "l_discount", "l_tax", "l_returnflag", "l_linestatus", "l_shipdate", "l_commitdate", "l_receiptdate", "l_shipinstruct", "l_shipmode", "l_comment"]
schema' "filter" [_, _, s] = s
schema' "oidx" [_, _, _, v, _, _] = v
schema' "hidx" [_, _, _, v, _] = v
schema' "join" [_, _, a, b] = List.sort $ a++b
schema' "depjoin" [_, v, _, v'] = List.sort $ v ++ v'
schema' "scalar" [_, s] = s
schema' "dot" [_, _, s] = s
schema' "list" [_, _, s] = s
schema' "simpleList" [_, s] = s
schema' "tuple" (_ : xs) = concat xs
schema' "T" _ = []
schema' "F" _ = []
schema' n _ = [n]

-- schema n xs = trace (show (n, xs)) (schema' n xs)
schema = schema'

schemaOf node =
  Maybe.fromJust $ Map.lookup (nodeIdentity node) (annotate bothEq schema node)

data Kind = Relation | Scalar | MetaData
  deriving ( Eq, Show )

kind :: Symbol -> [Kind] -> Kind
kind n _
  | n == "filter" || n == "select" || n == "depjoin" || n == "join" || n == "oidx" || n == "hidx" || n == "list" || n == "scalar" = Relation
  | n == "eq" || n == "lt" = Scalar
  | otherwise = MetaData

kindOf node =
  Maybe.fromJust $ Map.lookup (nodeIdentity node) (annotate bothEq kind node)

isStructure n = n == "oidx" || n == "hidx" || n == "list" || n == "scalar"

hasStructure :: Symbol -> [Bool] -> Bool
hasStructure n xs = isStructure n || or xs

hasStructureOf node =
  Maybe.fromJust $ Map.lookup (nodeIdentity node) (annotate (||) hasStructure node)

introList = frule' "intro-list" lhs rhs
  where
    lhs = var 0
    rhs subst = do
      let node = lookupSubst 0 subst
      if hasStructureOf node then Nothing else do
        let schm = schemaOf node
        return $ listT (var 0) (tupleT [scalarT $ nameT n | n <- schm])

introSimpleList = frule' "intro-simple-list" lhs rhs
  where
    lhs = var 0
    rhs subst = return $ simpleListT (var 0)

forceRtime = rule (var 0) rhs
  where
    rhs = appC "constrained" [rtimeT, var 0] (mkEqConstraints [[path [0, 1, 0], path [1, 0, 1, 0]]])

flipEq = flipBinop "eq"
flipAnd = flipBinop "and"

rewriteNoReduce t =
  (repeat' 5 $
    try (rewriteAll splitFilter)
    `andThen` try (rewriteAll mergeFilter)
    `andThen` try (rewriteAll hoistFilter)
    `andThen` try (rewriteAll flipAnd)
    `andThen` try (rewriteAll flipEq)
    `andThen` try (rewriteAll flipJoin)
  )
  `andThen` (repeat' 5 $
     try (rewriteAll elimJoin)
     `andThen` try (rewriteAll filterToHidx)
     -- `andThen` try (rewriteAll filterToOidx)
     `andThen` try (rewriteAll filterToOidx1)
     `andThen` try (rewriteAll filterToOidx2)
    )
  `andThen` try (rewriteAll introList)
  `andThen` rewriteRoot forceRtime
  $ liftClosedPat t

rewrite t = reducePartially <$> rewriteNoReduce t

tpch3 =
  joinT
    (eqT (nameT "c_custkey") (nameT "o_custkey"))
    ( joinT
        (eqT (nameT "l_orderkey") (nameT "o_orderkey"))
        (filterT (ltT (nameT "o_orderdate") (paramT "param1")) (relationT "orders"))
        (filterT (ltT (paramT "param1") (nameT "l_shipdate")) (relationT "lineitem"))
    )
    (filterT (eqT (nameT "c_mktsegment") (paramT "param0")) (relationT "customer"))

containsEdgeLabel lbl =
  crush (\(Node es) -> Any (any (\e -> edgeSymbol e == lbl) es))
containsConstr = containsEdgeLabel "constrained"

simple = filterT (eqT (nameT "test") (nameT "test")) $ relationT "lineitem"

simpleC = appC "constrained" [rtimeT, simple] (mkEqConstraints [[path [0, 1, 0], path [1, 0, 1, 0]]])

dumpDot (Just x) = Dot.renderDot $ toDot x
prettyDot (Just x) = Dot.prettyPrintDot $ toDot x

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
