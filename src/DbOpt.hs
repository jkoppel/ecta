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
    App (Maybe Symbol) [p]
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
        (App (Just sym) args) ->
          matchArgs matchEdge args $
          List.filter (\(Edge sym' _) -> sym == sym') $
          nodeEdges n
        (App Nothing args) -> matchArgs matchEdgeLoose args $ nodeEdges n
        (As (p, idx)) -> List.map (bindSubst idx n) $ matches p n
        (Meta p) -> matchMetas p $ nodeEdges n
        (Var idx) -> [mkSubst [(idx, n)]]
        (NodePat n') -> if n == n' then [mempty] else []

    matchEdge :: [ConstrPattern] -> Edge -> [Subst]
    matchEdge pats edge =
      let children = edgeChildren edge in
      if length pats /= length children then [] else
        mconcat <$> zipWithM matches pats children

    matchEdgeLoose :: [ConstrPattern] -> Edge -> [Subst]
    matchEdgeLoose pats edge =
      let children = edgeChildren edge in
        mconcat <$> zipWithM matches pats children

    matchArgs me args = concatMap (me args)

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
    (App (Just sym) args) -> funcC sym (List.map (liftPat subst) args) constrs
    (Var idx) -> lookupSubst idx subst
    (NodePat n) -> n
    (App Nothing _) -> error "Cannot lift App"
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
                      trace ("processed " ++ show i ++ " " ++ "nodes " ++ (show $ nodeCount <$> root') ++ " edges " ++ (show $ edgeCount <$> root')) root')
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

rule' name lhs rhs = Rule { lhs, rhs = PatternRhs rhs, ruleName = name }
rule = rule' ""
frule' name lhs rhs = Rule { lhs, rhs = FuncRhs rhs, ruleName = name }
frule = frule' ""

var x = ConstrPattern (Var x, EmptyConstraints)
varC x c = ConstrPattern (Var x, c)
app f xs = ConstrPattern (App (Just f) xs, EmptyConstraints)
appC f xs c = ConstrPattern (App (Just f) xs, c)
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

relationT n = app "relation" [ctimeT, app n []]

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
schema' "relation" [_, ["orders"]] = ["o_orderkey", "o_custkey", "o_orderstatus", "o_totalprice", "o_orderdate", "o_orderpriority", "o_clerk", "o_shippriority", "o_comment"]
schema' "relation" [_, ["customer"]] = ["c_custkey", "c_name", "c_address", "c_nationkey", "c_phone", "c_acctbal", "c_mktsegment", "c_comment"]
schema' "relation" [_, ["lineitem"]] = ["l_orderkey", "l_partkey", "l_suppkey", "l_linenumber", "l_quantity", "l_extendedprice", "l_discount", "l_tax", "l_returnflag", "l_linestatus", "l_shipdate", "l_commitdate", "l_receiptdate", "l_shipinstruct", "l_shipmode", "l_comment"]
schema' "filter" [_, _, s] = s
schema' "oidx" [_, _, _, v, _, _] = v
schema' "hidx" [_, _, _, v, _] = v
schema' "join" [_, _, a, b] = List.sort $ a++b
schema' "depjoin" [_, v, _, v'] = List.sort $ v ++ v'
schema' "depjoin" [_, v, v'] = List.sort $ v ++ v'
schema' "scalar" [_, s] = s
schema' "dot" [_, _, s] = s
schema' "list" [_, _, s] = s
schema' "simpleList" [_, s] = s
schema' "tuple" (_ : xs) = concat xs
schema' "T" _ = []
schema' "F" _ = []
schema' n _ = [n]

schemaE :: Symbol -> [[Symbol]] -> [Symbol]
schemaE "relation" [_, _, ["orders"]] = ["o_orderkey", "o_custkey", "o_orderstatus", "o_totalprice", "o_orderdate", "o_orderpriority", "o_clerk", "o_shippriority", "o_comment"]
schemaE "relation" [_, _, ["customer"]] = ["c_custkey", "c_name", "c_address", "c_nationkey", "c_phone", "c_acctbal", "c_mktsegment", "c_comment"]
schemaE "relation" [_, _, ["lineitem"]] = ["l_orderkey", "l_partkey", "l_suppkey", "l_linenumber", "l_quantity", "l_extendedprice", "l_discount", "l_tax", "l_returnflag", "l_linestatus", "l_shipdate", "l_commitdate", "l_receiptdate", "l_shipinstruct", "l_shipmode", "l_comment"]
schemaE "filter" [_, _, _, s] = s
schemaE "oidx" [_, _, _, _, v, _, _] = v
schemaE "hidx" [_, _, _, _, v, _] = v
schemaE "join" [_, _, _, a, b] = List.sort $ a++b
schemaE "depjoin" [_, _, v, _, v'] = List.sort $ v ++ v'
schemaE "depjoin" [_, _, v, v'] = List.sort $ v ++ v'
schemaE "scalar" [_, _, s] = s
schemaE "dot" [_, _, _, s] = s
schemaE "list" [_, _, _, s] = s
schemaE "tuple" (_ : _ : xs) = concat xs
schemaE "T" _ = []
schemaE "F" _ = []
schemaE n _ = [n]

schemaOf' s node =
  Maybe.fromJust $ Map.lookup (nodeIdentity node) (annotate bothEq s node)

schemaOf = schemaOf' schema'
schemaOfE = schemaOf' schemaE

data Kind = Relation | Scalar | MetaData
  deriving ( Eq, Show )

kind :: Symbol -> [Kind] -> Kind
kind n _
  | n == "filter" || n == "select" || n == "depjoin" || n == "join" ||
    n == "oidx" || n == "hidx" || n == "list" || n == "scalar" || n == "relation" = Relation
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
      case kindOf node of
        Relation ->
          do
            let schm = schemaOf node
            return $ listT (var 0) (tupleT [scalarT $ nameT n | n <- schm])
        _ -> Nothing

rtimeConstr x = appC "constrained" [rtimeT, x] (mkEqConstraints [[path [0, 1, 0], path [1, 0, 1, 0]]])

forceRtime = rule (var 0) rhs
  where
    rhs = rtimeConstr (var 0)

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
  $ liftClosedPat (rtimeConstr t)

rewriteSimple t =
  reducePartially <$>
  (-- try (rewriteAll elimJoin)
   try (rewriteAll filterToHidx)
  -- `andThen` try (rewriteAll filterToOidx2)
  `andThen` try (rewriteAll introList)) (liftClosedPat (rtimeConstr t))

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

tpch3' =
  (filterT (eqT (nameT "c_mktsegment") (paramT "param0")) (relationT "customer"))

containsEdgeLabel lbl n =
  getAny $ crush (\(Node es) -> Any (any (\e -> edgeSymbol e == lbl) es)) n
containsConstr = containsEdgeLabel "constrained"

dumpStats (Just x) = print $ "nodes " ++ (show $ nodeCount x) ++ " edges " ++ (show $ edgeCount x)
dumpDot (Just x) = Dot.renderDot $ toDot x
prettyDot (Just x) = Dot.prettyPrintDot $ toDot x

ntuples :: Symbol -> [Int] -> Int
ntuples "filter" [_, _, n] = n
ntuples "select" [_, _, n] = n
ntuples "oidx" [_, k, _, v, _, _] = (v `div` k) * 30
ntuples "hidx" [_, k, _, v, _, _] = v `div` k
ntuples "join" [_, _, a, b] = max a b
ntuples "depjoin" [_, k, _, v] = (max (k) (v))
ntuples "lineitem" _ = 6000000
ntuples "orders" _ = 1500000
ntuples "customer" _ = 150000
ntuples "constrained" xs = minimum xs
ntuples _ _ = 0

true = nodePat $ liftClosedPat $ app "T" []
false = nodePat $ liftClosedPat $ app "F" []
relationE n = app "relation" [true, false, app n []]
joinE p r r' = app "join" [true, false, p, r, r']
nameE n = app n [true, true]
eqE t t' p p' = app "eq" [t, t', p, p']
ltE t t' p p' = app "lt" [t, t', p, p']
andE t t' p p' = app "and" [t, t', p, p']
dotE t t' p p' = app "dot" [t, t', p, p']
filterE t t' p q = app "filter" [t, t', p, q]
depjoinE t t' p q = app "depjoin" [t, t', p, q]
hidxE t t' p s q k = app "hidx" [t, t', p, s, q, k]
oidxE t t' p s q k k' = app "oidx" [t, t', p, s, q, k, k']
listE t t' p s q = app "list" [t, t', p, s, q]
tupleE t t' ps = app "tuple" (t : t' : ps)
scalarE t t' p = app "scalar" [t, t', p]
noneE = app "none" [true, true]
selectE t t' p q = app "select" [t, t', p, q]
cscopeE = nodePat $ liftClosedPat $ app "k" [true, false]
rscopeE = nodePat $ liftClosedPat $ app "k" [false, true]

tpch3E = joinE (eqE false false (nameE "c_custkey") (nameE "o_custkey"))
        (joinE (eqE false false (nameE "l_orderkey") (nameE "o_orderkey"))
          (filterE false false (ltE false false (nameE "o_orderdate") (nameE "param1")) (relationE "orders"))
          (filterE false false (ltE false false (nameE "param1") (nameE "l_shipdate")) (relationE "lineitem")))
         (filterE false false (eqE false false (nameE "c_mktsegment") (nameE "param0")) (relationE "customer"))

ignore = var (-1)
elimJoinE = rule lhs rhs
  where
    lhs = joinE (var 0) (var 1) (var 2)
    rhs = depjoinE false false (var 1) (filterE false false (var 0) (var 2))

splitFilterE = rule' "split-filter-e" lhs rhs
  where
    lhs = filterE ignore ignore (andE ignore ignore (var 0) (var 1)) (var 2)
    rhs = filterE false false (var 0) $ filterE false false (var 1) (var 2)

mergeFilterE = rule' "merge-filter-e" lhs rhs
  where
    lhs = filterE ignore ignore (var 0) $ filterE ignore ignore (var 1) (var 2)
    rhs = filterE false false (andE false false (var 0) (var 1)) (var 2)

hoistFilterE = rule lhs rhs
  where
    lhs = joinE (var 0) (filterE ignore ignore (var 1) (var 2)) (var 3)
    rhs = filterE false false (var 1) $ joinE (var 0) (var 2) (var 3)

flipJoinE = rule lhs rhs
  where
    lhs = joinE (var 0) (var 1) (var 2)
    rhs = joinE (var 0) (var 2) (var 1)

flipBinopE op = rule lhs rhs
  where
    lhs = app op [ignore, ignore, var 1, var 2]
    rhs = app op [false, false, var 2, var 1]

flipEqE = flipBinopE "eq"
flipAndE = flipBinopE "and"

anyApp args = ConstrPattern (App Nothing args, EmptyConstraints)

bothStageE1 name c = rule' (name ++ "-stage-c") lhs rhs
  where
    lhs = c false (var 0) (anyApp [true] `as` 1) (anyApp [true] `as` 2)
    rhs = c true (var 0) (var 1) (var 2)
bothStageE2 name c = rule' (name ++ "-stage-r") lhs rhs
  where
    lhs = c (var 0) false (anyApp [ignore, true] `as` 1) (anyApp [ignore, true] `as` 2)
    rhs = c (var 0) true (var 1) (var 2)

depjoinStageE1 = bothStageE1 "depjoin" depjoinE
depjoinStageE2 = bothStageE2 "depjoin" depjoinE
filterStageE1 = bothStageE1 "filter" filterE
filterStageE2 = bothStageE2 "filter" filterE
eqStageE1 = bothStageE1 "eq" eqE
eqStageE2 = bothStageE2 "eq" eqE
ltStageE1 = bothStageE1 "lt" ltE
ltStageE2 = bothStageE2 "lt" ltE
andStageE1 = bothStageE1 "and" andE
andStageE2 = bothStageE2 "and" andE
dotStageE1 = bothStageE1 "dot" dotE
dotStageE2 = bothStageE2 "dot" dotE
selectStageE1 = bothStageE1 "select" selectE
selectStageE2 = bothStageE2 "select" selectE

hidxStageE1 = rule' "hidx-stage" lhs rhs
  where
    lhs = hidxE false (var 0) (anyApp [true] `as` 1) (var 2) (anyApp [true] `as` 3) (anyApp [true] `as` 4)
    rhs = hidxE true (var 0) (var 1) (var 2) (var 3) (var 4)
hidxStageE2 = rule' "hidx-stage" lhs rhs
  where
    lhs = hidxE (var 0) false (anyApp [true] `as` 1) (var 2) (anyApp [ignore, true] `as` 3) (anyApp [ignore, true] `as` 4)
    rhs = hidxE (var 0) true (var 1) (var 2) (var 3) (var 4)

oidxStageE1 = rule' "oidx-stage" lhs rhs
  where
    lhs = oidxE false (var 0) (anyApp [true] `as` 1) (var 2) (anyApp [true] `as` 3) (anyApp [true] `as` 4) (anyApp [true] `as` 5)
    rhs = oidxE true (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
oidxStageE2 = rule' "oidx-stage" lhs rhs
  where
    lhs = oidxE (var 0) false (anyApp [true] `as` 1) (var 2) (anyApp [ignore, true] `as` 3) (anyApp [ignore, true] `as` 4) (anyApp [ignore, true] `as` 5)
    rhs = oidxE (var 0) true (var 1) (var 2) (var 3) (var 4) (var 5)

listStageE1 = rule' "list-stage" lhs rhs
  where
    lhs = listE false (var 0) (anyApp [true] `as` 1) (var 2) (anyApp [true] `as` 3)
    rhs = listE true (var 0) (var 1) (var 2) (var 3)
listStageE2 = rule' "list-stage" lhs rhs
  where
    lhs = listE (var 0) false (anyApp [true] `as` 1) (var 2) (anyApp [ignore, true] `as` 3)
    rhs = listE (var 0) true (var 1) (var 2) (var 3)

scalarStageE = rule' "scalar-stage" lhs rhs
  where
    lhs = scalarE ignore ignore (anyApp [true] `as` 1)
    rhs = scalarE true true (var 1)

filterToHidxE = rule lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterE ignore ignore (eqE ignore ignore ckey rkey) rel
    rhs = hidxE false false (selectE false false ckey rel) cscopeE (filterE false false (eqE false false ckey (dotE false false cscopeE ckey)) rel) rkey

filterToOidx1E = rule' "filter-to-oidx1-e" lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterE ignore ignore (ltE ignore ignore ckey rkey) rel
    rhs = oidxE false false (selectE false false ckey rel) cscopeE (filterE false false (eqE false false ckey (dotE false false cscopeE ckey)) rel) noneE rkey

filterToOidx2E = rule' "filter-to-oidx2-e" lhs rhs
  where
    ckey = var 0
    rkey = var 1
    rel = var 2
    lhs = filterE ignore ignore (ltE ignore ignore rkey ckey) rel
    rhs = oidxE false false (selectE false false ckey rel) cscopeE (filterE false false (eqE false false ckey (dotE false false cscopeE ckey)) rel) rkey noneE

introListE = frule' "intro-list" lhs rhs
  where
    lhs = var 0
    rhs subst = 
      let node = lookupSubst 0 subst in
      case kindOf node of
        Relation ->
          let schm = schemaOfE node in
            return $ listE false false (var 0) cscopeE (tupleE true true [scalarE false false (dotE false false cscopeE $ nameE n) | n <- schm])
        _ -> Nothing

rewriteEgraph =
  ( repeat' 5 $
    try (rewriteAll splitFilterE)
    `andThen` try (rewriteAll mergeFilterE)
    `andThen` try (rewriteAll hoistFilterE)
    `andThen` try (rewriteAll flipAndE)
    `andThen` try (rewriteAll flipEqE)
    `andThen` try (rewriteAll flipJoinE)
  )
  `andThen` (repeat' 5 $
            try (rewriteAll elimJoinE)
            `andThen` (try $ rewriteAll filterToHidxE)
            `andThen` (try $ rewriteAll filterToOidx1E)
            `andThen` (try $ rewriteAll filterToOidx2E)
            )
  `andThen` (try (rewriteAll introListE))
  `andThen`
    (repeat' 10 $
     try (rewriteAll depjoinStageE1)
     `andThen` try (rewriteAll depjoinStageE2)
     `andThen` try (rewriteAll filterStageE1)
     `andThen` try (rewriteAll filterStageE2)
     `andThen` try (rewriteAll eqStageE1)
     `andThen` try (rewriteAll eqStageE2)
     `andThen` try (rewriteAll ltStageE1)
     `andThen` try (rewriteAll ltStageE2)
     `andThen` try (rewriteAll andStageE1)
     `andThen` try (rewriteAll andStageE2)
     `andThen` try (rewriteAll hidxStageE1)
     `andThen` try (rewriteAll hidxStageE2)
     `andThen` try (rewriteAll oidxStageE1)
     `andThen` try (rewriteAll oidxStageE2)
     `andThen` try (rewriteAll listStageE1)
     `andThen` try (rewriteAll listStageE2)
     `andThen` try (rewriteAll dotStageE1)
     `andThen` try (rewriteAll dotStageE2)
     `andThen` try (rewriteAll selectStageE1)
     `andThen` try (rewriteAll selectStageE2)
     `andThen` try (rewriteAll scalarStageE)
    )
