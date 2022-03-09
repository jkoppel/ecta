{-# LANGUAGE OverloadedStrings #-}

module Application.TermSearch.TermSearch where

import           Data.List                      ( (\\)
                                                , permutations
                                                )
import           Data.List.Extra                ( nubOrd )
import qualified Data.Map                      as Map
import           Data.Maybe                     ( fromMaybe )
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Tuple                     ( swap )
import           System.IO                      ( hFlush
                                                , stdout
                                                )

import           Data.ECTA
import           Data.ECTA.Paths
import           Data.ECTA.Term
import           Data.Text.Extended.Pretty
import           Utility.Fixpoint

import           Application.EqualitySaturation ( At(..)
                                                , UseVarAt(..)
                                                , modEcs
                                                , nodeModEcs
                                                , useVar
                                                , varPath
                                                )
import           Application.TermSearch.Dataset
import           Application.TermSearch.Type
import           Application.TermSearch.Utils

------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-------------------------------  Recursive Nodes   -----------------------------
--------------------------------------------------------------------------------

tau :: Node
tau = createMu
  (\n -> union
    (  [arrowType n n, var1, var2, var3, var4]
    ++ map (Node . (: []) . constructorToEdge n) usedConstructors
    )
  )
 where
  constructorToEdge :: Node -> (Text, Int) -> Edge
  constructorToEdge n (nm, arity) = Edge (Symbol nm) (replicate arity n)

  usedConstructors = allConstructors

allConstructors :: [(Text, Int)]
allConstructors =
  nubOrd
      (  concatMap getConstructors (Map.keys hoogleComponents)
      ++ [("Set", 1), ("Map", 2)]
      )
    \\ [("Fun", 2)]
 where
  getConstructors :: TypeSkeleton -> [(Text, Int)]
  getConstructors (TVar _    ) = []
  getConstructors (TFun t1 t2) = getConstructors t1 ++ getConstructors t2
  getConstructors (TCons nm ts) =
    (nm, length ts) : concatMap getConstructors ts

envSize :: Int
envSize = 3

envPath :: Path
envPath = path [1]

generalize :: Node -> Node
generalize n@(Node [_]) = Node
  [mkEdge s ns' (mkEqConstraints $ map pathsForVar vars)]
 where
  vars                = [var1, var2, var3, var4, varAcc]
  nWithVarsRemoved    = mapNodes (\x -> if x `elem` vars then tau else x) n
  (Node [Edge s ns']) = nWithVarsRemoved

  pathsForVar :: Node -> [Path]
  pathsForVar v = pathsMatching (== v) n
generalize n = error $ "cannot generalize: " ++ show n

--------------------------------------------------------------------------------
-------------------------------   Term Encoding    -----------------------------
--------------------------------------------------------------------------------

-- Use of `getPath (path [0, 2]) n1` instead of `tau` effectively pre-computes some reduction.
-- Sometimes this can be desirable, but for enumeration,
app :: Int -> Node -> Node -> Node
app lambdaCnt n1 n2 = Node
  [ mkEdge
      "app"
      [tau, anyEnv lambdaCnt, theArrowNode, n1, n2]
      (mkEqConstraints                            -- constraints for "app e1 e2"
        [ [path [2]   , path [3, 0, 0]]           -- trick: arrow symbol to mark the type of e1 is a function type
        , [path [4, 0], path [3, 0, 1]]           -- argument type of T(e1) equals to T(e2)
        , [path [0]   , path [3, 0, 2]]           -- T(app e1 e2) equals to T(e1)
        , [path [1]   , path [3, 1], path [4, 1]] -- environment remains the same before and after the application
        ]
      )
  ]

lambda :: Int -> Node -> Node
lambda lambdaCnt n = Node
  [ mkEdge
      "lambda"
      [tau, anyEnv lambdaCnt, theArrowNode, n]
      (copyLiftedEnvToChild envPath (lambdaCnt + 1) 2 <> mkEqConstraints  -- constraints for "lambda x e"
        [ [path [0, 0], path [2]]          -- lambda terms returns a function type, so the first part of T(lambda x e) is the arrow symbol
        , [path [0, 1], path [3, 1, 0]]    -- T(x) equals to the argument type of T(lambda x e)
        , [path [0, 2], path [3, 0]]       -- T(e) equals to the return type of T(lambda x e)
        ]
      )
  ]
 where
    -- de Bruijn index operations
  copyLiftedEnvToChild :: Path -> Int -> Int -> EqConstraints
  copyLiftedEnvToChild ep sz childIdx = foldMap doCopyVar [1 .. sz - 1]
   where
    doCopyVar :: Int -> EqConstraints
    doCopyVar targIdx = mkEqConstraints
      [[varPath ep (targIdx - 1), path [childIdx + 1] <> varPath ep targIdx]]

--------------------------------------------------------------------------------
------------------------------- Relevancy Encoding -----------------------------
--------------------------------------------------------------------------------

applyOperator :: Int -> Node
applyOperator lambdaCnt = Node $ map ($ lambdaCnt)
  [ constFunc
    "$"
    (generalize $ arrowType (arrowType var1 var2) (arrowType var1 var2))
  , constFunc "id" (generalize $ arrowType var1 var1)
  ]

hoogleComps :: [Int -> Edge]
hoogleComps =
  filter
      (\e ->
        edgeSymbol (e 0)
          `notElem` map (Symbol . toMappedName) speciallyTreatedFunctions
      )
    $ map (uncurry parseHoogleComponent . swap)
    $ Map.toList hoogleComponents

anyFunc :: Int -> Node
-- anyFunc = Node hoogleComps
anyFunc lambdaCnt = Node
  $ map ($ lambdaCnt) [f31, f10, f32, f33, f34, f35, f36, f37, f38, f39, f16]
-- anyFunc _ = Node []

filterType :: Node -> Node -> Node
filterType n t =
  Node [mkEdge "filter" [t, n] (mkEqConstraints [[path [0], path [1, 0]]])]

constructLambdaK :: (Int -> Node) -> Int -> Int -> Node
constructLambdaK anyArg lambdaCnt k =
  lambda lambdaCnt (union (termsK anyArg True (lambdaCnt + 1) (k - 1)))

anyEnv :: Int -> Node
anyEnv sz = Node [Edge "env" $ replicate sz tau]

type Size = Int

withEnvPropagation :: Path -> Int -> [UseVarAt] -> Node -> Node
withEnvPropagation ep numChildren uvas n =
  nodeModEcs (<> foldMap copyEnvToChild normalChildren)
    $ foldr nodeUseVarFromEnv n uvas
 where
  varChildren    = map childIdx uvas
  normalChildren = [0 .. numChildren - 1] \\ varChildren

  useVarFromEnv :: UseVarAt -> Edge -> Edge
  useVarFromEnv uva e = modEcs
    (<> mkEqConstraints [[varPath ep (varIdx uva), path [childIdx uva]]])
    e

  nodeUseVarFromEnv :: UseVarAt -> Node -> Node
  nodeUseVarFromEnv uva = nodeMapChildren (useVarFromEnv uva)

  copyEnvToChild :: Int -> EqConstraints
  copyEnvToChild childIdx = mkEqConstraints [[ep, path [childIdx] <> ep]]

mkIthArg :: Int -> Int -> Node
mkIthArg lambdaCnt i =
  Node [Edge (Symbol $ Text.pack $ "_x" ++ show i) [tau, anyEnv lambdaCnt]]

useLambdaArgs :: Int -> [Node]
useLambdaArgs lambdaCnt = map
  (\i -> withEnvPropagation envPath 1 [useVar i At 0] (mkIthArg lambdaCnt i))
  [0 .. lambdaCnt - 1]

termsK :: (Int -> Node) -> Bool -> Int -> Size -> [Node]
termsK _ _ _ 0 = []
termsK anyArg False lambdaCnt 1 =
  [anyArg lambdaCnt, anyFunc lambdaCnt] ++ useLambdaArgs lambdaCnt
termsK anyArg True lambdaCnt 1 =
  [anyArg lambdaCnt, anyFunc lambdaCnt, applyOperator lambdaCnt]
    ++ useLambdaArgs lambdaCnt
-- termsK anyArg isArg maxDebruijn 2 =
--   [ app anyListFunc (union [anyNonNilFunc, anyArg, applyOperator])
--   , app fromJustFunc (union [anyNonNothingFunc, anyArg, applyOperator])
--   , app (union [anyNonListFunc, anyArg]) (union (termsK anyArg True 1))
--   ] ++ [constructLambdaK anyArg 1 | isArg]
termsK anyArg isArg lambdaCnt k = if isArg
  then constructLambdaK anyArg lambdaCnt k : map constructApp [1 .. (k - 1)]
  else map constructApp [1 .. (k - 1)]
 where
  constructApp :: Int -> Node
  constructApp i = app lambdaCnt
                       (union (termsK anyArg False lambdaCnt i))
                       (union (termsK anyArg True lambdaCnt (k - i)))

relevantTermK :: (Int -> Node) -> Bool -> Int -> Size -> [Argument] -> [Node]
relevantTermK anyArg includeApplyOp lambdaCnt k [] =
  termsK anyArg includeApplyOp lambdaCnt k
relevantTermK _ _ lambdaCnt 1 [(x, t)] = [Node [constArg x t lambdaCnt]]
relevantTermK anyArg includeApplyOp lambdaCnt k argNames
  | k < length argNames = []
  | otherwise = if includeApplyOp
    then constructLambda k argNames
      : concatMap (\i -> map (constructApp i) allSplits) [1 .. (k - 1)]
    else concatMap (\i -> map (constructApp i) allSplits) [1 .. k - 1]
 where
  allSplits = map (`splitAt` argNames) [0 .. (length argNames)]

  constructApp :: Int -> ([Argument], [Argument]) -> Node
  constructApp i (xs, ys) =
    let f = union (relevantTermK anyArg False lambdaCnt i xs)
        x = union (relevantTermK anyArg True lambdaCnt (k - i) ys)
    in  app lambdaCnt f x

  constructLambda :: Int -> [Argument] -> Node
  constructLambda i args = lambda
    lambdaCnt
    (union $ relevantTermK anyArg True (lambdaCnt + 1) (i - 1) args)

relevantTermsUptoK :: (Int -> Node) -> [Argument] -> Int -> Node
relevantTermsUptoK anyArg args k = union
  (map (union . relevantTermsForArgs) [1 .. k])
 where
  relevantTermsForArgs i =
    concatMap (relevantTermK anyArg False 0 i) (permutations args)

prettyTerm :: Term -> Term
prettyTerm (Term "app" ns) = Term
  "app"
  [prettyTerm (ns !! (length ns - 2)), prettyTerm (ns !! (length ns - 1))]
prettyTerm (Term "filter" ns) = prettyTerm (last ns)
prettyTerm (Term "lambda" ns) = Term "lambda" [prettyTerm (last ns)]
prettyTerm (Term s        _ ) = Term s []

dropTypes :: Node -> Node
dropTypes (Node es) = Node (map dropEdgeTypes es)
 where
  dropEdgeTypes (Edge "app" [_, _, _, a, b]) =
    Edge "app" [dropTypes a, dropTypes b]
  dropEdgeTypes (Edge "lambda" [_, _, _, a]) = Edge "lambda" [dropTypes a]
  dropEdgeTypes (Edge "filter" [_, a]      ) = Edge "filter" [dropTypes a]
  dropEdgeTypes (Edge s        [_]         ) = Edge s []
  dropEdgeTypes e                            = e
dropTypes n = n

getText :: Symbol -> Text
getText (Symbol s) = s

--------------------------
-------- Remove uninteresting terms
--------------------------

fromJustFunc :: Int -> Node
fromJustFunc lambdaCnt =
  Node $ filter (\e -> edgeSymbol e `elem` maybeFunctions) $ map ($ lambdaCnt)
                                                                 hoogleComps

maybeFunctions :: [Symbol]
maybeFunctions =
  [ "Data.Maybe.fromJust"
  , "Data.Maybe.maybeToList"
  , "Data.Maybe.isJust"
  , "Data.Maybe.isNothing"
  ]

listReps :: [Text]
listReps = map
  toMappedName
  [ "Data.Maybe.listToMaybe"
  , "Data.Either.lefts"
  , "Data.Either.rights"
  , "Data.Either.partitionEithers"
  , "Data.Maybe.catMaybes"
  , "GHC.List.head"
  , "GHC.List.last"
  , "GHC.List.tail"
  , "GHC.List.init"
  , "GHC.List.null"
  , "GHC.List.length"
  , "GHC.List.reverse"
  , "GHC.List.concat"
  , "GHC.List.concatMap"
  , "GHC.List.sum"
  , "GHC.List.product"
  , "GHC.List.maximum"
  , "GHC.List.minimum"
  , "(GHC.List.!!)"
  , "(GHC.List.++)"
  ]

isListFunction :: Symbol -> Bool
isListFunction (Symbol sym) = sym `elem` listReps

maybeReps :: [Text]
maybeReps = map
  toMappedName
  [ "Data.Maybe.maybeToList"
  , "Data.Maybe.isJust"
  , "Data.Maybe.isNothing"
  , "Data.Maybe.fromJust"
  ]

isMaybeFunction :: Symbol -> Bool
isMaybeFunction (Symbol sym) = sym `elem` maybeReps

anyListFunc :: Int -> Node
anyListFunc lambdaCnt =
  Node $ filter (isListFunction . edgeSymbol) $ map ($ lambdaCnt) hoogleComps

anyNonListFunc :: Int -> Node
anyNonListFunc lambdaCnt = Node $ filter
  (\e -> not (isListFunction (edgeSymbol e))
    && not (isMaybeFunction (edgeSymbol e))
  )
  (map ($ lambdaCnt) hoogleComps)

anyNonNilFunc :: Int -> Node
anyNonNilFunc lambdaCnt =
  Node $ filter (\e -> edgeSymbol e /= Symbol (toMappedName "Nil")) $ map
    ($ lambdaCnt)
    hoogleComps

anyNonNothingFunc :: Int -> Node
anyNonNothingFunc lambdaCnt = Node $ filter
  (\e -> edgeSymbol e /= Symbol (toMappedName "Data.Maybe.Nothing"))
  (map ($ lambdaCnt) hoogleComps)

--------------------------------------------------------------------------------

reduceFully :: Node -> Node
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)
-- reduceFully = fixUnbounded (reducePartially)

checkSolution :: Term -> [Term] -> IO ()
checkSolution _ [] = return ()
checkSolution target (s : solutions)
  | prettyTerm s == target = print $ pretty (prettyTerm s)
  | otherwise = do
    print $ pretty (prettyTerm s)
    -- print s
    checkSolution target solutions

reduceFullyAndLog :: Node -> IO Node
reduceFullyAndLog = go 0
 where
  go :: Int -> Node -> IO Node
  go i n = do
    putStrLn
      $  "Round "
      ++ show i
      ++ ": "
      ++ show (nodeCount n)
      ++ " nodes, "
      ++ show (edgeCount n)
      ++ " edges"
    hFlush stdout
    -- putStrLn $ renderDot $ toDot n
    -- print n
    let n' = withoutRedundantEdges (reducePartially n)
    if n == n' || i >= 30 then return n else go (i + 1) n'

--------------------------------------------------------------------------------
--------------------------------- Test Functions -------------------------------
--------------------------------------------------------------------------------
--------------------

constFunc :: Symbol -> Node -> Int -> Edge
constFunc s t lambdaCnt = Edge s [t, anyEnv lambdaCnt]

constArg :: Symbol -> Node -> Int -> Edge
constArg = constFunc

f1 :: Int -> Edge
f1 = constFunc "Nothing" (maybeType tau)

f2 :: Int -> Edge
f2 = constFunc "Just" (generalize $ arrowType var1 (maybeType var1))

f3 :: Int -> Edge
f3 = constFunc
  "fromMaybe"
  (generalize $ arrowType var1 (arrowType (maybeType var1) var1))

f4 :: Int -> Edge
f4 = constFunc "listToMaybe"
               (generalize $ arrowType (listType var1) (maybeType var1))

f5 :: Int -> Edge
f5 = constFunc "maybeToList"
               (generalize $ arrowType (maybeType var1) (listType var1))

f6 :: Int -> Edge
f6 = constFunc
  "catMaybes"
  (generalize $ arrowType (listType (maybeType var1)) (listType var1))

f7 :: Int -> Edge
f7 = constFunc
  "mapMaybe"
  (generalize $ arrowType (arrowType var1 (maybeType var2))
                          (arrowType (listType var1) (listType var2))
  )

f8 :: Int -> Edge
f8 = constFunc "id" (generalize $ arrowType var1 var1)

f9 :: Int -> Edge
f9 = constFunc
  "replicate"
  (generalize $ arrowType (constrType0 "Int") (arrowType var1 (listType var1)))

f10 :: Int -> Edge
f10 = constFunc
  "foldr"
  (generalize $ arrowType (arrowType var1 (arrowType var2 var2))
                          (arrowType var2 (arrowType (listType var1) var2))
  )

f11 :: Int -> Edge
f11 = constFunc
  "iterate"
  (generalize $ arrowType (arrowType var1 var1) (arrowType var1 (listType var1))
  )

f12 :: Int -> Edge
f12 = constFunc
  "(!!)"
  (generalize $ arrowType (listType var1) (arrowType (constrType0 "Int") var1))

f13 :: Int -> Edge
f13 = constFunc
  "either"
  (generalize $ arrowType
    (arrowType var1 var3)
    (arrowType (arrowType var2 var3)
               (arrowType (constrType2 "Either" var1 var2) var3)
    )
  )

f14 :: Int -> Edge
f14 = constFunc
  "Left"
  (generalize $ arrowType var1 (constrType2 "Either" var1 var2))

f15 :: Int -> Edge
f15 = constFunc "id" (generalize $ arrowType var1 var1)

f16 :: Int -> Edge
f16 = constFunc
  "(,)"
  (generalize $ arrowType var1 (arrowType var2 (constrType2 "Pair" var1 var2)))

f17 :: Int -> Edge
f17 =
  constFunc "fst" (generalize $ arrowType (constrType2 "Pair" var1 var2) var1)

f18 :: Int -> Edge
f18 =
  constFunc "snd" (generalize $ arrowType (constrType2 "Pair" var1 var2) var2)

f19 :: Int -> Edge
f19 = constFunc
  "foldl"
  (generalize $ arrowType (arrowType var2 (arrowType var1 var2))
                          (arrowType var2 (arrowType (listType var1) var2))
  )

f20 :: Int -> Edge
f20 = constFunc
  "swap"
  ( generalize
  $ arrowType (constrType2 "Pair" var1 var2) (constrType2 "Pair" var2 var1)
  )

f21 :: Int -> Edge
f21 = constFunc
  "curry"
  (generalize $ arrowType (arrowType (constrType2 "Pair" var1 var2) var3)
                          (arrowType var1 (arrowType var2 var3))
  )

f22 :: Int -> Edge
f22 = constFunc
  "uncurry"
  (generalize $ arrowType (arrowType var1 (arrowType var2 var3))
                          (arrowType (constrType2 "Pair" var1 var2) var3)
  )

f23 :: Int -> Edge
f23 = constFunc "head" (generalize $ arrowType (listType var1) var1)

f24 :: Int -> Edge
f24 = constFunc "last" (generalize $ arrowType (listType var1) var1)

f25 :: Int -> Edge
f25 = constFunc
  "Data.ByteString.foldr"
  (generalize $ arrowType
    (arrowType (constrType0 "Word8") (arrowType var2 var2))
    (arrowType var2 (arrowType (constrType0 "ByteString") var2))
  )

f26 :: Int -> Edge
f26 = constFunc
  "unfoldr"
  (generalize $ arrowType
    (arrowType var1 (maybeType (constrType2 "Pair" (constrType0 "Word8") var1)))
    (arrowType var1 (constrType0 "ByteString"))
  )

f27 :: Int -> Edge
f27 = constFunc
  "Data.ByteString.foldrChunks"
  (generalize $ arrowType
    (arrowType (constrType0 "ByteString") (arrowType var2 var2))
    (arrowType var2 (arrowType (constrType0 "ByteString") var2))
  )

f28 :: Int -> Edge
f28 = constFunc
  "bool"
  ( generalize
  $ arrowType var1 (arrowType var1 (arrowType (constrType0 "Bool") var1))
  )

f29 :: Int -> Edge
f29 = constFunc
  "lookup"
  (generalize $ arrowType
    (constrType1 "@@hplusTC@@Eq" var1)
    (arrowType var1 (arrowType (constrType2 "Pair" var1 var2) (maybeType var2)))
  )

f30 :: Int -> Edge
f30 = constFunc "nil" (generalize $ listType var1)

f31 :: Int -> Edge
f31 = constFunc
  "map"
  (generalize $ arrowType (arrowType var1 var2)
                          (arrowType (listType var1) (listType var2))
  )

-- | fromSet :: (k -> a) -> Set k -> Map k a
f32 :: Int -> Edge
f32 = constFunc
  "Map.fromSet"
  (generalize $ arrowType
    (arrowType var1 var2)
    (arrowType (constrType1 "Set" var1) (constrType2 "Map" var1 var2))
  )

-- | paritionWithKey :: (k -> a -> Bool) -> Map k a -> (Map k a, Map k a)
f33 :: Int -> Edge
f33 = constFunc
  "Map.partitionWithKey"
  (generalize $ arrowType
    (arrowType var1 (arrowType var2 (constrType0 "Bool")))
    (arrowType
      (constrType2 "Map" var1 var2)
      (constrType2 "Pair"
                   (constrType2 "Map" var1 var2)
                   (constrType2 "Map" var1 var2)
      )
    )
  )

-- | member :: Ord a => a -> Set a -> Bool
f34 :: Int -> Edge
f34 = constFunc
  "Set.member"
  (generalize $ arrowType
    (constrType1 "@@hplusTC@@Ord" var1)
    (arrowType var1 (arrowType (constrType1 "Set" var1) (constrType0 "Bool")))
  )

-- | map :: (a -> b) -> Map k a -> Map k b
f35 :: Int -> Edge
f35 = constFunc
  "Map.map"
  (generalize $ arrowType
    (arrowType var2 var3)
    (arrowType (constrType2 "Map" var1 var2) (constrType2 "Map" var1 var3))
  )

-- | elems :: Map k a -> [a]
f36 :: Int -> Edge
f36 = constFunc
  "Map.elems"
  (generalize $ arrowType (constrType2 "Map" var1 var2) (listType var2))

-- | filter :: (a -> Bool) -> Map k a -> Map k a
f37 :: Int -> Edge
f37 = constFunc
  "Map.filter"
  (generalize $ arrowType
    (arrowType var2 (constrType0 "Bool"))
    (arrowType (constrType2 "Map" var1 var2) (constrType2 "Map" var1 var2))
  )

-- | null :: Map k a -> Bool
f38 :: Int -> Edge
f38 = constFunc
  "Map.null"
  (generalize $ arrowType (constrType2 "Map" var1 var2) (constrType0 "Bool"))

-- | not :: Bool -> Bool
f39 :: Int -> Edge
f39 = constFunc
  "not"
  (generalize $ arrowType (constrType0 "Bool") (constrType0 "Bool"))

--------------------------
------ Util functions
--------------------------

toMappedName :: Text -> Text
toMappedName x = fromMaybe x (Map.lookup x groupMapping)

prettyPrintAllTerms :: AblationType -> Term -> Node -> IO ()
prettyPrintAllTerms ablation sol n = do
  putStrLn $ "Expected: " ++ show (pretty sol)
  let ts = case ablation of
        NoEnumeration -> naiveDenotationBounded (Just 3) n
        NoOptimize    -> naiveDenotationBounded (Just 3) n
        _             -> getAllTerms n
  checkSolution sol ts

substTerm :: Term -> Term
substTerm (Term (Symbol sym) ts) =
  Term (Symbol $ fromMaybe sym (Map.lookup sym groupMapping)) (map substTerm ts)

parseHoogleComponent :: Text -> TypeSkeleton -> Int -> Edge
parseHoogleComponent name t =
  constFunc (Symbol name) (generalize $ typeToFta t)
