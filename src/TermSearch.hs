{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP               #-}

module TermSearch where

import Data.List ((\\), permutations, isInfixOf, subsequences)
import qualified Data.List as L
import Data.List.Extra (nubOrd)
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set
import Text.RawString.QQ
import qualified Data.Bifunctor as Bi
import Data.Text ( Text )
import qualified Data.Text as Text
import Debug.Trace
import Text.Pretty.Simple (pPrint)
import Data.Text.Extended.Pretty
-- import Language.Dot.Pretty
import Data.Time
import System.Timeout
import Control.Monad (when)
import Language.Dot ( renderDot )
import System.IO (hFlush, stdout)

import Data.ECTA
import Data.ECTA.Paths
import Data.ECTA.Term
import Utility.Fixpoint

import Language.Dot ( renderDot )

------------------------------------------------------------------------------

tau :: Node
tau = createGloballyUniqueMu (\n -> union ([arrowType n n, var1, var2, var3, var4] ++ map (Node . (:[]) . constructorToEdge n) usedConstructors))
  where
    constructorToEdge :: Node -> (Text, Int) -> Edge
    constructorToEdge n (nm, arity) = Edge (Symbol nm) (replicate arity n)

    -- usedConstructors = allConstructors
    usedConstructors = [("List", 1), ("Pair", 2)]

--tau :: Node
--tau = Node [Edge "tau" []]

baseType :: Node
baseType = Node [Edge "baseType" []]

typeConst :: Text -> Node
typeConst s = Node [Edge (Symbol s) []]

constrType0 :: Text -> Node
constrType0 s = Node [Edge (Symbol s) []]

constrType1 :: Text -> Node -> Node
constrType1 s n = Node [Edge (Symbol s) [n]]

constrType2 :: Text -> Node -> Node -> Node
constrType2 s n1 n2 = Node [Edge (Symbol s) [n1, n2]]

maybeType :: Node -> Node
maybeType = constrType1 "Maybe"

listType :: Node -> Node
listType = constrType1 "List"

theArrowNode :: Node
theArrowNode = Node [Edge "(->)" []]

arrowType :: Node -> Node -> Node
arrowType n1 n2 = Node [Edge "->" [theArrowNode, n1, n2]]

constFunc :: Symbol -> Node -> Edge
constFunc s t = Edge s [t]

constArg :: Symbol -> Node -> Edge
constArg = constFunc

-- Use of `getPath (path [0, 2]) n1` instead of `tau` effectively pre-computes some reduction.
-- Sometimes this can be desirable, but for enumeration,
app :: Node -> Node -> Node
app n1 n2 = Node [mkEdge "app" [{- getPath (path [0, 2]) n1 -} tau
                               , theArrowNode, n1, n2
                               ]
                               (mkEqConstraints [ [path [1],      path [2, 0, 0]]
                                                , [path [3, 0],   path [2, 0, 1]]
                                                , [path [0],      path [2, 0, 2]]
                                                ])
                 ]

var1, var2, var3, var4, varAcc :: Node
var1   = Node [Edge "var1" []]
var2   = Node [Edge "var2" []]
var3   = Node [Edge "var3" []]
var4   = Node [Edge "var4" []]
varAcc = Node [Edge "acc" []]

-- | TODO: Also constraint children to be (->) nodes
generalize :: Node -> Node
generalize n@(Node [_]) = Node [mkEdge s ns' (mkEqConstraints $ map pathsForVar vars)]
  where
    vars = [var1, var2, var3, var4, varAcc]
    nWithVarsRemoved = mapNodes (\x -> if x `elem` vars then tau else x) n
    (Node [Edge s ns']) = nWithVarsRemoved

    pathsForVar :: Node -> [Path]
    pathsForVar v = pathsMatching (==v) n

-- f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 :: Edge
-- f1 = constFunc "Nothing" (maybeType tau)
-- f2 = constFunc "Just" (generalize $ arrowType var1 (maybeType var1))
-- f3 = constFunc "fromMaybe" (generalize $ arrowType var1 (arrowType (maybeType var1) var1))
-- f4 = constFunc "listToMaybe" (generalize $ arrowType (listType var1) (maybeType var1))
-- f5 = constFunc "maybeToList" (generalize $ arrowType (maybeType var1) (listType var1))
-- f6 = constFunc "catMaybes" (generalize $ arrowType (listType (maybeType var1)) (listType var1))
-- f7 = constFunc "mapMaybe" (generalize $ arrowType (arrowType var1 (maybeType var2)) (arrowType (listType var1) (listType var2)))
-- f8 = constFunc "id" (generalize $ arrowType var1 var1) -- | TODO: Getting an exceeded maxIters when add this; must investigate
f9 = constFunc "replicate" (generalize $ arrowType (constrType0 "Int") (arrowType var1 (listType var1)))
f10 = constFunc "foldr" (generalize $ arrowType (arrowType var1 (arrowType var2 var2)) (arrowType var2 (arrowType (listType var1) var2)))
f11 = constFunc "iterate" (generalize $ arrowType (arrowType var1 var1) (arrowType var1 (listType var1)))
f12 = constFunc "(!!)" (generalize $ arrowType (listType var1) (arrowType (constrType0 "Int") var1))

-- f13 = constFunc "either" (generalize $ arrowType (arrowType var1 var3) (arrowType (arrowType var2 var3) (arrowType (constrType2 "Either" var1 var2) var3)))
-- f14 = constFunc "Left" (generalize $ arrowType var1 (constrType2 "Either" var1 var2))
-- f15 = constFunc "id" (generalize $ arrowType var1 var1)
f16 = constFunc "(,)" (generalize $ arrowType var1 (arrowType var2 (constrType2 "Pair" var1 var2)))
f17 = constFunc "fst" (generalize $ arrowType (constrType2 "Pair" var1 var2) var1)
f18 = constFunc "snd" (generalize $ arrowType (constrType2 "Pair" var1 var2) var2)
f19 = constFunc "foldl" (generalize $ arrowType (arrowType var2 (arrowType var1 var2)) (arrowType var2 (arrowType (listType var1) var2)))
f20 = constFunc "swap" (generalize $ arrowType (constrType2 "Pair" var1 var2) (constrType2 "Pair" var2 var1))
f21 = constFunc "curry" (generalize $ arrowType (arrowType (constrType2 "Pair" var1 var2) var3) (arrowType var1 (arrowType var2 var3)))
f22 = constFunc "uncurry" (generalize $ arrowType (arrowType var1 (arrowType var2 var3)) (arrowType (constrType2 "Pair" var1 var2) var3))

applyOperator :: Node
applyOperator = Node [ constFunc "$" (generalize $ arrowType (arrowType var1 var2) (arrowType var1 var2))
                    --  , constFunc "Data.Function.id" (generalize $ arrowType var1 var1)
                     ]

-- args :: [(Symbol, Node)]
-- args = [
--     -- type query 1 @ g: (a -> a) -> x: a -> n: Int -> a
--     ("g", arrowType baseType baseType), 
--     ("x", baseType), 
--     ("n", constrType0 "Int")
--     -- type query 2 @ def: a -> mbs: [Maybe a] -> a
--   --   ("def", baseType)
--   -- , ("mbs", listType (maybeType baseType))
--   ]

-- arg1, arg2 :: Edge
-- arg1 = constArg "def" baseType
-- arg2 = constArg "mbs" (listType (maybeType baseType))
-- arg3 = constArg "g" (arrowType baseType baseType)
-- arg4 = constArg "x" baseType
-- arg5 = constArg "n" (constrType0 "Int")

-- anyArg :: Node
-- -- anyArg = Node [arg1, arg2]
-- anyArg = Node [arg3, arg4, arg5]

-- -- | Note: Component #178 is Either.either. Somehow, including this one causes a huge blowup
-- --   in the ECTA.
-- anyFunc = Node [f1, f2, f3, f4, f5, f6, f7, f9, f10, f11, f12]
-- anyFunc = Node [f13, f14, f15]
anyFunc = Node [f10, f16, f17, f18, f19]

-- size1WithoutApplyOperator, size1, size2, size3, size4, size5, size6 :: Node
size1WithoutApplyOperator anyArg = union [anyArg, anyFunc]
size1 anyArg = union [anyArg, anyFunc]
size2 anyArg = app (size1WithoutApplyOperator anyArg) (size1 anyArg)
size3 anyArg = union [app (size2 anyArg) (size1 anyArg), app (size1WithoutApplyOperator anyArg) (size2 anyArg)]
size4 anyArg = union [app (size3 anyArg) (size1 anyArg), app (size2 anyArg) (size2 anyArg), app (size1WithoutApplyOperator anyArg) (size3 anyArg)]
size5 anyArg = union [app (size4 anyArg) (size1 anyArg), app (size3 anyArg) (size2 anyArg), app (size2 anyArg) (size3 anyArg), app (size1WithoutApplyOperator anyArg) (size4 anyArg)]
size6 anyArg = union [app (size5 anyArg) (size1 anyArg), app (size4 anyArg) (size2 anyArg), app (size3 anyArg) (size3 anyArg), app (size2 anyArg) (size4 anyArg), app (size1WithoutApplyOperator anyArg) (size5 anyArg)]
size7 anyArg = union [app (size6 anyArg) (size1 anyArg), app (size5 anyArg) (size2 anyArg), app (size4 anyArg) (size3 anyArg), app (size3 anyArg) (size4 anyArg), app (size2 anyArg) (size5 anyArg), app (size1WithoutApplyOperator anyArg) (size6 anyArg)]

-- uptoSize2, uptoSize3, uptoSize4, uptoSize5, uptoSize6 :: Node
-- uptoSize2 = union [size1, size2]
-- uptoSize3 = union [size1, size2, size3]
uptoSize4 anyArg = union (map ($ anyArg) [size1, size2, size3, size4])
uptoSize5 anyArg = union (map ($ anyArg) [size1, size2, size3, size4, size5])
uptoSize6 anyArg = union (map ($ anyArg) [size1, size2, size3, size4, size5, size6])
uptoSize7 anyArg = union (map ($ anyArg) [size1, size2, size3, size4, size5, size6, size7])

-- uptoDepth2 :: Node
-- uptoDepth2 = union [size1, app size1 size1]

-- uptoDepth3 :: Node
-- uptoDepth3 = union [uptoDepth2, app uptoDepth2 uptoDepth2]

-- uptoDepth4 :: Node
-- uptoDepth4 = union [uptoDepth3, app uptoDepth3 uptoDepth3]

filterType :: Node -> Node -> Node
filterType n t = Node [mkEdge "filter" [t, n] (mkEqConstraints [[path [0], path [1, 0]]])]

termsK :: Node -> Bool -> Int -> [Node]
termsK anyArg _ 0 = []
termsK anyArg False 1 = [anyArg, anyFunc]
termsK anyArg True 1 = [anyArg, anyFunc, applyOperator]
-- termsK anyArg _ 2 = [ app anyListFunc (union [anyNonNilFunc, anyArg, applyOperator])
--                     , app fromJustFunc (union [anyNonNothingFunc, anyArg, applyOperator])
--                     , app (union [anyNonListFunc, anyArg]) (union (termsK anyArg True 1))
--                     ]
termsK anyArg _ k = map constructApp [1..(k-1)]
  where
    constructApp :: Int -> Node
    constructApp i = app (union (termsK anyArg False i)) (union (termsK anyArg True (k-i)))

type ArgType = (Symbol, Node)

relevantTermK :: Node -> Bool -> Int -> [ArgType] -> [Node]
relevantTermK anyArg includeApplyOp k [] = termsK anyArg includeApplyOp k
relevantTermK _ _ 1 [(x, t)] = [Node [constArg x t]]
relevantTermK anyArg _ k argNames
  | k < length argNames = []
  | otherwise = concatMap (\i -> map (constructApp i) allSubsets) [1..(k-1)]
  where
    allSplits = map (`splitAt` argNames) [0..(length argNames)]
    allSubsets = allSplits
    -- allSubsets = nubOrd $ 
    --              concatMap (\(xs, ys) -> map ((, ys) . L.union xs) (subsequences argNames)) allSplits 
    --           ++ concatMap (\(xs, ys) -> map ((xs, ) . L.union ys) (subsequences argNames)) allSplits

    constructApp :: Int -> ([ArgType], [ArgType]) -> Node
    constructApp i (xs, ys) = let f = union (relevantTermK anyArg False i xs)
                                  x = union (relevantTermK anyArg True (k-i) ys)
                               in app f x

relevantTermsUptoK :: Node -> [ArgType] -> Int -> Node
relevantTermsUptoK anyArg args k = union (map (union . relevantTermsForArgs) [1..k])
  where
    relevantTermsForArgs k = concatMap (relevantTermK anyArg True k) (permutations args)

prettyTerm :: Term -> Term
prettyTerm (Term "app" ns) = Term "app" [prettyTerm (ns !! (length ns - 2)), prettyTerm (ns !! (length ns - 1))]
prettyTerm (Term "filter" ns) = prettyTerm (last ns)
prettyTerm (Term s _) = Term s []

dropTypes :: Node -> Node
dropTypes (Node es) = Node (map dropEdgeTypes es)
  where
    dropEdgeTypes (Edge "app"    [_, _, a, b]) = Edge "app" [dropTypes a, dropTypes b]
    dropEdgeTypes (Edge "filter" [_, a]      ) = Edge "filter" [dropTypes a]
    dropEdgeTypes (Edge s        [_]         ) = Edge s []

data ExportType
  = ExportVar Text
  | ExportFun ExportType ExportType
  | ExportCons Text [ExportType]
  | ExportForall Text ExportType
  deriving ( Eq, Ord, Show, Read )

data Benchmark = Benchmark Text Int String ([(Text, ExportType)], ExportType)
  deriving ( Eq, Ord, Show, Read )

speciallyTreatedFunctions :: [Symbol]
speciallyTreatedFunctions = [-- `($)` is hardcoded to only be in argument position
                              "(Data.Function.$)"
                            -- `id` is almost entirely useless, but clogs up the graph. Currently banned
                            , "Data.Function.id"

                            -- Seeing what happens upon banning other too-polymorphic functions
                            -- Data.Either
                            -- , "Data.Either.either" -- Either a b -> (a -> c) -> (b -> c) -> c

                            -- GHC.List
                            , "GHC.List.scanr" -- (a -> b -> b) -> b -> [a] -> [b]
                            , "GHC.List.scanl"
                            , "GHC.List.scanl'"
                            , "GHC.List.scanl1"
                            -- , "GHC.List.foldl"
                            , "GHC.List.foldl'"
                            , "GHC.List.foldl1" -- (a -> a -> a) -> [a] -> a
                            , "GHC.List.foldl1'" -- (a -> a -> a) -> [a] -> a
                            -- , "GHC.List.foldr" -- (a -> b -> b) -> b -> [a] -> b
                            , "GHC.List.foldr1" -- (a -> a -> a) -> [a] -> a
                            , "GHC.List.zipWith3" -- (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
                            , "GHC.List.head"
                            , "GHC.List.last"
                            , "GHC.List.maximum"
                            , "GHC.List.minimum"
                            , "GHC.List.any"
                            , "GHC.List.all"
                            , "GHC.List.and"
                            , "GHC.List.concat"
                            , "GHC.List.cycle"
                            , "GHC.List.drop"
                            , "GHC.List.elem"
                            , "GHC.List.init"
                            , "GHC.List.length"
                            , "GHC.List.notElem"
                            , "GHC.List.null"
                            , "GHC.List.or"
                            , "GHC.List.product"
                            , "GHC.List.replicate"
                            , "GHC.List.repeat"
                            , "GHC.List.reverse"
                            , "GHC.List.sum"
                            , "GHC.List.tail"
                            , "GHC.List.take"
                            , "GHC.List.uncons"
                            , "(GHC.List.!!)"
                            , "(GHC.List.++)"
                            -- higher order functions
                            , "GHC.List.break"
                            , "GHC.List.takeWhile"
                            , "GHC.List.dropWhile"
                            , "GHC.List.map"
                            , "GHC.List.filter"
                            , "GHC.List.concatMap"
                            , "GHC.List.iterate"
                            , "GHC.List.iterate'"
                            , "GHC.List.lookup"
                            , "GHC.List.span"
                            , "GHC.List.splitAt"
                            , "GHC.List.unzip"
                            , "GHC.List.unzip3"
                            , "GHC.List.zip"
                            , "GHC.List.zip3"
                            , "GHC.List.zipWith"
                            -- , "Nil"
                            -- Data.Maybe
                            -- , "Data.Maybe.maybe" -- b -> (a -> b) -> Maybe a -> b
                            -- , "Data.Maybe.Nothing"
                            ]

pickedModules :: [Text]
pickedModules = ["Pair", "Data.Tuple", "GHC.List"]

isElemPickedModules :: Symbol -> Bool
isElemPickedModules (Symbol s) = any (`Text.isInfixOf` s) pickedModules

hoogleComps :: [Edge]
hoogleComps = filter (\e -> edgeSymbol e `notElem` speciallyTreatedFunctions)
            $ filter (isElemPickedModules . edgeSymbol)
            $ map (uncurry parseHoogleComponent)
            $ Map.toList groupedComponents

anyFunc :: Node
-- anyFunc = Node hoogleComps

fromJustFunc :: Node
fromJustFunc = Node [ constFunc "Data.Maybe.fromJust" (generalize $ arrowType (maybeType var1) var1)
                    , constFunc "Data.Maybe.maybeToList" (generalize $ arrowType (maybeType var1) (listType var1))
                    ]

isListFunction :: Symbol -> Bool
isListFunction (Symbol sym) = ("GHC.List." `Text.isInfixOf` sym) || (sym `elem` ["Data.Maybe.listToMaybe", "Data.Either.lefts", "Data.Either.rights", "Data.Maybe.catMaybes"])

anyListFunc :: Node
anyListFunc = Node $ filter (isListFunction . edgeSymbol) hoogleComps

anyNonListFunc :: Node
anyNonListFunc = Node $ filter (\e -> not (isListFunction (edgeSymbol e)) && edgeSymbol e /= "Data.Maybe.fromJust" && edgeSymbol e /= "Data.Maybe.maybeToList") hoogleComps

anyNonNilFunc :: Node
anyNonNilFunc = Node $ filter (\e -> edgeSymbol e /= "Nil") hoogleComps

anyNonNothingFunc :: Node
anyNonNothingFunc = Node $ filter (\e -> edgeSymbol e /= "Data.Maybe.Nothing") hoogleComps

---------------------------------------------------------------------------------------
-------------------------- Importing components from Hoogle+ --------------------------
---------------------------------------------------------------------------------------

exportTypeToFta :: ExportType -> Node
exportTypeToFta (ExportVar "a")   = var1
exportTypeToFta (ExportVar "b")   = var2
exportTypeToFta (ExportVar "c")   = var3
exportTypeToFta (ExportVar "d")   = var4
exportTypeToFta (ExportVar "acc") = varAcc
exportTypeToFta (ExportVar v)     = error $ "Current implementation only supports function signatures with type variables a, b, c, d, and acc, but got " ++ show v
exportTypeToFta (ExportFun t1 t2) = arrowType (exportTypeToFta t1) (exportTypeToFta t2)
exportTypeToFta (ExportCons s [])  = typeConst s
exportTypeToFta (ExportCons "Fun" [t1, t2])  = arrowType (exportTypeToFta t1) (exportTypeToFta t2)
exportTypeToFta (ExportCons s [t]) = constrType1 s (exportTypeToFta t)
exportTypeToFta (ExportCons s [t1, t2]) = constrType2 s (exportTypeToFta t1) (exportTypeToFta t2)
exportTypeToFta (ExportForall _ t) = exportTypeToFta t



allConstructors :: [(Text, Int)]
allConstructors = nubOrd (concatMap getConstructors (Map.elems groupedComponents)) \\ [("Fun", 2)]
  where
    getConstructors :: ExportType -> [(Text, Int)]
    getConstructors (ExportVar _) = []
    getConstructors (ExportFun t1 t2) = getConstructors t1 ++ getConstructors t2
    getConstructors (ExportCons nm ts) = (nm, length ts) : concatMap getConstructors ts
    getConstructors (ExportForall _ t) = getConstructors t

parseHoogleComponent :: Text -> ExportType -> Edge
parseHoogleComponent name t = constFunc (Symbol name) (generalize $ exportTypeToFta t)

hoogleComponents :: Map Text ExportType
hoogleComponents = read rawHooglePlusExport

(hoogleGroups, groupedComponents) = (Map.empty, hoogleComponents) -- groupHoogleComponents hoogleComponents

groupHoogleComponents :: Map Text ExportType -> (Map ExportType (Set Text), Map Text ExportType)
groupHoogleComponents comps = Map.foldlWithKey go (Map.empty, Map.empty) comps
  where
    go (seen, res) name typ
      | typ `Map.member` seen = let seen' = Map.adjust (Set.insert name) typ seen
                                 in (seen', res)
      | otherwise             = let seen' = Map.insert typ (Set.singleton name) seen
                                    res'  = Map.insert name typ res
                                 in (seen', res')

rawHooglePlusExport :: String
rawHooglePlusExport = [r|fromList [("(Data.Bool.&&)",ExportFun (ExportCons "Bool" []) (ExportFun (ExportCons "Bool" []) (ExportCons "Bool" []))),("(Data.Bool.||)",ExportFun (ExportCons "Bool" []) (ExportFun (ExportCons "Bool" []) (ExportCons "Bool" []))),("(Data.Eq./=)",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Bool" []))))),("(Data.Eq.==)",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Bool" []))))),("(GHC.List.!!)",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "Int" []) (ExportVar "a")))),("(GHC.List.++)",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("@@hplusTCInstance@@0EqBool",ExportCons "@@hplusTC@@Eq" [ExportCons "Bool" []]),("@@hplusTCInstance@@0EqChar",ExportCons "@@hplusTC@@Eq" [ExportCons "Char" []]),("@@hplusTCInstance@@0EqDouble",ExportCons "@@hplusTC@@Eq" [ExportCons "Double" []]),("@@hplusTCInstance@@0EqFloat",ExportCons "@@hplusTC@@Eq" [ExportCons "Float" []]),("@@hplusTCInstance@@0EqInt",ExportCons "@@hplusTC@@Eq" [ExportCons "Int" []]),("@@hplusTCInstance@@0EqUnit",ExportCons "@@hplusTC@@Eq" [ExportCons "Unit" []]),("@@hplusTCInstance@@0IsString",ExportCons "@@hplusTC@@IsString" [ExportCons "Builder" []]),("@@hplusTCInstance@@0NumDouble",ExportCons "@@hplusTC@@Num" [ExportCons "Double" []]),("@@hplusTCInstance@@0NumFloat",ExportCons "@@hplusTC@@Num" [ExportCons "Float" []]),("@@hplusTCInstance@@0NumInt",ExportCons "@@hplusTC@@Num" [ExportCons "Int" []]),("@@hplusTCInstance@@0OrdBool",ExportCons "@@hplusTC@@Ord" [ExportCons "Bool" []]),("@@hplusTCInstance@@0OrdChar",ExportCons "@@hplusTC@@Ord" [ExportCons "Char" []]),("@@hplusTCInstance@@0OrdDouble",ExportCons "@@hplusTC@@Ord" [ExportCons "Double" []]),("@@hplusTCInstance@@0OrdFloat",ExportCons "@@hplusTC@@Ord" [ExportCons "Float" []]),("@@hplusTCInstance@@0OrdInt",ExportCons "@@hplusTC@@Ord" [ExportCons "Int" []]),("@@hplusTCInstance@@0ShowBool",ExportCons "@@hplusTC@@Show" [ExportCons "Bool" []]),("@@hplusTCInstance@@0ShowChar",ExportCons "@@hplusTC@@Show" [ExportCons "Char" []]),("@@hplusTCInstance@@0ShowDouble",ExportCons "@@hplusTC@@Show" [ExportCons "Double" []]),("@@hplusTCInstance@@0ShowFloat",ExportCons "@@hplusTC@@Show" [ExportCons "Float" []]),("@@hplusTCInstance@@0ShowInt",ExportCons "@@hplusTC@@Show" [ExportCons "Int" []]),("@@hplusTCInstance@@0ShowUnit",ExportCons "@@hplusTC@@Show" [ExportCons "Unit" []]),("@@hplusTCInstance@@1Show",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "b"]) (ExportCons "@@hplusTC@@Show" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@2Read",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Read" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Read" [ExportVar "b"]) (ExportCons "@@hplusTC@@Read" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@3Ord",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "b"]) (ExportCons "@@hplusTC@@Ord" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@4Eq",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "b"]) (ExportCons "@@hplusTC@@Eq" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@6Semigroup",ExportForall "b" (ExportForall "a" (ExportCons "@@hplusTC@@Semigroup" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))),("@@hplusTCInstance@@9Eq",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportCons "@@hplusTC@@Eq" [ExportCons "List" [ExportVar "a"]]))),("Cons",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("Data.Bool.False",ExportCons "Bool" []),("Data.Bool.True",ExportCons "Bool" []),("Data.Bool.bool",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportFun (ExportCons "Bool" []) (ExportVar "a"))))),("Data.Bool.not",ExportFun (ExportCons "Bool" []) (ExportCons "Bool" [])),("Data.Bool.otherwise",ExportCons "Bool" []),("Data.ByteString.Builder.byteString",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.byteStringHex",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.char7",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.char8",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.charUtf8",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleBE",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleDec",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleHexFixed",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleLE",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatBE",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatDec",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatHexFixed",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatLE",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.hPutBuilder",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Builder" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Builder.int16BE",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16Dec",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16HexFixed",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16LE",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32BE",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32Dec",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32HexFixed",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32LE",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64BE",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64Dec",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64HexFixed",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64LE",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8Dec",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8HexFixed",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.intDec",ExportFun (ExportCons "Int" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.integerDec",ExportFun (ExportCons "Integer" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.lazyByteString",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.lazyByteStringHex",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.shortByteString",ExportFun (ExportCons "ShortByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.string7",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.string8",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.stringUtf8",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.toLazyByteString",ExportFun (ExportCons "Builder" []) (ExportCons "ByteString" [])),("Data.ByteString.Builder.word16BE",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16Dec",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16Hex",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16HexFixed",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16LE",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32BE",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32Dec",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32Hex",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32HexFixed",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32LE",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64BE",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64Dec",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64Hex",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64HexFixed",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64LE",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8Dec",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8Hex",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8HexFixed",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.wordDec",ExportFun (ExportCons "Word" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.wordHex",ExportFun (ExportCons "Word" []) (ExportCons "Builder" [])),("Data.ByteString.Lazy.all",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.any",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.append",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.appendFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.break",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.concat",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.concatMap",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.cons",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.cons'",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.copy",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.count",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Int64" []))),("Data.ByteString.Lazy.cycle",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.drop",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.dropWhile",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.elem",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.elemIndex",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.elemIndexEnd",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.elemIndices",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.empty",ExportCons "ByteString" []),("Data.ByteString.Lazy.filter",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.find",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Word8" []]))),("Data.ByteString.Lazy.findIndex",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.findIndices",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.foldl",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "Word8" []) (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldl'",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "Word8" []) (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldl1",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.foldl1'",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.foldlChunks",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldr",ExportForall "a" (ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldr1",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.foldrChunks",ExportForall "a" (ExportFun (ExportFun (ExportCons "ByteString" []) (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.fromChunks",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.fromStrict",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.getContents",ExportCons "IO" [ExportCons "ByteString" []]),("Data.ByteString.Lazy.group",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.groupBy",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hGet",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Int" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hGetContents",ExportFun (ExportCons "Handle" []) (ExportCons "IO" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.hGetNonBlocking",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Int" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hPut",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.hPutNonBlocking",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hPutStr",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.head",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.index",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "Int64" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.init",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.inits",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.interact",ExportFun (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.intercalate",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.intersperse",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.isPrefixOf",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.isSuffixOf",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.iterate",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" [])) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.last",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.length",ExportFun (ExportCons "ByteString" []) (ExportCons "Int64" [])),("Data.ByteString.Lazy.map",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.mapAccumL",ExportForall "acc" (ExportFun (ExportFun (ExportVar "acc") (ExportFun (ExportCons "Word8" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "Word8" []]))) (ExportFun (ExportVar "acc") (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "ByteString" []]))))),("Data.ByteString.Lazy.mapAccumR",ExportForall "acc" (ExportFun (ExportFun (ExportVar "acc") (ExportFun (ExportCons "Word8" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "Word8" []]))) (ExportFun (ExportVar "acc") (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "ByteString" []]))))),("Data.ByteString.Lazy.maximum",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.minimum",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.notElem",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.null",ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" [])),("Data.ByteString.Lazy.pack",ExportFun (ExportCons "List" [ExportCons "Word8" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.partition",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.putStr",ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.putStrLn",ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.readFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "IO" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.repeat",ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.replicate",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.reverse",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.scanl",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])))),("Data.ByteString.Lazy.singleton",ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.snoc",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.span",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.split",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.splitAt",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.splitWith",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.stripPrefix",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.stripSuffix",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.tail",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.tails",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.take",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.takeWhile",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.toChunks",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.toStrict",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.transpose",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.uncons",ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "ByteString" []]])),("Data.ByteString.Lazy.unfoldr",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "Word8" [],ExportVar "a"]])) (ExportFun (ExportVar "a") (ExportCons "ByteString" [])))),("Data.ByteString.Lazy.unpack",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Word8" []])),("Data.ByteString.Lazy.unsnoc",ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "Word8" []]])),("Data.ByteString.Lazy.unzip",ExportFun (ExportCons "List" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "Word8" []]]) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []])),("Data.ByteString.Lazy.writeFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.zip",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "Word8" []]]))),("Data.ByteString.Lazy.zipWith",ExportForall "a" (ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportVar "a"))) (ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportVar "a"]))))),("Data.Either.Left",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "a") (ExportCons "Either" [ExportVar "a",ExportVar "b"])))),("Data.Either.Right",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "b") (ExportCons "Either" [ExportVar "a",ExportVar "b"])))),("Data.Either.either",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "c")) (ExportFun (ExportFun (ExportVar "b") (ExportVar "c")) (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportVar "c"))))))),("Data.Either.fromLeft",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportVar "a"))))),("Data.Either.fromRight",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "b") (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportVar "b"))))),("Data.Either.isLeft",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportCons "Bool" [])))),("Data.Either.isRight",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportCons "Bool" [])))),("Data.Either.lefts",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "List" [ExportVar "a"])))),("Data.Either.partitionEithers",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]])))),("Data.Either.rights",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "List" [ExportVar "b"])))),("Data.List.group",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportCons "List" [ExportVar "a"]])))),("Data.Maybe.Just",ExportForall "a" (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "a"]))),("Data.Maybe.Nothing",ExportForall "a" (ExportCons "Maybe" [ExportVar "a"])),("Data.Maybe.catMaybes",ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]]) (ExportCons "List" [ExportVar "a"]))),("Data.Maybe.fromJust",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportVar "a"))),("Data.Maybe.fromMaybe",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportVar "a")))),("Data.Maybe.isJust",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "Bool" []))),("Data.Maybe.isNothing",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "Bool" []))),("Data.Maybe.listToMaybe",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Maybe" [ExportVar "a"]))),("Data.Maybe.mapMaybe",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "b"])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("Data.Maybe.maybe",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "b") (ExportFun (ExportFun (ExportVar "a") (ExportVar "b")) (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportVar "b")))))),("Data.Maybe.maybeToList",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("Data.Tuple.curry",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "c")) (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))))))),("Data.Tuple.fst",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "a")))),("Data.Tuple.snd",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "b")))),("Data.Tuple.swap",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportCons "Pair" [ExportVar "b",ExportVar "a"])))),("Data.Tuple.uncurry",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))) (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "c")))))),("GHC.Char.chr",ExportFun (ExportCons "Int" []) (ExportCons "Char" [])),("GHC.Char.eqChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "Char" []) (ExportCons "Bool" []))),("GHC.Char.neChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "Char" []) (ExportCons "Bool" []))),("GHC.List.all",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" [])))),("GHC.List.and",ExportFun (ExportCons "List" [ExportCons "Bool" []]) (ExportCons "Bool" [])),("GHC.List.any",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" [])))),("GHC.List.break",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])))),("GHC.List.concat",ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "List" [ExportVar "a"]]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.concatMap",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "b"])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("GHC.List.cycle",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.drop",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.dropWhile",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.elem",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" []))))),("GHC.List.filter",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.foldl",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "b")))))),("GHC.List.foldl'",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "b")))))),("GHC.List.foldl1",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.foldl1'",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.foldr",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "b")))))),("GHC.List.foldr1",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.head",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a"))),("GHC.List.init",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.iterate",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "a")) (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"])))),("GHC.List.iterate'",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "a")) (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"])))),("GHC.List.last",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a"))),("GHC.List.length",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Int" []))),("GHC.List.lookup",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]) (ExportCons "Maybe" [ExportVar "b"])))))),("GHC.List.map",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "b")) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("GHC.List.maximum",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.minimum",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.notElem",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" []))))),("GHC.List.null",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" []))),("GHC.List.or",ExportFun (ExportCons "List" [ExportCons "Bool" []]) (ExportCons "Bool" [])),("GHC.List.product",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Num" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.repeat",ExportForall "a" (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"]))),("GHC.List.replicate",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"])))),("GHC.List.reverse",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.scanl",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"])))))),("GHC.List.scanl'",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"])))))),("GHC.List.scanl1",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.scanr",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"])))))),("GHC.List.scanr1",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.span",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])))),("GHC.List.splitAt",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])))),("GHC.List.sum",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Num" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.tail",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.take",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.takeWhile",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.uncons",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Maybe" [ExportCons "Pair" [ExportVar "a",ExportCons "List" [ExportVar "a"]]]))),("GHC.List.unzip",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]])))),("GHC.List.unzip3",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportCons "Pair" [ExportVar "a",ExportVar "b"],ExportVar "c"]]) (ExportCons "Pair" [ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]],ExportCons "List" [ExportVar "c"]]))))),("GHC.List.zip",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]))))),("GHC.List.zip3",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportFun (ExportCons "List" [ExportVar "c"]) (ExportCons "List" [ExportCons "Pair" [ExportCons "Pair" [ExportVar "a",ExportVar "b"],ExportVar "c"]]))))))),("GHC.List.zipWith",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportCons "List" [ExportVar "c"]))))))),("GHC.List.zipWith3",ExportForall "d" (ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportFun (ExportVar "c") (ExportVar "d")))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportFun (ExportCons "List" [ExportVar "c"]) (ExportCons "List" [ExportVar "d"]))))))))),("Nil",ExportForall "a" (ExportCons "List" [ExportVar "a"])),("Pair",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportCons "Pair" [ExportVar "a",ExportVar "b"]))))),("Text.Show.show",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportCons "List" [ExportCons "Char" []])))),("Text.Show.showChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))),("Text.Show.showList",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showListWith",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showParen",ExportFun (ExportCons "Bool" []) (ExportFun (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []])) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []])))),("Text.Show.showString",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))),("Text.Show.shows",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showsPrec",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "Int" []) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))))]|]

benchmarks :: [Benchmark]
benchmarks = read rawBenchmarks

rawBenchmarks :: String
rawBenchmarks = [r|[Benchmark "appBoth" 5 "app(app(Pair, app(f, x)), app(g, x))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("g",ExportFun (ExportVar "a") (ExportVar "c")),("x",ExportVar "a")],ExportCons "Pair" [ExportVar "b",ExportVar "c"]),Benchmark "test" 5 "app(app(app(Data.Bool.bool, Data.Maybe.Nothing), app(Data.Maybe.Just, x)), b)" ([("b",ExportCons "Bool" []),("x",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"]),Benchmark "both" 7 "app(Pair, app(f, app(Data.Tuple.fst, p)), app(f, app(Data.Tuple.snd, p)))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("p",ExportCons "Pair" [ExportVar "a",ExportVar "a"])],ExportCons "Pair" [ExportVar "b",ExportVar "b"]),Benchmark "mapEither" 4 "app(Data.Either.partitionEithers, app(app(GHC.List.map, f), xs))" ([("f",ExportFun (ExportVar "a") (ExportCons "Either" [ExportVar "b",ExportVar "c"])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "b"],ExportCons "List" [ExportVar "c"]]),Benchmark "mapMaybes" 4 "app(Data.Maybe.listToMaybe, app(app(Data.Maybe.mapMaybe, f), xs))" ([("f",ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "b"])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Maybe" [ExportVar "b"]),Benchmark "mergeEither" 4 "app(app(app(Data.Either.either, Data.Either.Left), Data.Function.id), e)" ([("e",ExportCons "Either" [ExportVar "a",ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportVar "b"]),Benchmark "mbToEither" 5 "app(app(app(Data.Maybe.maybe, app(Data.Either.Left, x)), Data.Either.Right), mb)" ([("x",ExportVar "a"),("mb",ExportCons "Maybe" [ExportVar "b"])],ExportCons "Either" [ExportVar "a",ExportVar "b"]),Benchmark "cartProduct" 6 "app(app(GHC.List.map, app(GHC.List.zip, xs)), app(app(GHC.List.map, GHC.List.repeat), ys))" ([("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportVar "b"])],ExportCons "List" [ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]]),Benchmark "multiAppPair" 7 "app(app(Pair, app(app(Data.Tuple.fst, tp), x)), app(app(Data.Tuple.snd, tp), x))" ([("tp",ExportCons "Pair" [ExportFun (ExportVar "a") (ExportVar "b"),ExportFun (ExportVar "a") (ExportVar "c")]),("x",ExportVar "a")],ExportCons "Pair" [ExportVar "b",ExportVar "c"]),Benchmark "map" 3 "app(app(GHC.List.map, f), xs)" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "b"]),Benchmark "replFuncs" 3 "app(app(GHC.List.replicate, n), f)" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("n",ExportCons "Int" [])],ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "b")]),Benchmark "mbAppFirst" 5 "app(app(app(Data.Maybe.maybe, x), f), app(Data.Maybe.listToMaybe, xs))" ([("x",ExportVar "b"),("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportVar "b"),Benchmark "mapTwice" 5 "app(app(GHC.List.map, g), app(app(GHC.List.map, f), xs))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("g",ExportFun (ExportVar "b") (ExportVar "c")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "c"]),Benchmark "resolveEither" 4 "app(app(app(Data.Either.either, f), Data.Function.id), e)" ([("e",ExportCons "Either" [ExportVar "a",ExportVar "b"]),("f",ExportFun (ExportVar "a") (ExportVar "b"))],ExportVar "b"),Benchmark "firstJust" 5 "app(app(Data.Maybe.fromMaybe, x), app(Data.Maybe.listToMaybe, app(Data.Maybe.catMaybes, xs)))" ([("x",ExportVar "a"),("xs",ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]])],ExportVar "a"),Benchmark "appendN" 4 "app(GHC.List.concat, app(app(GHC.List.replicate, n), xs))" ([("n",ExportCons "Int" []),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"]),Benchmark "applyNtimes" 6 "app(app(app(GHC.List.foldr, $), x), app(app(GHC.List.replicate, n), f))" ([("f",ExportFun (ExportVar "a") (ExportVar "a")),("x",ExportVar "a"),("n",ExportCons "Int" [])],ExportVar "a"),Benchmark "dedupe" 5 "app(app(GHC.List.map, GHC.List.head), app(app(Data.List.group, tcarg0), xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"]),Benchmark "inverseMap" 5 "app(app(app(GHC.List.zipWith, $), fs), app(GHC.List.repeat, x))" ([("fs",ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "b")]),("x",ExportVar "a")],ExportCons "List" [ExportVar "b"]),Benchmark "app2" 4 "app(app(f, x), app(g, x))" ([("f",ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))),("g",ExportFun (ExportVar "a") (ExportVar "b")),("x",ExportVar "a")],ExportVar "c"),Benchmark "singletonList" 3 "app(app(Cons, x), Nil)" ([("x",ExportVar "a")],ExportCons "List" [ExportVar "a"]),Benchmark "headLast" 5 "app(app(Pair, app(GHC.List.head, xs)), app(GHC.List.last, xs))" ([("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportVar "a",ExportVar "a"]),Benchmark "headRest" 3 "app(Data.Maybe.fromJust, app(GHC.List.uncons, xs))" ([("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportVar "a",ExportCons "List" [ExportVar "a"]]),Benchmark "coundPredMatch" 4 "app(GHC.List.length, app(app(GHC.List.filter, p), xs))" ([("xs",ExportCons "List" [ExportVar "a"]),("p",ExportFun (ExportVar "a") (ExportCons "Bool" []))],ExportCons "Int" []),Benchmark "splitStr" 7 "impossible" ([("str",ExportCons "List" [ExportCons "Char" []]),("c",ExportCons "Char" [])],ExportCons "List" [ExportCons "List" [ExportCons "Char" []]]),Benchmark "splitAtFirst" 5 "app(app(GHC.List.break, app(app((Data.Eq.==), tcarg0), x)), xs)" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]]),Benchmark "hoogle01" 3 "app(f, app(GHC.List.head, xs))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportVar "b"),Benchmark "firstMatch" 4 "app(GHC.List.head, app(app(GHC.List.filter, p), xs))" ([("xs",ExportCons "List" [ExportVar "a"]),("p",ExportFun (ExportVar "a") (ExportCons "Bool" []))],ExportVar "a"),Benchmark "firstMaybe" 3 "app(GHC.List.head, app(Data.Maybe.catMaybes, mbs))" ([("mbs",ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]])],ExportVar "a"),Benchmark "rights" 3 "app(Data.Either.Right, app(Data.Either.rights, es))" ([("es",ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportCons "List" [ExportVar "b"]]),Benchmark "firstKey" 3 "app(Data.Tuple.fst, app(GHC.List.head, xs))" ([("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportVar "a"),Benchmark "firstRight" 4 "app(Data.Either.Right, app(GHC.List.head, app(Data.Either.rights, es)))" ([("es",ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportVar "b"]),Benchmark "maybe" 4 "app(Data.Maybe.Just, app(app(Data.Maybe.fromMaybe, x), mb))" ([("mb",ExportCons "Maybe" [ExportVar "a"]),("x",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"]),Benchmark "app3" 4 "app(app(app(f, x), z), y)" ([("f",ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportFun (ExportVar "c") (ExportVar "d")))),("x",ExportVar "a"),("y",ExportVar "c"),("z",ExportVar "b")],ExportVar "d"),Benchmark "zipWithResult" 5 "app(app(GHC.List.zip, xs), app(app(GHC.List.map, f), xs))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]),Benchmark "eitherTriple" 5 "app(app(app(Data.Bool.bool, e2), e1), app(Data.Either.isLeft, e1))" ([("e1",ExportCons "Either" [ExportVar "a",ExportVar "b"]),("e2",ExportCons "Either" [ExportVar "a",ExportVar "b"])],ExportCons "Either" [ExportVar "a",ExportVar "b"]),Benchmark "pipe" 4 "app(app(app(GHC.List.foldr, $), x), fs)" ([("fs",ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "a")]),("x",ExportVar "a")],ExportVar "a"),Benchmark "lookup" 5 "app(Data.Maybe.fromJust, app(app(app(GHC.List.lookup, tcarg0), k), xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]),("k",ExportVar "a")],ExportVar "b"),Benchmark "mbElem" 6 "app(Data.Maybe.listToMaybe, app(app(GHC.List.filter, app(app((Data.Eq.==), tcarg0), x)), xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Maybe" [ExportVar "a"]),Benchmark "areEq" 7 "app(Data.Maybe.listToMaybe, app(app(GHC.List.filter, app(app((Data.Eq.==), tcarg0), x)), app(GHC.List.repeat, y)))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("y",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"]),Benchmark "applyPair" 4 "app(app(Data.Tuple.fst, p), app(Data.Tuple.snd, p))" ([("p",ExportCons "Pair" [ExportFun (ExportVar "a") (ExportVar "b"),ExportVar "a"])],ExportVar "b"),Benchmark "flatten" 3 "app(GHC.List.concat, app(GHC.List.concat, xss))" ([("xss",ExportCons "List" [ExportCons "List" [ExportCons "List" [ExportVar "a"]]])],ExportCons "List" [ExportVar "a"]),Benchmark "takeNdropM" 7 "app(app(Pair, app(app(GHC.List.take, n), xs)), app(app(GHC.List.drop, m), xs))" ([("n",ExportCons "Int" []),("m",ExportCons "Int" []),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]]),Benchmark "indexesOf" 6 "app(app(GHC.List.map, Data.Tuple.snd), app(f, app(app(GHC.List.zip, xs), ys)))" ([("f",ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportCons "Int" []]]) (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportCons "Int" []]])),("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportCons "Int" []])],ExportCons "List" [ExportCons "Int" []]),Benchmark "containsEdge" 9 "app(app((Data.Bool.&&), app(app(GHC.List.elem, app(Data.Tuple.fst, edge)), vs)), app(app(GHC.List.elem, app(Data.Tuple.snd, edge)), vs))" ([("vs",ExportCons "List" [ExportCons "Int" []]),("edge",ExportCons "Pair" [ExportCons "Int" [],ExportCons "Int" []])],ExportCons "Bool" [])]|]

reduceFully :: Node -> Node
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)
-- reduceFully = fix 5 (withoutRedundantEdges . reducePartially)

checkSolution :: String -> [Term] -> IO ()
checkSolution target [] = return ()
checkSolution target (s:solutions)
  | show (prettyTerm s) == target = print (prettyTerm s)
  | otherwise = do
    print (prettyTerm s)
    -- error "stop"
    checkSolution target solutions

prettyPrintAllTerms :: String -> Node -> IO ()
prettyPrintAllTerms solStr n = do let ts = getAllTerms n
                                  checkSolution ("\"" ++ solStr ++"\"") ts
                          --  print (length ts)
#ifdef PROFILE_CACHES
                              Memoization.printAllCacheMetrics
                              Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Node))
                              Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Edge))
                              Text.putStrLn ""
#endif

runBenchmark :: Benchmark -> IO ()
runBenchmark (Benchmark name depth solStr (args, res)) = do
    let names = []
    let hardBenchmarks = []
    let filteredComponents = Map.filterWithKey (\k _ -> any (`Text.isInfixOf` k) pickedModules) groupedComponents
    -- print $ filteredComponents
    -- print $ length filteredComponents
    -- let hardBenchmarks = ["both", "multiAppPair", "cartProduct", "headLast", "takeNdropM", "areEq"]
    when (name `elem` names || null names)
      (do
        start <- getCurrentTime
        putStrLn $ "Running benchmark " ++ Text.unpack name
        let argNodes = map (Bi.bimap Symbol exportTypeToFta) args
        let resNode = exportTypeToFta res
        let anyArg = Node (map (uncurry constArg) argNodes)
        -- let filterNode = filterType (relevantTermsUptoK anyArg argNodes depth) resNode
        let filterNode = filterType (uptoSize7 anyArg) resNode
        -- putStrLn $ renderDot . toDot $ filterNode
        
        timeout (1800 * 10^6) $ do
            reducedNode <- if name `elem` hardBenchmarks
                           then return $ (withoutRedundantEdges . reducePartially) filterNode
                           else reduceFullyAndLog filterNode
            putStrLn $ renderDot . toDot $ reducedNode
            let !foldedNode = refold reducedNode
            reduceTime <- getCurrentTime
            putStrLn $ "Reduction time: " ++ show (diffUTCTime reduceTime start)
            hFlush stdout
            -- putStrLn $ renderDot . toDot $ reducedNode
            prettyPrintAllTerms solStr foldedNode
        
        end <- getCurrentTime
        print $ "Time: " ++ show (diffUTCTime end start)
        hFlush stdout)
  where
    reduceFullyAndLog :: Node -> IO Node
    reduceFullyAndLog = go 0
      where
        go i n = do putStrLn $ "Round " ++ show i ++ ": " ++ show (nodeCount n) ++ " nodes, " ++ show (edgeCount n) ++ " edges"
                    if i == 0 then putStrLn (renderDot $ toDot n) else return ()
                    let d = constraintAdjustedDepth n
                    putStrLn $ "Depth: " ++ show d
                    let n' = {- withoutRedundantEdges $ -} reducePartially n
                    if n == n' then
                      return n
                    else
                      go (i + 1) n'