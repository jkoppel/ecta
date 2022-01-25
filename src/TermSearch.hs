{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP               #-}

module TermSearch where

import Data.List ((\\), permutations, isInfixOf, isPrefixOf)
import Data.List.Extra (nubOrd)
import           Data.Map ( Map )
import qualified Data.Map as Map
import Text.RawString.QQ
import qualified Data.Bifunctor as Bi
import Data.Text ( Text )
import qualified Data.Text as Text
import Debug.Trace
import Text.Pretty.Simple (pPrint)
import Data.Text.Extended.Pretty
import qualified Data.Text.IO as Text
import Data.Interned.Extended.HashTableBased as Interned
import Data.Memoization as Memoization
import Data.Memoization.Metrics
import Data.Time
import System.Timeout
import Control.Monad (when)
import Language.Dot ( renderDot )
import System.IO (hFlush, stdout, withFile, IOMode(..), hPutStr)
import Data.Char (isUpper)

import Data.ECTA
import Data.ECTA.Paths
import Data.ECTA.Term
import Data.ECTA.Internal.ECTA.Enumeration
import Minimization
import Utility.Fixpoint

------------------------------------------------------------------------------

tau :: Node
tau = createGloballyUniqueMu (\n -> union ([appType n n, arrowType n n, var1, var2, var3, var4] ++ constructors ++ map (constructorToEdge n) usedConstructors))
  where
    constructorToEdge :: Node -> (Text, Int) -> Node
    constructorToEdge n (nm, arity) = foldl appType (typeConst nm) (replicate arity n)

    constructors = map (typeConst . fst) usedConstructors

    -- usedConstructors = allConstructors
    usedConstructors = [ ("Pair", 2)
                       , ("List", 1)
                       , ("Monad", 1)
                       , ("StateT", 3)
                       , ("Foldable", 1)
                       , ("Traversable", 1)
                       , ("Either", 2)
                       , ("String", 0)
                       , ("Maybe", 1)
                       , ("MaybeT", 2)
                       , ("MonadPlus", 1)
                       ]

replicatorTau :: Node
replicatorTau = createGloballyUniqueMu (\n -> union (map (Node . (:[]) . constructorToEdge n) usedConstructors))
  where
    constructorToEdge :: Node -> (Text, Int) -> Edge
    constructorToEdge n (nm, arity) = Edge (Symbol nm) (replicate arity n)

    usedConstructors = [("List", 1)]

--tau :: Node
--tau = Node [Edge "tau" []]

baseType :: Node
baseType = Node [Edge "baseType" []]

typeConst :: Text -> Node
typeConst s = Node [Edge (Symbol s) []]

constrType0 :: Text -> Node
constrType0 s = Node [Edge (Symbol s) []]

constrType1 :: Text -> Node -> Node
constrType1 s n = appType (typeConst s) n -- Node [Edge (Symbol s) [n]]

constrType2 :: Text -> Node -> Node -> Node
constrType2 s n1 n2 = appType (appType (typeConst s) n1) n2 -- Node [Edge (Symbol s) [n1, n2]]

maybeType :: Node -> Node
maybeType = appType (typeConst "Maybe")

listType :: Node -> Node
listType = appType (typeConst "List")

theArrowNode :: Node
theArrowNode = Node [Edge "(->)" []]

arrowType :: Node -> Node -> Node
arrowType n1 n2 = Node [Edge "->" [theArrowNode, n1, n2]]

appType :: Node -> Node -> Node
appType n1 n2 = Node [Edge "TyApp" [n1, n2]]

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

-- app :: Bool -> Node -> Node -> Node
-- app appliedMatch n1 n2 = Node [mkEdge "app" [ tau
--                                             , tau
--                                             , theArrowNode, n1, n2
--                                             ]
--                                             (mkEqConstraints [ [path [1],      path [2, 0, 0]]
--                                                              , [path [3, 0],   path [2, 0, 1]]
--                                                              , [path [0],      path [2, 0, 2]]
--                                                              ])
--                  ]

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
f1 = constFunc "Nothing" (maybeType tau)
f2 = constFunc "Just" (generalize $ arrowType var1 (maybeType var1))
f3 = constFunc "fromMaybe" (generalize $ arrowType var1 (arrowType (maybeType var1) var1))
f4 = constFunc "listToMaybe" (generalize $ arrowType (listType var1) (maybeType var1))
f5 = constFunc "maybeToList" (generalize $ arrowType (maybeType var1) (listType var1))
f6 = constFunc "catMaybes" (generalize $ arrowType (listType (maybeType var1)) (listType var1))
f7 = constFunc "mapMaybe" (generalize $ arrowType (arrowType var1 (maybeType var2)) (arrowType (listType var1) (listType var2)))
f8 = constFunc "id" (generalize $ arrowType var1 var1) -- | TODO: Getting an exceeded maxIters when add this; must investigate
f9 = constFunc "replicate" (generalize $ arrowType (constrType0 "Int") (arrowType var1 (listType var1)))
f10 = constFunc "foldr" (generalize $ arrowType (arrowType var1 (arrowType var2 var2)) (arrowType var2 (arrowType (listType var1) var2)))
f11 = constFunc "iterate" (generalize $ arrowType (arrowType var1 var1) (arrowType var1 (listType var1)))
f12 = constFunc "(!!)" (generalize $ arrowType (listType var1) (arrowType (constrType0 "Int") var1))
f13 = constFunc "either" (generalize $ arrowType (arrowType var1 var3) (arrowType (arrowType var2 var3) (arrowType (constrType2 "Either" var1 var2) var3)))
f14 = constFunc "Left" (generalize $ arrowType var1 (constrType2 "Either" var1 var2))
f15 = constFunc "id" (generalize $ arrowType var1 var1)
f16 = constFunc "(,)" (generalize $ arrowType var1 (arrowType var2 (constrType2 "Pair" var1 var2)))
f17 = constFunc "fst" (generalize $ arrowType (appType (appType (constrType0 "Pair") var1) var2) var1)
f18 = constFunc "snd" (generalize $ arrowType (constrType2 "Pair" var1 var2) var2)
f19 = constFunc "foldl" (generalize $ arrowType (arrowType var2 (arrowType var1 var2)) (arrowType var2 (arrowType (listType var1) var2)))
f20 = constFunc "swap" (generalize $ arrowType (constrType2 "Pair" var1 var2) (constrType2 "Pair" var2 var1))
f21 = constFunc "curry" (generalize $ arrowType (arrowType (constrType2 "Pair" var1 var2) var3) (arrowType var1 (arrowType var2 var3)))
f22 = constFunc "uncurry" (generalize $ arrowType (arrowType var1 (arrowType var2 var3)) (arrowType (constrType2 "Pair" var1 var2) var3))
f23 = constFunc "head" (generalize $ arrowType (listType var1) var1)
f24 = constFunc "last" (generalize $ arrowType (listType var1) var1) 
f25 = constFunc "Data.ByteString.foldr" (generalize $ arrowType (arrowType (constrType0 "Word8") (arrowType var2 var2)) (arrowType var2 (arrowType (constrType0 "ByteString") var2)))
f26 = constFunc "unfoldr" (generalize $ arrowType (arrowType var1 (maybeType (constrType2 "Pair" (constrType0 "Word8") var1))) (arrowType var1 (constrType0 "ByteString")))
f27 = constFunc "Data.ByteString.foldrChunks" (generalize $ arrowType (arrowType (constrType0 "ByteString") (arrowType var2 var2)) (arrowType var2 (arrowType (constrType0 "ByteString") var2)))
f28 = constFunc "fromJust" (generalize $ arrowType (maybeType var1) var1)
f29 = constFunc "splitAt" (generalize $ arrowType (constrType0 "Int") (arrowType (listType var1) (constrType2 "Pair" (listType var1) (listType var1))))
f30 = constFunc "take" (generalize $ arrowType (constrType0 "Int") (arrowType (listType var1) (listType var1)))
f31 = constFunc "drop" (generalize $ arrowType (constrType0 "Int") (arrowType (listType var1) (listType var1)))
f32 = constFunc "Nil" (generalize $ listType var1)
f33 = constFunc "runStateT" (generalize $ arrowType (appType (constrType0 "Monad") var2) (arrowType (appType (appType (appType (constrType0 "StateT") var1) var2) var3) (arrowType var1 (appType var2 (appType (appType (constrType0 "Pair") var3) var1)))))
f34 = constFunc "return" (generalize $ arrowType (appType (constrType0 "Monad") var2) (arrowType var1 (appType var2 var1)))
f35 = constFunc "liftM" (generalize $ arrowType (appType (constrType0 "Monad") var3) (arrowType (arrowType var1 var2) (arrowType (appType var3 var1) (appType var3 var2))))
f36 = constFunc "List@Monad" (appType (constrType0 "Monad") (constrType0 "List"))
f37 = constFunc "(.)" (generalize $ arrowType (arrowType var2 var3) (arrowType (arrowType var1 var2) (arrowType var1 var3)))
f38 = constFunc "(>>=)" (generalize $ arrowType (appType (constrType0 "Monad") var3) (arrowType (appType var3 var1) (arrowType (arrowType var1 (appType var3 var2)) (appType var3 var2))))
f39 = constFunc "(=<<)" (generalize $ arrowType (appType (constrType0 "Monad") var3) (arrowType (arrowType var1 (appType var3 var2)) (arrowType (appType var3 var1) (appType var3 var2))))
f40 = constFunc "foldM" (generalize $ arrowType (appType (constrType0 "Monad") var3) (arrowType (appType (constrType0 "Foldable") var4) (arrowType (arrowType var2 (arrowType var1 (appType var3 var2))) (arrowType var2 (arrowType (appType var4 var1) (appType var3 var2))))))
f41 = constFunc "mapM" (generalize $ arrowType (appType (constrType0 "Monad") var3) (arrowType (appType (constrType0 "Traversable") var4) (arrowType (arrowType var1 (appType var3 var2)) (arrowType (appType var4 var1) (appType var3 (appType var4 var2))))))
f42 = constFunc "map" (generalize $ arrowType (arrowType var1 var2) (arrowType (listType var1) (listType var2)))
f43 = constFunc "List@Foldable" (appType (constrType0 "Foldable") (constrType0 "List"))
f44 = constFunc "zip" (generalize $ arrowType (listType var1) (arrowType (listType var2) (listType (constrType2 "Pair" var1 var2))))
f45 = constFunc "lines" (generalize $ arrowType (constrType0 "String") (listType (constrType0 "String")))
f46 = constFunc "evalStateT" (generalize $ arrowType (appType (constrType0 "Monad") var2) (arrowType (appType (appType (appType (constrType0 "StateT") var1) var2) var3) (arrowType var1 (appType var2 var3))))
f47 = constFunc "MaybeT" (generalize $ arrowType (appType (constrType0 "Monad") var2) (arrowType (appType var2 (maybeType var1)) (appType (appType (constrType0 "MaybeT") var2) var1)))
f48 = constFunc "msum" (generalize $ arrowType (appType (constrType0 "MonadPlus") var2) (arrowType (appType (typeConst "Foldable") var3) (arrowType (appType var3 (appType var2 var1)) (appType var2 var1))))
f49 = constFunc "Maybe@MonadPlus" (appType (constrType0 "MonadPlus") (constrType0 "Maybe"))


applyOperator :: Node
applyOperator = Node [ constFunc "$" (generalize $ arrowType (arrowType var1 var2) (arrowType var1 var2))
                     , constFunc "Data.Function.id" (generalize $ arrowType var1 var1)
                     ]

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
  | otherwise = concatMap (\i -> map (constructApp i) allSplits) [1..(k-1)]
  where
    allSplits = map (`splitAt` argNames) [0..(length argNames)]

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
                            , "GHC.List.foldl1" -- (a -> a -> a) -> [a] -> a
                            , "GHC.List.foldl1'" -- (a -> a -> a) -> [a] -> a
                            -- , "GHC.List.foldr" -- (a -> b -> b) -> b -> [a] -> b
                            , "GHC.List.foldr1" -- (a -> a -> a) -> [a] -> a
                            , "GHC.List.zipWith3" -- (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
                            -- , "Nil"
                            -- Data.Maybe
                            -- , "Data.Maybe.maybe" -- b -> (a -> b) -> Maybe a -> b
                            -- , "Data.Maybe.Nothing"
                            -- Data.ByteString
                            -- , "Data.ByteString.Lazy.foldr"
                            -- , "Data.ByteString.Lazy.foldrChunks"
                            -- , "Data.ByteString.Lazy.unfoldr"
                            -- , "Text.Show.showListWith"
                            ]

getText :: Symbol -> Text
getText (Symbol s) = s

hoogleComps :: [Edge]
hoogleComps = filter (\e -> (edgeSymbol e `notElem` speciallyTreatedFunctions))
            $ map (uncurry parseHoogleComponent)
            $ Map.toList hoogleComponents

anyFunc :: Node
-- anyFunc = Node [f34, f36]
anyFunc = Node [f3, f41, f42, f43, f48, f49]
-- anyFunc = Node [f1, f32, f10, f12, f16, f17, f18, f19, f21, f22, f23, f24, f28, f29, f30, f31]
-- anyFunc = Node hoogleComps
-- anyFunc = Node [f16, f23, f24, f10, f19, f17, f18, f20, f25, f26, f1, f2, f3, f4, f5, f6, f7, f8, f9, f11, f12, f13, f14, f15, f21, f22]

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
-- exportTypeToFta (ExportCons s [])  = typeConst s
exportTypeToFta (ExportCons "Fun" [t1, t2])  = arrowType (exportTypeToFta t1) (exportTypeToFta t2)
-- exportTypeToFta (ExportCons s [t]) = constrType1 s (exportTypeToFta t)
-- exportTypeToFta (ExportCons s [t1, t2]) = constrType2 s (exportTypeToFta t1) (exportTypeToFta t2)
exportTypeToFta (ExportCons d ts) = if isUpper (Text.head d) then foldl appType (typeConst d) (map exportTypeToFta ts)
                                                        else foldl appType (exportTypeToFta (ExportVar d)) (map exportTypeToFta ts)
exportTypeToFta (ExportForall _ t) = exportTypeToFta t



allConstructors :: [(Text, Int)]
allConstructors = nubOrd (concatMap getConstructors (Map.elems hoogleComponents)) \\ [("Fun", 2)]
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

rawHooglePlusExport :: String
rawHooglePlusExport = [r|fromList [("(Data.Bool.&&)",ExportFun (ExportCons "Bool" []) (ExportFun (ExportCons "Bool" []) (ExportCons "Bool" []))),("(Data.Bool.||)",ExportFun (ExportCons "Bool" []) (ExportFun (ExportCons "Bool" []) (ExportCons "Bool" []))),("(Data.Eq./=)",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Bool" []))))),("(Data.Eq.==)",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Bool" []))))),("(GHC.List.!!)",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "Int" []) (ExportVar "a")))),("(GHC.List.++)",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("@@hplusTCInstance@@0EqBool",ExportCons "@@hplusTC@@Eq" [ExportCons "Bool" []]),("@@hplusTCInstance@@0EqChar",ExportCons "@@hplusTC@@Eq" [ExportCons "Char" []]),("@@hplusTCInstance@@0EqDouble",ExportCons "@@hplusTC@@Eq" [ExportCons "Double" []]),("@@hplusTCInstance@@0EqFloat",ExportCons "@@hplusTC@@Eq" [ExportCons "Float" []]),("@@hplusTCInstance@@0EqInt",ExportCons "@@hplusTC@@Eq" [ExportCons "Int" []]),("@@hplusTCInstance@@0EqUnit",ExportCons "@@hplusTC@@Eq" [ExportCons "Unit" []]),("@@hplusTCInstance@@0IsString",ExportCons "@@hplusTC@@IsString" [ExportCons "Builder" []]),("@@hplusTCInstance@@0NumDouble",ExportCons "@@hplusTC@@Num" [ExportCons "Double" []]),("@@hplusTCInstance@@0NumFloat",ExportCons "@@hplusTC@@Num" [ExportCons "Float" []]),("@@hplusTCInstance@@0NumInt",ExportCons "@@hplusTC@@Num" [ExportCons "Int" []]),("@@hplusTCInstance@@0OrdBool",ExportCons "@@hplusTC@@Ord" [ExportCons "Bool" []]),("@@hplusTCInstance@@0OrdChar",ExportCons "@@hplusTC@@Ord" [ExportCons "Char" []]),("@@hplusTCInstance@@0OrdDouble",ExportCons "@@hplusTC@@Ord" [ExportCons "Double" []]),("@@hplusTCInstance@@0OrdFloat",ExportCons "@@hplusTC@@Ord" [ExportCons "Float" []]),("@@hplusTCInstance@@0OrdInt",ExportCons "@@hplusTC@@Ord" [ExportCons "Int" []]),("@@hplusTCInstance@@0ShowBool",ExportCons "@@hplusTC@@Show" [ExportCons "Bool" []]),("@@hplusTCInstance@@0ShowChar",ExportCons "@@hplusTC@@Show" [ExportCons "Char" []]),("@@hplusTCInstance@@0ShowDouble",ExportCons "@@hplusTC@@Show" [ExportCons "Double" []]),("@@hplusTCInstance@@0ShowFloat",ExportCons "@@hplusTC@@Show" [ExportCons "Float" []]),("@@hplusTCInstance@@0ShowInt",ExportCons "@@hplusTC@@Show" [ExportCons "Int" []]),("@@hplusTCInstance@@0ShowUnit",ExportCons "@@hplusTC@@Show" [ExportCons "Unit" []]),("@@hplusTCInstance@@1Show",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "b"]) (ExportCons "@@hplusTC@@Show" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@2Read",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Read" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Read" [ExportVar "b"]) (ExportCons "@@hplusTC@@Read" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@3Ord",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "b"]) (ExportCons "@@hplusTC@@Ord" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@4Eq",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "b"]) (ExportCons "@@hplusTC@@Eq" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@6Semigroup",ExportForall "b" (ExportForall "a" (ExportCons "@@hplusTC@@Semigroup" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))),("@@hplusTCInstance@@9Eq",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportCons "@@hplusTC@@Eq" [ExportCons "List" [ExportVar "a"]]))),("Cons",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("Data.Bool.False",ExportCons "Bool" []),("Data.Bool.True",ExportCons "Bool" []),("Data.Bool.bool",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportFun (ExportCons "Bool" []) (ExportVar "a"))))),("Data.Bool.not",ExportFun (ExportCons "Bool" []) (ExportCons "Bool" [])),("Data.Bool.otherwise",ExportCons "Bool" []),("Data.ByteString.Builder.byteString",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.byteStringHex",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.char7",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.char8",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.charUtf8",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleBE",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleDec",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleHexFixed",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleLE",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatBE",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatDec",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatHexFixed",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatLE",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.hPutBuilder",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Builder" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Builder.int16BE",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16Dec",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16HexFixed",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16LE",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32BE",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32Dec",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32HexFixed",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32LE",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64BE",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64Dec",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64HexFixed",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64LE",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8Dec",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8HexFixed",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.intDec",ExportFun (ExportCons "Int" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.integerDec",ExportFun (ExportCons "Integer" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.lazyByteString",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.lazyByteStringHex",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.shortByteString",ExportFun (ExportCons "ShortByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.string7",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.string8",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.stringUtf8",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.toLazyByteString",ExportFun (ExportCons "Builder" []) (ExportCons "ByteString" [])),("Data.ByteString.Builder.word16BE",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16Dec",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16Hex",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16HexFixed",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16LE",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32BE",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32Dec",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32Hex",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32HexFixed",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32LE",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64BE",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64Dec",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64Hex",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64HexFixed",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64LE",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8Dec",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8Hex",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8HexFixed",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.wordDec",ExportFun (ExportCons "Word" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.wordHex",ExportFun (ExportCons "Word" []) (ExportCons "Builder" [])),("Data.ByteString.Lazy.all",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.any",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.append",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.appendFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.break",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.concat",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.concatMap",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.cons",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.cons'",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.copy",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.count",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Int64" []))),("Data.ByteString.Lazy.cycle",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.drop",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.dropWhile",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.elem",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.elemIndex",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.elemIndexEnd",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.elemIndices",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.empty",ExportCons "ByteString" []),("Data.ByteString.Lazy.filter",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.find",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Word8" []]))),("Data.ByteString.Lazy.findIndex",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.findIndices",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.foldl",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "Word8" []) (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldl'",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "Word8" []) (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldl1",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.foldl1'",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.foldlChunks",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldr",ExportForall "a" (ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldr1",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.foldrChunks",ExportForall "a" (ExportFun (ExportFun (ExportCons "ByteString" []) (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.fromChunks",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.fromStrict",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.getContents",ExportCons "IO" [ExportCons "ByteString" []]),("Data.ByteString.Lazy.group",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.groupBy",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hGet",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Int" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hGetContents",ExportFun (ExportCons "Handle" []) (ExportCons "IO" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.hGetNonBlocking",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Int" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hPut",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.hPutNonBlocking",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hPutStr",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.head",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.index",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "Int64" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.init",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.inits",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.interact",ExportFun (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.intercalate",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.intersperse",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.isPrefixOf",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.isSuffixOf",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.iterate",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" [])) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.last",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.length",ExportFun (ExportCons "ByteString" []) (ExportCons "Int64" [])),("Data.ByteString.Lazy.map",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.mapAccumL",ExportForall "acc" (ExportFun (ExportFun (ExportVar "acc") (ExportFun (ExportCons "Word8" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "Word8" []]))) (ExportFun (ExportVar "acc") (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "ByteString" []]))))),("Data.ByteString.Lazy.mapAccumR",ExportForall "acc" (ExportFun (ExportFun (ExportVar "acc") (ExportFun (ExportCons "Word8" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "Word8" []]))) (ExportFun (ExportVar "acc") (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "ByteString" []]))))),("Data.ByteString.Lazy.maximum",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.minimum",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.notElem",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.null",ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" [])),("Data.ByteString.Lazy.pack",ExportFun (ExportCons "List" [ExportCons "Word8" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.partition",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.putStr",ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.putStrLn",ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.readFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "IO" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.repeat",ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.replicate",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.reverse",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.scanl",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])))),("Data.ByteString.Lazy.singleton",ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.snoc",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.span",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.split",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.splitAt",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.splitWith",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.stripPrefix",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.stripSuffix",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.tail",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.tails",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.take",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.takeWhile",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.toChunks",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.toStrict",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.transpose",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.uncons",ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "ByteString" []]])),("Data.ByteString.Lazy.unfoldr",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "Word8" [],ExportVar "a"]])) (ExportFun (ExportVar "a") (ExportCons "ByteString" [])))),("Data.ByteString.Lazy.unpack",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Word8" []])),("Data.ByteString.Lazy.unsnoc",ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "Word8" []]])),("Data.ByteString.Lazy.unzip",ExportFun (ExportCons "List" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "Word8" []]]) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []])),("Data.ByteString.Lazy.writeFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.zip",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "Word8" []]]))),("Data.ByteString.Lazy.zipWith",ExportForall "a" (ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportVar "a"))) (ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportVar "a"]))))),("Data.Either.Left",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "a") (ExportCons "Either" [ExportVar "a",ExportVar "b"])))),("Data.Either.Right",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "b") (ExportCons "Either" [ExportVar "a",ExportVar "b"])))),("Data.Either.either",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "c")) (ExportFun (ExportFun (ExportVar "b") (ExportVar "c")) (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportVar "c"))))))),("Data.Either.fromLeft",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportVar "a"))))),("Data.Either.fromRight",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "b") (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportVar "b"))))),("Data.Either.isLeft",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportCons "Bool" [])))),("Data.Either.isRight",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportCons "Bool" [])))),("Data.Either.lefts",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "List" [ExportVar "a"])))),("Data.Either.partitionEithers",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]])))),("Data.Either.rights",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "List" [ExportVar "b"])))),("Data.List.group",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportCons "List" [ExportVar "a"]])))),("Data.Maybe.Just",ExportForall "a" (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "a"]))),("Data.Maybe.Nothing",ExportForall "a" (ExportCons "Maybe" [ExportVar "a"])),("Data.Maybe.catMaybes",ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]]) (ExportCons "List" [ExportVar "a"]))),("Data.Maybe.fromJust",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportVar "a"))),("Data.Maybe.fromMaybe",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportVar "a")))),("Data.Maybe.isJust",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "Bool" []))),("Data.Maybe.isNothing",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "Bool" []))),("Data.Maybe.listToMaybe",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Maybe" [ExportVar "a"]))),("Data.Maybe.mapMaybe",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "b"])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("Data.Maybe.maybe",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "b") (ExportFun (ExportFun (ExportVar "a") (ExportVar "b")) (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportVar "b")))))),("Data.Maybe.maybeToList",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("Data.Tuple.curry",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "c")) (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))))))),("Data.Tuple.fst",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "a")))),("Data.Tuple.snd",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "b")))),("Data.Tuple.swap",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportCons "Pair" [ExportVar "b",ExportVar "a"])))),("Data.Tuple.uncurry",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))) (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "c")))))),("GHC.Char.chr",ExportFun (ExportCons "Int" []) (ExportCons "Char" [])),("GHC.Char.eqChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "Char" []) (ExportCons "Bool" []))),("GHC.Char.neChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "Char" []) (ExportCons "Bool" []))),("GHC.List.all",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" [])))),("GHC.List.and",ExportFun (ExportCons "List" [ExportCons "Bool" []]) (ExportCons "Bool" [])),("GHC.List.any",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" [])))),("GHC.List.break",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])))),("GHC.List.concat",ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "List" [ExportVar "a"]]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.concatMap",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "b"])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("GHC.List.cycle",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.drop",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.dropWhile",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.elem",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" []))))),("GHC.List.filter",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.foldl",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "b")))))),("GHC.List.foldl'",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "b")))))),("GHC.List.foldl1",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.foldl1'",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.foldr",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "b")))))),("GHC.List.foldr1",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.head",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a"))),("GHC.List.init",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.iterate",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "a")) (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"])))),("GHC.List.iterate'",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "a")) (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"])))),("GHC.List.last",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a"))),("GHC.List.length",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Int" []))),("GHC.List.lookup",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]) (ExportCons "Maybe" [ExportVar "b"])))))),("GHC.List.map",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "b")) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("GHC.List.maximum",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.minimum",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.notElem",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" []))))),("GHC.List.null",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" []))),("GHC.List.or",ExportFun (ExportCons "List" [ExportCons "Bool" []]) (ExportCons "Bool" [])),("GHC.List.product",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Num" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.repeat",ExportForall "a" (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"]))),("GHC.List.replicate",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"])))),("GHC.List.reverse",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.scanl",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"])))))),("GHC.List.scanl'",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"])))))),("GHC.List.scanl1",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.scanr",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"])))))),("GHC.List.scanr1",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.span",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])))),("GHC.List.splitAt",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])))),("GHC.List.sum",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Num" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "a")))),("GHC.List.tail",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.take",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.takeWhile",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.uncons",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Maybe" [ExportCons "Pair" [ExportVar "a",ExportCons "List" [ExportVar "a"]]]))),("GHC.List.unzip",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]])))),("GHC.List.unzip3",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportCons "Pair" [ExportVar "a",ExportVar "b"],ExportVar "c"]]) (ExportCons "Pair" [ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]],ExportCons "List" [ExportVar "c"]]))))),("GHC.List.zip",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]))))),("GHC.List.zip3",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportFun (ExportCons "List" [ExportVar "c"]) (ExportCons "List" [ExportCons "Pair" [ExportCons "Pair" [ExportVar "a",ExportVar "b"],ExportVar "c"]]))))))),("GHC.List.zipWith",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportCons "List" [ExportVar "c"]))))))),("GHC.List.zipWith3",ExportForall "d" (ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportFun (ExportVar "c") (ExportVar "d")))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportFun (ExportCons "List" [ExportVar "c"]) (ExportCons "List" [ExportVar "d"]))))))))),("Nil",ExportForall "a" (ExportCons "List" [ExportVar "a"])),("Pair",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportCons "Pair" [ExportVar "a",ExportVar "b"]))))),("Text.Show.show",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportCons "List" [ExportCons "Char" []])))),("Text.Show.showChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))),("Text.Show.showList",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showListWith",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showParen",ExportFun (ExportCons "Bool" []) (ExportFun (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []])) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []])))),("Text.Show.showString",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))),("Text.Show.shows",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showsPrec",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "Int" []) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))))]|]

reduceFully :: Node -> Node
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)

checkSolution :: String -> [Term] -> IO ()
checkSolution target [] = return ()
checkSolution target (s:solutions)
  | show (prettyTerm s) == target = print (prettyTerm s)
  | otherwise = do
    print (prettyTerm s)
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

reduceFullyAndLog :: Node -> IO Node
reduceFullyAndLog = go 0
  where
    go i n = do putStrLn $ "Round " ++ show i ++ ": " ++ show (nodeCount n) ++ " nodes, " ++ show (edgeCount n) ++ " edges"
                hFlush stdout
                putStrLn (renderDot $ toDot n)
                if i == 5 then error "stop" else return ()
                -- when (i == 21) $ do
                --   let Node es = n
                --   let nn = (edgeChildren (es !! 0)) !! 1
                --   let Node es = nn
                --   mapM_ (\(e, j) -> withFile (show i ++ "." ++ show j ++ ".before") WriteMode (\hdl -> hPutStr hdl (renderDot $ toDot $ Node [e]))) (zip es [0..])
                -- let d = constraintAdjustedDepth n
                -- putStrLn $ "Depth: " ++ show d
                let n' = reducePartially'' (-1) n
                -- putStrLn $ renderDot $ toDot n'
                -- n' <- minReductionFail n
                -- when (i == 21) $ do
                --   let Node es = n'
                --   let nn = (edgeChildren (es !! 0)) !! 1
                --   let Node es = nn
                --   mapM_ (\(e, j) -> withFile (show i ++ "." ++ show j ++ ".after") WriteMode (\hdl -> hPutStr hdl (renderDot $ toDot $ Node [e]))) (zip es [0..])
                --   error "stop at 21"
                if n == n' then
                  return n
                else
                  go (i + 1) n'

runBenchmark :: Benchmark -> IO ()
runBenchmark (Benchmark name depth solStr (args, res)) = do
    let names = []
    let hardBenchmarks = []
    -- let hardBenchmarks = ["both", "multiAppPair", "cartProduct", "headLast", "takeNdropM", "areEq"]
    when (name `elem` names || null names)
      (do
        start <- getCurrentTime
        putStrLn $ "Running benchmark " ++ Text.unpack name
        let argNodes = map (Bi.bimap Symbol exportTypeToFta) args
        let resNode = exportTypeToFta res
        let anyArg = Node (map (uncurry constArg) argNodes)
        print argNodes
        let !filterNode = filterType (relevantTermsUptoK anyArg argNodes depth) resNode
        nodeCons <- getCurrentTime
        -- print $ "Construction time: " ++ show (diffUTCTime nodeCons start)
        
        do
        -- timeout (200 * 10^6) $ do
            -- let reducedNode = if name `elem` hardBenchmarks 
            --                   then (withoutRedundantEdges . reducePartially) filterNode
            --                   else reduceFully filterNode
            -- let reducedNode = reduceFully filterNode
            reducedNode <- reduceFullyAndLog filterNode
            -- putStrLn $ renderDot . toDot $ reducedNode
            let foldedNode = refold reducedNode
            -- putStrLn $ renderDot . toDot $ foldedNode
            prettyPrintAllTerms solStr foldedNode
            -- let n' = reducePartially EmptyConstraints filterNode
--             Text.putStrLn $ "Nodes: "        <> Text.pack (show (nodeCount   n'))
--             Text.putStrLn $ "Edges: "        <> Text.pack (show (edgeCount   n'))
--             Text.putStrLn $ "Max indegree: " <> Text.pack (show (maxIndegree n'))
-- #ifdef PROFILE_CACHES
--             Memoization.printAllCacheMetrics
--             Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Node))
--             Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Edge))
--             Text.putStrLn ""
-- #endif

        end <- getCurrentTime
        print $ "Time: " ++ show (diffUTCTime end start)
        hFlush stdout)

replicator :: Node
replicator = Node [
    mkEdge "Pair" [
      Node [
        mkEdge "Pair" [replicatorTau, replicatorTau] (mkEqConstraints [[path [0,0], path [0,1], path [1]]])
      ],
      Node [
        -- mkEdge "Pair" [tau, tau]
        -- (mkEqConstraints [[path [0,0], path [0,1], path [1]]])
        Edge "Pair" [replicatorTau, replicatorTau]
      ]
    ]
    (mkEqConstraints [[path [0,0], path [0,1], path [1]]])
  ]

counterExample :: Node
counterExample = Node [
    mkEdge "f" [
      Node [
        mkEdge "g" [
          Node [Edge "h" [
            Node [
              Edge "Pair" [replicatorTau, replicatorTau],
              Edge "var2" []
            ],
            Node [Edge "Pair" [
              replicatorTau,
              -- Node [Edge "Pair" [
              --   Node [
              --     Edge "Pair" [replicatorTau, replicatorTau]
              --   ], 
              --   var2]
              -- ]
              replicatorTau
            ]]
          ]]
        ]
        (mkEqConstraints [[path [0,0], path [0,1,0]]]),
        Edge "gg" [
          Node [Edge "Pair" [var2, var2]]
        ]
      ]
      -- Node [Edge "e" [
      --   replicatorTau,
      --   Node [
      --     Edge "Pair" [replicatorTau, replicatorTau],
      --     Edge "var2" []
      --   ]
      -- ]]
    ]
    (mkEqConstraints [[path [0,0,0], path [0,0,1]]])
  ]

loop2 :: Node
loop2 = Node [
                mkEdge "g" [
                    Node [
                        mkEdge "Pair" [
                            Node [
                                Edge "List" [
                                    -- Node [Edge "List" [replicatorTau]]
                                    replicatorTau
                                    ]
                                ],
                              replicatorTau
                            -- Node [Edge "List" [replicatorTau]]
                            ]
                            (mkEqConstraints [[path [0,0], path [1]]])
                        ],
                    Node [
                        mkEdge "Pair" [
                            Node [
                                Edge "List" [
                                    -- Node [Edge "List" [replicatorTau]]
                                    replicatorTau
                                    ]
                                ],
                            replicatorTau
                            ]
                            (mkEqConstraints [[path [0], path [1]]])
                        ]
                    ]
                    (mkEqConstraints [[path [0,1,0], path [1,1]], [path [0,0], path [1,0]]])
                ]

testBenchmark1 :: Benchmark
testBenchmark1 = Benchmark "evalState" 7 "app(app(liftM, fst), app(app(app(runStateT, tc0), m), st)))" 
  ([ ("tc0", (ExportCons "Monad" [ExportVar "a"]))
   , ("m", (ExportCons "StateT" [ExportVar "b", ExportVar "a", ExportVar "c"]))
   , ("st", ExportVar "b")
   ], 
   (ExportCons "a" [ExportVar "c"]))

testBenchmark2 :: Benchmark
testBenchmark2 = Benchmark "monadList" 3 "app(app(return, List@Monad), x)" 
  ([ ("x", ExportVar "a")], 
   (ExportCons "List" [ExportVar "a"]))

testBenchmark3 :: Benchmark
testBenchmark3 = Benchmark "composeMonads" 9 "app(app(app((=<<), tc0), app(app((.), app(return, tc0)), app(app((=<<), tc1), f))), sm)"
  ([ ("tc0", (ExportCons "Monad" [ExportVar "c"]))
   , ("tc1", (ExportCons "Monad" [ExportVar "d"]))
   , ("sm", (ExportCons "c" [ExportCons "d" [ExportVar "a"]]))
   , ("f", (ExportFun (ExportVar "a") (ExportCons "d" [ExportVar "b"])))
   ], 
   (ExportCons "c" [ExportCons "d" [ExportVar "b"]]))

-- | used components: Node [f17, f40, f42, f43, f32]
testBenchmark4 :: Benchmark
testBenchmark4 = Benchmark "traverseDAG" 8 "app(app(app(app(app(foldM, tc0), List@Foldable), f), Nil), app(app(map, fst), dag))"
  ([("tc0", ExportCons "Monad" [ExportVar "c"])
   ,("f", ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportVar "b") (ExportCons "c" [ExportCons "List" [ExportVar "a"]])))
   ,("dag", ExportCons "List" [ExportCons "Pair" [ExportVar "b", ExportVar "a"]])
   ],
   (ExportCons "c" [ExportCons "List" [ExportVar "a"]]))

-- | used components: Node [f13, f41]
testBenchmark5 :: Benchmark
testBenchmark5 = Benchmark "extractEitherValues" 8 "app(app(app(app(mapM, tc1), tc0), app(app(either, Data.Function.id), Data.Function.id)), eithers)"
  ([("tc0", ExportCons "Traversable" [ExportVar "d"])
   ,("tc1", ExportCons "Monad" [ExportVar "c"])
   ,("eithers", ExportCons "d" [ExportCons "Either" [ExportCons "c" [ExportVar "b"], ExportCons "c" [ExportVar "b"]]])
   ],
  (ExportCons "c" [ExportCons "d" [ExportVar "b"]]))

testBenchmark6 :: Benchmark
testBenchmark6 = Benchmark "iterateLines" 7 "app(app(app(evalStateT, tc0), st), app(app(zip, xs), app(lines, input)))"
  ([("tc0", ExportCons "Monad" [ExportVar "c"])
   ,("st", ExportCons "StateT" [ExportCons "List" [ExportCons "Pair" [ExportVar "a", ExportCons "String" []]], ExportVar "c", ExportVar "b"])
   ,("xs", ExportCons "List" [ExportVar "a"])
   ,("input", ExportCons "String" [])
   ],
  ExportCons "c" [ExportVar "b"])

-- | used components: Node [f47, f34]
testBenchmark7 :: Benchmark
testBenchmark7 = Benchmark "maybeToTransformer" 5 "app(app(MaybeT, tc0), app(app(return, tc0), mb))"
  ([("tc0", ExportCons "Monad" [ExportVar "c"])
   ,("mb", ExportCons "Maybe" [ExportVar "a"])
   ],
  ExportCons "MaybeT" [ExportVar "c", ExportVar "a"])

-- | used components: Node [f3, f41, f42, f43, f48, f49]
testBenchmark8 :: Benchmark
testBenchmark8 = Benchmark "execThreads" 8 "app(app(fromMaybe, def), app(app(app(msum, Maybe@MonadPlus), List@Foldable), app(app(map, f), threads)))"
  ([("f", ExportFun (ExportVar "b") (ExportCons "Maybe" [ExportVar "a"]))
   ,("threads", ExportCons "List" [ExportVar "b"])
   ,("def", ExportVar "a")],
  ExportVar "a")