{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module TermSearch where

import ECDFTA

import           Data.Map ( Map )
import qualified Data.Map as Map

import Data.Text ( Text )
import qualified Data.Text as Text
import Text.RawString.QQ

import Debug.Trace
import Data.Function
import Data.List hiding (union)

------------------------------------------------------------------------------

tau :: Node
tau = Node [Edge "tau" []]

typeConst :: Text -> Node
typeConst s = Node [Edge (Symbol s) []]

constrType :: Text -> Node -> Node
constrType s n = Node [Edge (Symbol s) [n]]

constrType2 :: Text -> Node -> Node -> Node
constrType2 s n1 n2 = Node [Edge (Symbol s) [n1, n2]]

maybeType :: Node -> Node
maybeType = constrType "Maybe"

listType :: Node -> Node
listType = constrType "[]"

theArrowNode :: Node
theArrowNode = Node [Edge "(->)" []]

arrowType :: Node -> Node -> Node
arrowType n1 n2 = Node [Edge "->" [theArrowNode, n1, n2]]

constFunc :: Symbol -> Node -> Edge
constFunc s t = Edge s [t]

app :: Node -> Node -> Node
app n1 n2 = Node [mkEdge "app" [getPath (path [0, 2]) n1, theArrowNode, n1, n2]
                               [ EqConstraint (path [1])      (path [2, 0, 0])
                               , EqConstraint (path [2,0, 1]) (path [3, 0])
                               , EqConstraint (path [0])      (path [2, 0, 2])
                               ]
                 ]

f1, f2, f3, f4, f5, f6, f7 :: Edge
f1 = constFunc "Nothing" (maybeType tau)
f2 = constFunc "Just" (arrowType tau (maybeType tau))
f3 = constFunc "fromMaybe" (arrowType tau (arrowType (maybeType tau) tau))
f4 = constFunc "listToMaybe" (arrowType (listType tau) (maybeType tau))
f5 = constFunc "maybeToList" (arrowType (maybeType tau) (listType tau))
f6 = constFunc "catMaybes" (arrowType (listType (maybeType tau)) (listType tau))
f7 = constFunc "mapMaybe" (arrowType (arrowType tau (maybeType tau)) (arrowType (listType tau) (listType tau)))

arg1, arg2 :: Edge
arg1 = constFunc "def" tau
arg2 = constFunc "mbs" (listType (maybeType tau))

anyArg :: Node
anyArg = Node [arg1, arg2]

anyFunc :: Node
anyFunc = Node $ map (\(k, v) -> parseHoogleComponent k v) $ Map.toList hoogleComponents
--anyFunc = Node [f1, f2, f3, f4, f5, f6, f7]

size1, size2, size3, size4, size5, size6 :: Node
size1 = union [anyArg, anyFunc]
size2 = app size1 size1
size3 = union [app size2 size1, app size1 size2]
size4 = union [app size3 size1, app size2 size2, app size1 size3]
size5 = union [app size4 size1, app size3 size2, app size2 size3, app size1 size4]
size6 = union [app size5 size1, app size4 size2, app size3 size3, app size2 size4, app size1 size5]

uptoSize6UniqueRep :: Node
uptoSize6UniqueRep = union [size1, size2, size3, size4, size5, size6]

uptoDepth2 :: Node
uptoDepth2 = union [size1, app size1 size1]

uptoDepth3 :: Node
uptoDepth3 = union [uptoDepth2, app uptoDepth2 uptoDepth2]

uptoDepth4 :: Node
uptoDepth4 = union [uptoDepth3, app uptoDepth3 uptoDepth3]

filterType :: Node -> Node -> Node
filterType n t = Node [mkEdge "filter" [t, n] [EqConstraint (path [0]) (path [1, 0])]]

prettyTerm :: Term -> Term
prettyTerm (Term "app" [_, _, a, b]) = Term "app" [prettyTerm a, prettyTerm b]
prettyTerm (Term "filter" [_, a])    = prettyTerm a
prettyTerm (Term s [_]) = Term s []

dropTypes :: Node -> Node
dropTypes (Node es) = Node (map dropEdgeTypes es)
  where
    dropEdgeTypes (Edge "app"    [_, _, a, b]) = Edge "app" [dropTypes a, dropTypes b]
    dropEdgeTypes (Edge "filter" [_, a]      ) = Edge "filter" [dropTypes a]
    dropEdgeTypes (Edge s        [_]         ) = Edge s []


---------------------------------------------------------------------------------------
-------------------------- Importing components from Hoogle+ --------------------------
---------------------------------------------------------------------------------------


data ExportType = ExportVar Text
                | ExportFun ExportType ExportType
                | ExportCons Text [ExportType]
                | ExportForall Text ExportType
  deriving ( Eq, Ord, Show, Read )

exportTypeToFta :: ExportType -> Node
exportTypeToFta (ExportVar v) = tau -- This will need to change for real polymorphism
exportTypeToFta (ExportFun t1 t2) = arrowType (exportTypeToFta t1) (exportTypeToFta t2)
exportTypeToFta (ExportCons s [])  = typeConst s
exportTypeToFta (ExportCons "Fun" [t1, t2])  = arrowType (exportTypeToFta t1) (exportTypeToFta t2)
exportTypeToFta (ExportCons s [t]) = constrType s (exportTypeToFta t)
exportTypeToFta (ExportCons s [t1, t2]) = constrType2 s (exportTypeToFta t1) (exportTypeToFta t2)
exportTypeToFta (ExportForall _ t) = exportTypeToFta t

parseHoogleComponent :: Text -> ExportType -> Edge
parseHoogleComponent name t = Edge (Symbol name) [exportTypeToFta t]

hoogleComponents :: Map Text ExportType
hoogleComponents = read rawHooglePlusExport

rawHooglePlusExport :: String
rawHooglePlusExport = [r|fromList [("(Data.Bool.&&)",ExportFun (ExportCons "Bool" []) (ExportFun (ExportCons "Bool" []) (ExportCons "Bool" []))),("(Data.Bool.||)",ExportFun (ExportCons "Bool" []) (ExportFun (ExportCons "Bool" []) (ExportCons "Bool" []))),("(Data.Eq./=)",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Bool" []))))),("(Data.Eq.==)",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Bool" []))))),("(Data.Function.$)",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "b")) (ExportFun (ExportVar "a") (ExportVar "b"))))),("(Data.Function.$)'ho'",ExportForall "b" (ExportForall "a" (ExportCons "Fun" [ExportCons "Fun" [ExportVar "a",ExportVar "b"],ExportCons "Fun" [ExportVar "a",ExportVar "b"]]))),("(GHC.List.++)",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("@@hplusTCInstance@@0EqBool",ExportCons "@@hplusTC@@Eq" [ExportCons "Bool" []]),("@@hplusTCInstance@@0EqChar",ExportCons "@@hplusTC@@Eq" [ExportCons "Char" []]),("@@hplusTCInstance@@0EqDouble",ExportCons "@@hplusTC@@Eq" [ExportCons "Double" []]),("@@hplusTCInstance@@0EqFloat",ExportCons "@@hplusTC@@Eq" [ExportCons "Float" []]),("@@hplusTCInstance@@0EqInt",ExportCons "@@hplusTC@@Eq" [ExportCons "Int" []]),("@@hplusTCInstance@@0EqUnit",ExportCons "@@hplusTC@@Eq" [ExportCons "Unit" []]),("@@hplusTCInstance@@0IsString",ExportCons "@@hplusTC@@IsString" [ExportCons "Builder" []]),("@@hplusTCInstance@@0OrdBool",ExportCons "@@hplusTC@@Ord" [ExportCons "Bool" []]),("@@hplusTCInstance@@0OrdChar",ExportCons "@@hplusTC@@Ord" [ExportCons "Char" []]),("@@hplusTCInstance@@0OrdDouble",ExportCons "@@hplusTC@@Ord" [ExportCons "Double" []]),("@@hplusTCInstance@@0OrdFloat",ExportCons "@@hplusTC@@Ord" [ExportCons "Float" []]),("@@hplusTCInstance@@0OrdInt",ExportCons "@@hplusTC@@Ord" [ExportCons "Int" []]),("@@hplusTCInstance@@0ShowBool",ExportCons "@@hplusTC@@Show" [ExportCons "Bool" []]),("@@hplusTCInstance@@0ShowChar",ExportCons "@@hplusTC@@Show" [ExportCons "Char" []]),("@@hplusTCInstance@@0ShowDouble",ExportCons "@@hplusTC@@Show" [ExportCons "Double" []]),("@@hplusTCInstance@@0ShowFloat",ExportCons "@@hplusTC@@Show" [ExportCons "Float" []]),("@@hplusTCInstance@@0ShowInt",ExportCons "@@hplusTC@@Show" [ExportCons "Int" []]),("@@hplusTCInstance@@0ShowUnit",ExportCons "@@hplusTC@@Show" [ExportCons "Unit" []]),("@@hplusTCInstance@@1Show",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "b"]) (ExportCons "@@hplusTC@@Show" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@2Read",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Read" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Read" [ExportVar "b"]) (ExportCons "@@hplusTC@@Read" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@3Ord",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Ord" [ExportVar "b"]) (ExportCons "@@hplusTC@@Ord" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@4Eq",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "b"]) (ExportCons "@@hplusTC@@Eq" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))))),("@@hplusTCInstance@@6Semigroup",ExportForall "b" (ExportForall "a" (ExportCons "@@hplusTC@@Semigroup" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]))),("Cons",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("Data.Bool.False",ExportCons "Bool" []),("Data.Bool.True",ExportCons "Bool" []),("Data.Bool.bool",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportFun (ExportCons "Bool" []) (ExportVar "a"))))),("Data.Bool.not",ExportFun (ExportCons "Bool" []) (ExportCons "Bool" [])),("Data.Bool.otherwise",ExportCons "Bool" []),("Data.ByteString.Builder.byteString",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.byteStringHex",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.char7",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.char8",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.charUtf8",ExportFun (ExportCons "Char" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleBE",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleDec",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleHexFixed",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.doubleLE",ExportFun (ExportCons "Double" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatBE",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatDec",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatHexFixed",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.floatLE",ExportFun (ExportCons "Float" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.hPutBuilder",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Builder" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Builder.int16BE",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16Dec",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16HexFixed",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int16LE",ExportFun (ExportCons "Int16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32BE",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32Dec",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32HexFixed",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int32LE",ExportFun (ExportCons "Int32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64BE",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64Dec",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64HexFixed",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int64LE",ExportFun (ExportCons "Int64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8Dec",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.int8HexFixed",ExportFun (ExportCons "Int8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.intDec",ExportFun (ExportCons "Int" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.integerDec",ExportFun (ExportCons "Integer" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.lazyByteString",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.lazyByteStringHex",ExportFun (ExportCons "ByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.shortByteString",ExportFun (ExportCons "ShortByteString" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.string7",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.string8",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.stringUtf8",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "Builder" [])),("Data.ByteString.Builder.toLazyByteString",ExportFun (ExportCons "Builder" []) (ExportCons "ByteString" [])),("Data.ByteString.Builder.word16BE",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16Dec",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16Hex",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16HexFixed",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word16LE",ExportFun (ExportCons "Word16" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32BE",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32Dec",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32Hex",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32HexFixed",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word32LE",ExportFun (ExportCons "Word32" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64BE",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64Dec",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64Hex",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64HexFixed",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word64LE",ExportFun (ExportCons "Word64" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8Dec",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8Hex",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.word8HexFixed",ExportFun (ExportCons "Word8" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.wordDec",ExportFun (ExportCons "Word" []) (ExportCons "Builder" [])),("Data.ByteString.Builder.wordHex",ExportFun (ExportCons "Word" []) (ExportCons "Builder" [])),("Data.ByteString.Lazy.all",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.any",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.append",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.appendFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.break",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.concat",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.concatMap",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.cons",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.cons'",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.copy",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.count",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Int64" []))),("Data.ByteString.Lazy.drop",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.dropWhile",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.elem",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.elemIndex",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.elemIndexEnd",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.elemIndices",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.empty",ExportCons "ByteString" []),("Data.ByteString.Lazy.filter",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.find",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Word8" []]))),("Data.ByteString.Lazy.findIndex",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.findIndices",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Int64" []]))),("Data.ByteString.Lazy.foldr",ExportForall "a" (ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.foldrChunks",ExportForall "a" (ExportFun (ExportFun (ExportCons "ByteString" []) (ExportFun (ExportVar "a") (ExportVar "a"))) (ExportFun (ExportVar "a") (ExportFun (ExportCons "ByteString" []) (ExportVar "a"))))),("Data.ByteString.Lazy.fromChunks",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.fromStrict",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.getContents",ExportCons "IO" [ExportCons "ByteString" []]),("Data.ByteString.Lazy.group",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.groupBy",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" []))) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hGet",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Int" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hGetContents",ExportFun (ExportCons "Handle" []) (ExportCons "IO" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.hGetNonBlocking",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "Int" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hPut",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.hPutNonBlocking",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.hPutStr",ExportFun (ExportCons "Handle" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.index",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "Int64" []) (ExportCons "Word8" []))),("Data.ByteString.Lazy.interact",ExportFun (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.intercalate",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.intersperse",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.isPrefixOf",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.isSuffixOf",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.iterate",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" [])) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.length",ExportFun (ExportCons "ByteString" []) (ExportCons "Int64" [])),("Data.ByteString.Lazy.map",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.mapAccumL",ExportForall "acc" (ExportFun (ExportFun (ExportVar "acc") (ExportFun (ExportCons "Word8" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "Word8" []]))) (ExportFun (ExportVar "acc") (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "ByteString" []]))))),("Data.ByteString.Lazy.mapAccumR",ExportForall "acc" (ExportFun (ExportFun (ExportVar "acc") (ExportFun (ExportCons "Word8" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "Word8" []]))) (ExportFun (ExportVar "acc") (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportVar "acc",ExportCons "ByteString" []]))))),("Data.ByteString.Lazy.maximum",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.minimum",ExportFun (ExportCons "ByteString" []) (ExportCons "Word8" [])),("Data.ByteString.Lazy.notElem",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" []))),("Data.ByteString.Lazy.null",ExportFun (ExportCons "ByteString" []) (ExportCons "Bool" [])),("Data.ByteString.Lazy.pack",ExportFun (ExportCons "List" [ExportCons "Word8" []]) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.partition",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.putStr",ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.putStrLn",ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []])),("Data.ByteString.Lazy.readFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "IO" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.repeat",ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.replicate",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.reverse",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.scanl",ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportCons "Word8" []))) (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])))),("Data.ByteString.Lazy.singleton",ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.snoc",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "Word8" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.span",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.split",ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.splitAt",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []]))),("Data.ByteString.Lazy.splitWith",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.stripPrefix",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.stripSuffix",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "ByteString" []]))),("Data.ByteString.Lazy.take",ExportFun (ExportCons "Int64" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.takeWhile",ExportFun (ExportFun (ExportCons "Word8" []) (ExportCons "Bool" [])) (ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" []))),("Data.ByteString.Lazy.toChunks",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.toStrict",ExportFun (ExportCons "ByteString" []) (ExportCons "ByteString" [])),("Data.ByteString.Lazy.transpose",ExportFun (ExportCons "List" [ExportCons "ByteString" []]) (ExportCons "List" [ExportCons "ByteString" []])),("Data.ByteString.Lazy.uncons",ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "ByteString" []]])),("Data.ByteString.Lazy.unfoldr",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "Word8" [],ExportVar "a"]])) (ExportFun (ExportVar "a") (ExportCons "ByteString" [])))),("Data.ByteString.Lazy.unpack",ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Word8" []])),("Data.ByteString.Lazy.unsnoc",ExportFun (ExportCons "ByteString" []) (ExportCons "Maybe" [ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "Word8" []]])),("Data.ByteString.Lazy.unzip",ExportFun (ExportCons "List" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "Word8" []]]) (ExportCons "Pair" [ExportCons "ByteString" [],ExportCons "ByteString" []])),("Data.ByteString.Lazy.writeFile",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "ByteString" []) (ExportCons "IO" [ExportCons "Unit" []]))),("Data.ByteString.Lazy.zip",ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportCons "Pair" [ExportCons "Word8" [],ExportCons "Word8" []]]))),("Data.ByteString.Lazy.zipWith",ExportForall "a" (ExportFun (ExportFun (ExportCons "Word8" []) (ExportFun (ExportCons "Word8" []) (ExportVar "a"))) (ExportFun (ExportCons "ByteString" []) (ExportFun (ExportCons "ByteString" []) (ExportCons "List" [ExportVar "a"]))))),("Data.Either.Left",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "a") (ExportCons "Either" [ExportVar "a",ExportVar "b"])))),("Data.Either.Right",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "b") (ExportCons "Either" [ExportVar "a",ExportVar "b"])))),("Data.Either.either",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "c")) (ExportFun (ExportFun (ExportVar "b") (ExportVar "c")) (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportVar "c"))))))),("Data.Either.isLeft",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportCons "Bool" [])))),("Data.Either.isRight",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Either" [ExportVar "a",ExportVar "b"]) (ExportCons "Bool" [])))),("Data.Either.lefts",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "List" [ExportVar "a"])))),("Data.Either.partitionEithers",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]])))),("Data.Either.rights",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]]) (ExportCons "List" [ExportVar "b"])))),("Data.Function.id",ExportForall "a" (ExportFun (ExportVar "a") (ExportVar "a"))),("Data.Function.id'ho'",ExportForall "a" (ExportCons "Fun" [ExportVar "a",ExportVar "a"])),("Data.Maybe.Just",ExportForall "a" (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "a"]))),("Data.Maybe.Nothing",ExportForall "a" (ExportCons "Maybe" [ExportVar "a"])),("Data.Maybe.catMaybes",ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]]) (ExportCons "List" [ExportVar "a"]))),("Data.Maybe.fromMaybe",ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportVar "a")))),("Data.Maybe.isJust",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "Bool" []))),("Data.Maybe.isNothing",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "Bool" []))),("Data.Maybe.listToMaybe",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Maybe" [ExportVar "a"]))),("Data.Maybe.mapMaybe",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "b"])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("Data.Maybe.maybe",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "b") (ExportFun (ExportFun (ExportVar "a") (ExportVar "b")) (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportVar "b")))))),("Data.Maybe.maybeToList",ExportForall "a" (ExportFun (ExportCons "Maybe" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("Data.Tuple.curry",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "c")) (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))))))),("Data.Tuple.swap",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportCons "Pair" [ExportVar "b",ExportVar "a"])))),("Data.Tuple.uncurry",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))) (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "c")))))),("GHC.Char.chr",ExportFun (ExportCons "Int" []) (ExportCons "Char" [])),("GHC.Char.eqChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "Char" []) (ExportCons "Bool" []))),("GHC.Char.neChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "Char" []) (ExportCons "Bool" []))),("GHC.List.all",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" [])))),("GHC.List.and",ExportFun (ExportCons "List" [ExportCons "Bool" []]) (ExportCons "Bool" [])),("GHC.List.break",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])))),("GHC.List.concat",ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "List" [ExportVar "a"]]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.concatMap",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "b"])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("GHC.List.drop",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.elem",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" []))))),("GHC.List.filter",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.foldl",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "b")))))),("GHC.List.foldr",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportVar "b")))))),("GHC.List.iterate",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "a")) (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"])))),("GHC.List.length",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Int" []))),("GHC.List.lookup",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Eq" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]) (ExportCons "Maybe" [ExportVar "b"])))))),("GHC.List.map",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportVar "b")) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"]))))),("GHC.List.null",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Bool" []))),("GHC.List.or",ExportFun (ExportCons "List" [ExportCons "Bool" []]) (ExportCons "Bool" [])),("GHC.List.replicate",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportVar "a") (ExportCons "List" [ExportVar "a"])))),("GHC.List.reverse",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"]))),("GHC.List.scanl",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "b") (ExportFun (ExportVar "a") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"])))))),("GHC.List.scanr",ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "b"))) (ExportFun (ExportVar "b") (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "b"])))))),("GHC.List.splitAt",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])))),("GHC.List.take",ExportForall "a" (ExportFun (ExportCons "Int" []) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.takeWhile",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportCons "Bool" [])) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportVar "a"])))),("GHC.List.uncons",ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "Maybe" [ExportCons "Pair" [ExportVar "a",ExportCons "List" [ExportVar "a"]]]))),("GHC.List.unzip",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]) (ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]])))),("GHC.List.unzip3",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportCons "Pair" [ExportCons "Pair" [ExportVar "a",ExportVar "b"],ExportVar "c"]]) (ExportCons "Pair" [ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "b"]],ExportCons "List" [ExportVar "c"]]))))),("GHC.List.zip",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]))))),("GHC.List.zip3",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportFun (ExportCons "List" [ExportVar "c"]) (ExportCons "List" [ExportCons "Pair" [ExportCons "Pair" [ExportVar "a",ExportVar "b"],ExportVar "c"]]))))))),("GHC.List.zipWith",ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportCons "List" [ExportVar "c"]))))))),("GHC.List.zipWith3",ExportForall "d" (ExportForall "c" (ExportForall "b" (ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportFun (ExportVar "c") (ExportVar "d")))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "b"]) (ExportFun (ExportCons "List" [ExportVar "c"]) (ExportCons "List" [ExportVar "d"]))))))))),("Nil",ExportForall "a" (ExportCons "List" [ExportVar "a"])),("Pair",ExportForall "b" (ExportForall "a" (ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportCons "Pair" [ExportVar "a",ExportVar "b"]))))),("Text.Show.show",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportCons "List" [ExportCons "Char" []])))),("Text.Show.showChar",ExportFun (ExportCons "Char" []) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))),("Text.Show.showList",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showListWith",ExportForall "a" (ExportFun (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))) (ExportFun (ExportCons "List" [ExportVar "a"]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showParen",ExportFun (ExportCons "Bool" []) (ExportFun (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []])) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []])))),("Text.Show.showString",ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))),("Text.Show.shows",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []]))))),("Text.Show.showsPrec",ExportForall "a" (ExportFun (ExportCons "@@hplusTC@@Show" [ExportVar "a"]) (ExportFun (ExportCons "Int" []) (ExportFun (ExportVar "a") (ExportFun (ExportCons "List" [ExportCons "Char" []]) (ExportCons "List" [ExportCons "Char" []])))))),("fst",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "a")))),("snd",ExportForall "b" (ExportForall "a" (ExportFun (ExportCons "Pair" [ExportVar "a",ExportVar "b"]) (ExportVar "b"))))]|]