{-# LANGUAGE OverloadedStrings #-}

module Application.TermSearch.Dataset where

import           Data.ECTA
import           Data.Map                       ( Map )
import           Data.Text                      ( Text )

import           Application.TermSearch.Type
import           Application.TermSearch.Utils


typeToFta :: TypeSkeleton -> Node
typeToFta (TVar "a"  ) = var1
typeToFta (TVar "b"  ) = var2
typeToFta (TVar "c"  ) = var3
typeToFta (TVar "d"  ) = var4
typeToFta (TVar "acc") = varAcc
typeToFta (TVar v) =
  error
    $ "Current implementation only supports function signatures with type variables a, b, c, d, and acc, but got "
    ++ show v
typeToFta (TFun  t1    t2      ) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons "Fun" [t1, t2]) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons s     ts      ) = mkDatatype s (map typeToFta ts)

speciallyTreatedFunctions :: [Text]
speciallyTreatedFunctions =
  [ -- `($)` is hardcoded to only be in argument position
    "(Data.Function.$)"
  ,
    -- `id` is almost entirely useless, but clogs up the graph. Currently banned
    "Data.Function.id"
  ]

hooglePlusComponents :: [(Text, TypeSkeleton)]
hooglePlusComponents =
  [ ( "(Data.Bool.&&)"
    , TFun (TCons "Bool" []) (TFun (TCons "Bool" []) (TCons "Bool" []))
    )
  , ( "(Data.Bool.||)"
    , TFun (TCons "Bool" []) (TFun (TCons "Bool" []) (TCons "Bool" []))
    )
  , ( "(Data.Eq./=)"
    , TFun (TCons "@@hplusTC@@Eq" [TVar "a"])
           (TFun (TVar "a") (TFun (TVar "a") (TCons "Bool" [])))
    )
  , ( "(Data.Eq.==)"
    , TFun (TCons "@@hplusTC@@Eq" [TVar "a"])
           (TFun (TVar "a") (TFun (TVar "a") (TCons "Bool" [])))
    )
  , ( "(Data.Function.$)"
    , TFun (TFun (TVar "a") (TVar "b")) (TFun (TVar "a") (TVar "b"))
    )
  , ( "(GHC.List.!!)"
    , TFun (TCons "List" [TVar "a"]) (TFun (TCons "Int" []) (TVar "a"))
    )
  , ( "(GHC.List.++)"
    , TFun (TCons "List" [TVar "a"])
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ("@@hplusTCInstance@@0EqBool"  , TCons "@@hplusTC@@Eq" [TCons "Bool" []])
  , ("@@hplusTCInstance@@0EqChar"  , TCons "@@hplusTC@@Eq" [TCons "Char" []])
  , ("@@hplusTCInstance@@0EqDouble", TCons "@@hplusTC@@Eq" [TCons "Double" []])
  , ("@@hplusTCInstance@@0EqFloat" , TCons "@@hplusTC@@Eq" [TCons "Float" []])
  , ("@@hplusTCInstance@@0EqInt"   , TCons "@@hplusTC@@Eq" [TCons "Int" []])
  , ("@@hplusTCInstance@@0EqUnit"  , TCons "@@hplusTC@@Eq" [TCons "Unit" []])
  , ( "@@hplusTCInstance@@0IsString"
    , TCons "@@hplusTC@@IsString" [TCons "Builder" []]
    )
  , ( "@@hplusTCInstance@@0NumDouble"
    , TCons "@@hplusTC@@Num" [TCons "Double" []]
    )
  , ("@@hplusTCInstance@@0NumFloat", TCons "@@hplusTC@@Num" [TCons "Float" []])
  , ("@@hplusTCInstance@@0NumInt"  , TCons "@@hplusTC@@Num" [TCons "Int" []])
  , ("@@hplusTCInstance@@0OrdBool" , TCons "@@hplusTC@@Ord" [TCons "Bool" []])
  , ("@@hplusTCInstance@@0OrdChar" , TCons "@@hplusTC@@Ord" [TCons "Char" []])
  , ( "@@hplusTCInstance@@0OrdDouble"
    , TCons "@@hplusTC@@Ord" [TCons "Double" []]
    )
  , ("@@hplusTCInstance@@0OrdFloat", TCons "@@hplusTC@@Ord" [TCons "Float" []])
  , ("@@hplusTCInstance@@0OrdInt"  , TCons "@@hplusTC@@Ord" [TCons "Int" []])
  , ("@@hplusTCInstance@@0ShowBool", TCons "@@hplusTC@@Show" [TCons "Bool" []])
  , ("@@hplusTCInstance@@0ShowChar", TCons "@@hplusTC@@Show" [TCons "Char" []])
  , ( "@@hplusTCInstance@@0ShowDouble"
    , TCons "@@hplusTC@@Show" [TCons "Double" []]
    )
  , ( "@@hplusTCInstance@@0ShowFloat"
    , TCons "@@hplusTC@@Show" [TCons "Float" []]
    )
  , ("@@hplusTCInstance@@0ShowInt" , TCons "@@hplusTC@@Show" [TCons "Int" []])
  , ("@@hplusTCInstance@@0ShowUnit", TCons "@@hplusTC@@Show" [TCons "Unit" []])
  , ( "@@hplusTCInstance@@1Show"
    , TFun
      (TCons "@@hplusTC@@Show" [TVar "a"])
      (TFun (TCons "@@hplusTC@@Show" [TVar "b"])
            (TCons "@@hplusTC@@Show" [TCons "Either" [TVar "a", TVar "b"]])
      )
    )
  , ( "@@hplusTCInstance@@2Read"
    , TFun
      (TCons "@@hplusTC@@Read" [TVar "a"])
      (TFun (TCons "@@hplusTC@@Read" [TVar "b"])
            (TCons "@@hplusTC@@Read" [TCons "Either" [TVar "a", TVar "b"]])
      )
    )
  , ( "@@hplusTCInstance@@3Ord"
    , TFun
      (TCons "@@hplusTC@@Ord" [TVar "a"])
      (TFun (TCons "@@hplusTC@@Ord" [TVar "b"])
            (TCons "@@hplusTC@@Ord" [TCons "Either" [TVar "a", TVar "b"]])
      )
    )
  , ( "@@hplusTCInstance@@4Eq"
    , TFun
      (TCons "@@hplusTC@@Eq" [TVar "a"])
      (TFun (TCons "@@hplusTC@@Eq" [TVar "b"])
            (TCons "@@hplusTC@@Eq" [TCons "Either" [TVar "a", TVar "b"]])
      )
    )
  , ( "@@hplusTCInstance@@6Semigroup"
    , TCons "@@hplusTC@@Semigroup" [TCons "Either" [TVar "a", TVar "b"]]
    )
  , ( "@@hplusTCInstance@@9Eq"
    , TFun (TCons "@@hplusTC@@Eq" [TVar "a"])
           (TCons "@@hplusTC@@Eq" [TCons "List" [TVar "a"]])
    )
  , ( "Cons"
    , TFun (TVar "a") (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ("Data.Bool.False", TCons "Bool" [])
  , ("Data.Bool.True" , TCons "Bool" [])
  , ( "Data.Bool.bool"
    , TFun (TVar "a") (TFun (TVar "a") (TFun (TCons "Bool" []) (TVar "a")))
    )
  , ("Data.Bool.not"      , TFun (TCons "Bool" []) (TCons "Bool" []))
  , ("Data.Bool.otherwise", TCons "Bool" [])
  , ( "Data.ByteString.Builder.byteString"
    , TFun (TCons "ByteString" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.byteStringHex"
    , TFun (TCons "ByteString" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.char7"
    , TFun (TCons "Char" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.char8"
    , TFun (TCons "Char" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.charUtf8"
    , TFun (TCons "Char" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.doubleBE"
    , TFun (TCons "Double" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.doubleDec"
    , TFun (TCons "Double" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.doubleHexFixed"
    , TFun (TCons "Double" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.doubleLE"
    , TFun (TCons "Double" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.floatBE"
    , TFun (TCons "Float" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.floatDec"
    , TFun (TCons "Float" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.floatHexFixed"
    , TFun (TCons "Float" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.floatLE"
    , TFun (TCons "Float" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.hPutBuilder"
    , TFun (TCons "Handle" [])
           (TFun (TCons "Builder" []) (TCons "IO" [TCons "Unit" []]))
    )
  , ( "Data.ByteString.Builder.int16BE"
    , TFun (TCons "Int16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int16Dec"
    , TFun (TCons "Int16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int16HexFixed"
    , TFun (TCons "Int16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int16LE"
    , TFun (TCons "Int16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int32BE"
    , TFun (TCons "Int32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int32Dec"
    , TFun (TCons "Int32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int32HexFixed"
    , TFun (TCons "Int32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int32LE"
    , TFun (TCons "Int32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int64BE"
    , TFun (TCons "Int64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int64Dec"
    , TFun (TCons "Int64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int64HexFixed"
    , TFun (TCons "Int64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int64LE"
    , TFun (TCons "Int64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int8"
    , TFun (TCons "Int8" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int8Dec"
    , TFun (TCons "Int8" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.int8HexFixed"
    , TFun (TCons "Int8" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.intDec"
    , TFun (TCons "Int" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.integerDec"
    , TFun (TCons "Integer" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.lazyByteString"
    , TFun (TCons "ByteString" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.lazyByteStringHex"
    , TFun (TCons "ByteString" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.shortByteString"
    , TFun (TCons "ShortByteString" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.string7"
    , TFun (TCons "List" [TCons "Char" []]) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.string8"
    , TFun (TCons "List" [TCons "Char" []]) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.stringUtf8"
    , TFun (TCons "List" [TCons "Char" []]) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.toLazyByteString"
    , TFun (TCons "Builder" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Builder.word16BE"
    , TFun (TCons "Word16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word16Dec"
    , TFun (TCons "Word16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word16Hex"
    , TFun (TCons "Word16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word16HexFixed"
    , TFun (TCons "Word16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word16LE"
    , TFun (TCons "Word16" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word32BE"
    , TFun (TCons "Word32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word32Dec"
    , TFun (TCons "Word32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word32Hex"
    , TFun (TCons "Word32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word32HexFixed"
    , TFun (TCons "Word32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word32LE"
    , TFun (TCons "Word32" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word64BE"
    , TFun (TCons "Word64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word64Dec"
    , TFun (TCons "Word64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word64Hex"
    , TFun (TCons "Word64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word64HexFixed"
    , TFun (TCons "Word64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word64LE"
    , TFun (TCons "Word64" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word8"
    , TFun (TCons "Word8" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word8Dec"
    , TFun (TCons "Word8" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word8Hex"
    , TFun (TCons "Word8" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.word8HexFixed"
    , TFun (TCons "Word8" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.wordDec"
    , TFun (TCons "Word" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Builder.wordHex"
    , TFun (TCons "Word" []) (TCons "Builder" [])
    )
  , ( "Data.ByteString.Lazy.all"
    , TFun (TFun (TCons "Word8" []) (TCons "Bool" []))
           (TFun (TCons "ByteString" []) (TCons "Bool" []))
    )
  , ( "Data.ByteString.Lazy.any"
    , TFun (TFun (TCons "Word8" []) (TCons "Bool" []))
           (TFun (TCons "ByteString" []) (TCons "Bool" []))
    )
  , ( "Data.ByteString.Lazy.append"
    , TFun (TCons "ByteString" [])
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.appendFile"
    , TFun (TCons "List" [TCons "Char" []])
           (TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []]))
    )
  , ( "Data.ByteString.Lazy.break"
    , TFun
      (TFun (TCons "Word8" []) (TCons "Bool" []))
      (TFun (TCons "ByteString" [])
            (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
      )
    )
  , ( "Data.ByteString.Lazy.concat"
    , TFun (TCons "List" [TCons "ByteString" []]) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.concatMap"
    , TFun (TFun (TCons "Word8" []) (TCons "ByteString" []))
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.cons"
    , TFun (TCons "Word8" [])
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.cons'"
    , TFun (TCons "Word8" [])
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.copy"
    , TFun (TCons "ByteString" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.count"
    , TFun (TCons "Word8" []) (TFun (TCons "ByteString" []) (TCons "Int64" []))
    )
  , ( "Data.ByteString.Lazy.cycle"
    , TFun (TCons "ByteString" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.drop"
    , TFun (TCons "Int64" [])
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.dropWhile"
    , TFun (TFun (TCons "Word8" []) (TCons "Bool" []))
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.elem"
    , TFun (TCons "Word8" []) (TFun (TCons "ByteString" []) (TCons "Bool" []))
    )
  , ( "Data.ByteString.Lazy.elemIndex"
    , TFun (TCons "Word8" [])
           (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "Int64" []]))
    )
  , ( "Data.ByteString.Lazy.elemIndexEnd"
    , TFun (TCons "Word8" [])
           (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "Int64" []]))
    )
  , ( "Data.ByteString.Lazy.elemIndices"
    , TFun (TCons "Word8" [])
           (TFun (TCons "ByteString" []) (TCons "List" [TCons "Int64" []]))
    )
  , ("Data.ByteString.Lazy.empty", TCons "ByteString" [])
  , ( "Data.ByteString.Lazy.filter"
    , TFun (TFun (TCons "Word8" []) (TCons "Bool" []))
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.find"
    , TFun (TFun (TCons "Word8" []) (TCons "Bool" []))
           (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "Word8" []]))
    )
  , ( "Data.ByteString.Lazy.findIndex"
    , TFun (TFun (TCons "Word8" []) (TCons "Bool" []))
           (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "Int64" []]))
    )
  , ( "Data.ByteString.Lazy.findIndices"
    , TFun (TFun (TCons "Word8" []) (TCons "Bool" []))
           (TFun (TCons "ByteString" []) (TCons "List" [TCons "Int64" []]))
    )
  , ( "Data.ByteString.Lazy.foldl"
    , TFun (TFun (TVar "a") (TFun (TCons "Word8" []) (TVar "a")))
           (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
    )
  , ( "Data.ByteString.Lazy.foldl'"
    , TFun (TFun (TVar "a") (TFun (TCons "Word8" []) (TVar "a")))
           (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
    )
  , ( "Data.ByteString.Lazy.foldl1"
    , TFun
      (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Word8" [])))
      (TFun (TCons "ByteString" []) (TCons "Word8" []))
    )
  , ( "Data.ByteString.Lazy.foldl1'"
    , TFun
      (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Word8" [])))
      (TFun (TCons "ByteString" []) (TCons "Word8" []))
    )
  , ( "Data.ByteString.Lazy.foldlChunks"
    , TFun (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
           (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
    )
  , ( "Data.ByteString.Lazy.foldr"
    , TFun (TFun (TCons "Word8" []) (TFun (TVar "a") (TVar "a")))
           (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
    )
  , ( "Data.ByteString.Lazy.foldr1"
    , TFun
      (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Word8" [])))
      (TFun (TCons "ByteString" []) (TCons "Word8" []))
    )
  , ( "Data.ByteString.Lazy.foldrChunks"
    , TFun (TFun (TCons "ByteString" []) (TFun (TVar "a") (TVar "a")))
           (TFun (TVar "a") (TFun (TCons "ByteString" []) (TVar "a")))
    )
  , ( "Data.ByteString.Lazy.fromChunks"
    , TFun (TCons "List" [TCons "ByteString" []]) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.fromStrict"
    , TFun (TCons "ByteString" []) (TCons "ByteString" [])
    )
  , ("Data.ByteString.Lazy.getContents", TCons "IO" [TCons "ByteString" []])
  , ( "Data.ByteString.Lazy.group"
    , TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []])
    )
  , ( "Data.ByteString.Lazy.groupBy"
    , TFun
      (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Bool" [])))
      (TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []]))
    )
  , ( "Data.ByteString.Lazy.hGet"
    , TFun (TCons "Handle" [])
           (TFun (TCons "Int" []) (TCons "IO" [TCons "ByteString" []]))
    )
  , ( "Data.ByteString.Lazy.hGetContents"
    , TFun (TCons "Handle" []) (TCons "IO" [TCons "ByteString" []])
    )
  , ( "Data.ByteString.Lazy.hGetNonBlocking"
    , TFun (TCons "Handle" [])
           (TFun (TCons "Int" []) (TCons "IO" [TCons "ByteString" []]))
    )
  , ( "Data.ByteString.Lazy.hPut"
    , TFun (TCons "Handle" [])
           (TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []]))
    )
  , ( "Data.ByteString.Lazy.hPutNonBlocking"
    , TFun (TCons "Handle" [])
           (TFun (TCons "ByteString" []) (TCons "IO" [TCons "ByteString" []]))
    )
  , ( "Data.ByteString.Lazy.hPutStr"
    , TFun (TCons "Handle" [])
           (TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []]))
    )
  , ( "Data.ByteString.Lazy.head"
    , TFun (TCons "ByteString" []) (TCons "Word8" [])
    )
  , ( "Data.ByteString.Lazy.index"
    , TFun (TCons "ByteString" []) (TFun (TCons "Int64" []) (TCons "Word8" []))
    )
  , ( "Data.ByteString.Lazy.init"
    , TFun (TCons "ByteString" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.inits"
    , TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []])
    )
  , ( "Data.ByteString.Lazy.interact"
    , TFun (TFun (TCons "ByteString" []) (TCons "ByteString" []))
           (TCons "IO" [TCons "Unit" []])
    )
  , ( "Data.ByteString.Lazy.intercalate"
    , TFun
      (TCons "ByteString" [])
      (TFun (TCons "List" [TCons "ByteString" []]) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.intersperse"
    , TFun (TCons "Word8" [])
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.isPrefixOf"
    , TFun (TCons "ByteString" [])
           (TFun (TCons "ByteString" []) (TCons "Bool" []))
    )
  , ( "Data.ByteString.Lazy.isSuffixOf"
    , TFun (TCons "ByteString" [])
           (TFun (TCons "ByteString" []) (TCons "Bool" []))
    )
  , ( "Data.ByteString.Lazy.iterate"
    , TFun (TFun (TCons "Word8" []) (TCons "Word8" []))
           (TFun (TCons "Word8" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.last"
    , TFun (TCons "ByteString" []) (TCons "Word8" [])
    )
  , ( "Data.ByteString.Lazy.length"
    , TFun (TCons "ByteString" []) (TCons "Int64" [])
    )
  , ( "Data.ByteString.Lazy.map"
    , TFun (TFun (TCons "Word8" []) (TCons "Word8" []))
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.mapAccumL"
    , TFun
      (TFun
        (TVar "acc")
        (TFun (TCons "Word8" []) (TCons "Pair" [TVar "acc", TCons "Word8" []]))
      )
      (TFun
        (TVar "acc")
        (TFun (TCons "ByteString" [])
              (TCons "Pair" [TVar "acc", TCons "ByteString" []])
        )
      )
    )
  , ( "Data.ByteString.Lazy.mapAccumR"
    , TFun
      (TFun
        (TVar "acc")
        (TFun (TCons "Word8" []) (TCons "Pair" [TVar "acc", TCons "Word8" []]))
      )
      (TFun
        (TVar "acc")
        (TFun (TCons "ByteString" [])
              (TCons "Pair" [TVar "acc", TCons "ByteString" []])
        )
      )
    )
  , ( "Data.ByteString.Lazy.maximum"
    , TFun (TCons "ByteString" []) (TCons "Word8" [])
    )
  , ( "Data.ByteString.Lazy.minimum"
    , TFun (TCons "ByteString" []) (TCons "Word8" [])
    )
  , ( "Data.ByteString.Lazy.notElem"
    , TFun (TCons "Word8" []) (TFun (TCons "ByteString" []) (TCons "Bool" []))
    )
  , ( "Data.ByteString.Lazy.null"
    , TFun (TCons "ByteString" []) (TCons "Bool" [])
    )
  , ( "Data.ByteString.Lazy.pack"
    , TFun (TCons "List" [TCons "Word8" []]) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.partition"
    , TFun
      (TFun (TCons "Word8" []) (TCons "Bool" []))
      (TFun (TCons "ByteString" [])
            (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
      )
    )
  , ( "Data.ByteString.Lazy.putStr"
    , TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []])
    )
  , ( "Data.ByteString.Lazy.putStrLn"
    , TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []])
    )
  , ( "Data.ByteString.Lazy.readFile"
    , TFun (TCons "List" [TCons "Char" []]) (TCons "IO" [TCons "ByteString" []])
    )
  , ( "Data.ByteString.Lazy.repeat"
    , TFun (TCons "Word8" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.replicate"
    , TFun (TCons "Int64" []) (TFun (TCons "Word8" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.reverse"
    , TFun (TCons "ByteString" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.scanl"
    , TFun
      (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TCons "Word8" [])))
      (TFun (TCons "Word8" [])
            (TFun (TCons "ByteString" []) (TCons "ByteString" []))
      )
    )
  , ( "Data.ByteString.Lazy.singleton"
    , TFun (TCons "Word8" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.snoc"
    , TFun (TCons "ByteString" [])
           (TFun (TCons "Word8" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.span"
    , TFun
      (TFun (TCons "Word8" []) (TCons "Bool" []))
      (TFun (TCons "ByteString" [])
            (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
      )
    )
  , ( "Data.ByteString.Lazy.split"
    , TFun
      (TCons "Word8" [])
      (TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []]))
    )
  , ( "Data.ByteString.Lazy.splitAt"
    , TFun
      (TCons "Int64" [])
      (TFun (TCons "ByteString" [])
            (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
      )
    )
  , ( "Data.ByteString.Lazy.splitWith"
    , TFun
      (TFun (TCons "Word8" []) (TCons "Bool" []))
      (TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []]))
    )
  , ( "Data.ByteString.Lazy.stripPrefix"
    , TFun
      (TCons "ByteString" [])
      (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "ByteString" []]))
    )
  , ( "Data.ByteString.Lazy.stripSuffix"
    , TFun
      (TCons "ByteString" [])
      (TFun (TCons "ByteString" []) (TCons "Maybe" [TCons "ByteString" []]))
    )
  , ( "Data.ByteString.Lazy.tail"
    , TFun (TCons "ByteString" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.tails"
    , TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []])
    )
  , ( "Data.ByteString.Lazy.take"
    , TFun (TCons "Int64" [])
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.takeWhile"
    , TFun (TFun (TCons "Word8" []) (TCons "Bool" []))
           (TFun (TCons "ByteString" []) (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.toChunks"
    , TFun (TCons "ByteString" []) (TCons "List" [TCons "ByteString" []])
    )
  , ( "Data.ByteString.Lazy.toStrict"
    , TFun (TCons "ByteString" []) (TCons "ByteString" [])
    )
  , ( "Data.ByteString.Lazy.transpose"
    , TFun (TCons "List" [TCons "ByteString" []])
           (TCons "List" [TCons "ByteString" []])
    )
  , ( "Data.ByteString.Lazy.uncons"
    , TFun
      (TCons "ByteString" [])
      (TCons "Maybe" [TCons "Pair" [TCons "Word8" [], TCons "ByteString" []]])
    )
  , ( "Data.ByteString.Lazy.unfoldr"
    , TFun
      (TFun (TVar "a")
            (TCons "Maybe" [TCons "Pair" [TCons "Word8" [], TVar "a"]])
      )
      (TFun (TVar "a") (TCons "ByteString" []))
    )
  , ( "Data.ByteString.Lazy.unpack"
    , TFun (TCons "ByteString" []) (TCons "List" [TCons "Word8" []])
    )
  , ( "Data.ByteString.Lazy.unsnoc"
    , TFun
      (TCons "ByteString" [])
      (TCons "Maybe" [TCons "Pair" [TCons "ByteString" [], TCons "Word8" []]])
    )
  , ( "Data.ByteString.Lazy.unzip"
    , TFun (TCons "List" [TCons "Pair" [TCons "Word8" [], TCons "Word8" []]])
           (TCons "Pair" [TCons "ByteString" [], TCons "ByteString" []])
    )
  , ( "Data.ByteString.Lazy.writeFile"
    , TFun (TCons "List" [TCons "Char" []])
           (TFun (TCons "ByteString" []) (TCons "IO" [TCons "Unit" []]))
    )
  , ( "Data.ByteString.Lazy.zip"
    , TFun
      (TCons "ByteString" [])
      (TFun (TCons "ByteString" [])
            (TCons "List" [TCons "Pair" [TCons "Word8" [], TCons "Word8" []]])
      )
    )
  , ( "Data.ByteString.Lazy.zipWith"
    , TFun
      (TFun (TCons "Word8" []) (TFun (TCons "Word8" []) (TVar "a")))
      (TFun (TCons "ByteString" [])
            (TFun (TCons "ByteString" []) (TCons "List" [TVar "a"]))
      )
    )
  , ("Data.Either.Left" , TFun (TVar "a") (TCons "Either" [TVar "a", TVar "b"]))
  , ("Data.Either.Right", TFun (TVar "b") (TCons "Either" [TVar "a", TVar "b"]))
  , ( "Data.Either.either"
    , TFun
      (TFun (TVar "a") (TVar "c"))
      (TFun (TFun (TVar "b") (TVar "c"))
            (TFun (TCons "Either" [TVar "a", TVar "b"]) (TVar "c"))
      )
    )
  , ( "Data.Either.fromLeft"
    , TFun (TVar "a") (TFun (TCons "Either" [TVar "a", TVar "b"]) (TVar "a"))
    )
  , ( "Data.Either.fromRight"
    , TFun (TVar "b") (TFun (TCons "Either" [TVar "a", TVar "b"]) (TVar "b"))
    )
  , ( "Data.Either.isLeft"
    , TFun (TCons "Either" [TVar "a", TVar "b"]) (TCons "Bool" [])
    )
  , ( "Data.Either.isRight"
    , TFun (TCons "Either" [TVar "a", TVar "b"]) (TCons "Bool" [])
    )
  , ( "Data.Either.lefts"
    , TFun (TCons "List" [TCons "Either" [TVar "a", TVar "b"]])
           (TCons "List" [TVar "a"])
    )
  , ( "Data.Either.partitionEithers"
    , TFun (TCons "List" [TCons "Either" [TVar "a", TVar "b"]])
           (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "b"]])
    )
  , ( "Data.Either.rights"
    , TFun (TCons "List" [TCons "Either" [TVar "a", TVar "b"]])
           (TCons "List" [TVar "b"])
    )
  , ( "Data.List.group"
    , TFun
      (TCons "@@hplusTC@@Eq" [TVar "a"])
      (TFun (TCons "List" [TVar "a"]) (TCons "List" [TCons "List" [TVar "a"]]))
    )
  , ("Data.Maybe.Just"   , TFun (TVar "a") (TCons "Maybe" [TVar "a"]))
  , ("Data.Maybe.Nothing", TCons "Maybe" [TVar "a"])
  , ( "Data.Maybe.catMaybes"
    , TFun (TCons "List" [TCons "Maybe" [TVar "a"]]) (TCons "List" [TVar "a"])
    )
  , ("Data.Maybe.fromJust", TFun (TCons "Maybe" [TVar "a"]) (TVar "a"))
  , ( "Data.Maybe.fromMaybe"
    , TFun (TVar "a") (TFun (TCons "Maybe" [TVar "a"]) (TVar "a"))
    )
  , ("Data.Maybe.isJust"   , TFun (TCons "Maybe" [TVar "a"]) (TCons "Bool" []))
  , ("Data.Maybe.isNothing", TFun (TCons "Maybe" [TVar "a"]) (TCons "Bool" []))
  , ( "Data.Maybe.listToMaybe"
    , TFun (TCons "List" [TVar "a"]) (TCons "Maybe" [TVar "a"])
    )
  , ( "Data.Maybe.mapMaybe"
    , TFun (TFun (TVar "a") (TCons "Maybe" [TVar "b"]))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
    )
  , ( "Data.Maybe.maybe"
    , TFun
      (TVar "b")
      (TFun (TFun (TVar "a") (TVar "b"))
            (TFun (TCons "Maybe" [TVar "a"]) (TVar "b"))
      )
    )
  , ( "Data.Maybe.maybeToList"
    , TFun (TCons "Maybe" [TVar "a"]) (TCons "List" [TVar "a"])
    )
  , ( "Data.Tuple.curry"
    , TFun (TFun (TCons "Pair" [TVar "a", TVar "b"]) (TVar "c"))
           (TFun (TVar "a") (TFun (TVar "b") (TVar "c")))
    )
  , ("Data.Tuple.fst", TFun (TCons "Pair" [TVar "a", TVar "b"]) (TVar "a"))
  , ("Data.Tuple.snd", TFun (TCons "Pair" [TVar "a", TVar "b"]) (TVar "b"))
  , ( "Data.Tuple.swap"
    , TFun (TCons "Pair" [TVar "a", TVar "b"])
           (TCons "Pair" [TVar "b", TVar "a"])
    )
  , ( "Data.Tuple.uncurry"
    , TFun (TFun (TVar "a") (TFun (TVar "b") (TVar "c")))
           (TFun (TCons "Pair" [TVar "a", TVar "b"]) (TVar "c"))
    )
  , ("GHC.Char.chr", TFun (TCons "Int" []) (TCons "Char" []))
  , ( "GHC.Char.eqChar"
    , TFun (TCons "Char" []) (TFun (TCons "Char" []) (TCons "Bool" []))
    )
  , ( "GHC.Char.neChar"
    , TFun (TCons "Char" []) (TFun (TCons "Char" []) (TCons "Bool" []))
    )
  , ( "GHC.List.all"
    , TFun (TFun (TVar "a") (TCons "Bool" []))
           (TFun (TCons "List" [TVar "a"]) (TCons "Bool" []))
    )
  , ("GHC.List.and", TFun (TCons "List" [TCons "Bool" []]) (TCons "Bool" []))
  , ( "GHC.List.any"
    , TFun (TFun (TVar "a") (TCons "Bool" []))
           (TFun (TCons "List" [TVar "a"]) (TCons "Bool" []))
    )
  , ( "GHC.List.break"
    , TFun
      (TFun (TVar "a") (TCons "Bool" []))
      (TFun (TCons "List" [TVar "a"])
            (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
      )
    )
  , ( "GHC.List.concat"
    , TFun (TCons "List" [TCons "List" [TVar "a"]]) (TCons "List" [TVar "a"])
    )
  , ( "GHC.List.concatMap"
    , TFun (TFun (TVar "a") (TCons "List" [TVar "b"]))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
    )
  , ("GHC.List.cycle", TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
  , ( "GHC.List.drop"
    , TFun (TCons "Int" [])
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.dropWhile"
    , TFun (TFun (TVar "a") (TCons "Bool" []))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.elem"
    , TFun
      (TCons "@@hplusTC@@Eq" [TVar "a"])
      (TFun (TVar "a") (TFun (TCons "List" [TVar "a"]) (TCons "Bool" [])))
    )
  , ( "GHC.List.filter"
    , TFun (TFun (TVar "a") (TCons "Bool" []))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.foldl"
    , TFun (TFun (TVar "b") (TFun (TVar "a") (TVar "b")))
           (TFun (TVar "b") (TFun (TCons "List" [TVar "a"]) (TVar "b")))
    )
  , ( "GHC.List.foldl'"
    , TFun (TFun (TVar "b") (TFun (TVar "a") (TVar "b")))
           (TFun (TVar "b") (TFun (TCons "List" [TVar "a"]) (TVar "b")))
    )
  , ( "GHC.List.foldl1"
    , TFun (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
           (TFun (TCons "List" [TVar "a"]) (TVar "a"))
    )
  , ( "GHC.List.foldl1'"
    , TFun (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
           (TFun (TCons "List" [TVar "a"]) (TVar "a"))
    )
  , ( "GHC.List.foldr"
    , TFun (TFun (TVar "a") (TFun (TVar "b") (TVar "b")))
           (TFun (TVar "b") (TFun (TCons "List" [TVar "a"]) (TVar "b")))
    )
  , ( "GHC.List.foldr1"
    , TFun (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
           (TFun (TCons "List" [TVar "a"]) (TVar "a"))
    )
  , ("GHC.List.head", TFun (TCons "List" [TVar "a"]) (TVar "a"))
  , ("GHC.List.init", TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
  , ( "GHC.List.iterate"
    , TFun (TFun (TVar "a") (TVar "a"))
           (TFun (TVar "a") (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.iterate'"
    , TFun (TFun (TVar "a") (TVar "a"))
           (TFun (TVar "a") (TCons "List" [TVar "a"]))
    )
  , ("GHC.List.last"  , TFun (TCons "List" [TVar "a"]) (TVar "a"))
  , ("GHC.List.length", TFun (TCons "List" [TVar "a"]) (TCons "Int" []))
  , ( "GHC.List.lookup"
    , TFun
      (TCons "@@hplusTC@@Eq" [TVar "a"])
      (TFun
        (TVar "a")
        (TFun (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
              (TCons "Maybe" [TVar "b"])
        )
      )
    )
  , ( "GHC.List.map"
    , TFun (TFun (TVar "a") (TVar "b"))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
    )
  , ( "GHC.List.maximum"
    , TFun (TCons "@@hplusTC@@Ord" [TVar "a"])
           (TFun (TCons "List" [TVar "a"]) (TVar "a"))
    )
  , ( "GHC.List.minimum"
    , TFun (TCons "@@hplusTC@@Ord" [TVar "a"])
           (TFun (TCons "List" [TVar "a"]) (TVar "a"))
    )
  , ( "GHC.List.notElem"
    , TFun
      (TCons "@@hplusTC@@Eq" [TVar "a"])
      (TFun (TVar "a") (TFun (TCons "List" [TVar "a"]) (TCons "Bool" [])))
    )
  , ("GHC.List.null", TFun (TCons "List" [TVar "a"]) (TCons "Bool" []))
  , ("GHC.List.or"  , TFun (TCons "List" [TCons "Bool" []]) (TCons "Bool" []))
  , ( "GHC.List.product"
    , TFun (TCons "@@hplusTC@@Num" [TVar "a"])
           (TFun (TCons "List" [TVar "a"]) (TVar "a"))
    )
  , ("GHC.List.repeat", TFun (TVar "a") (TCons "List" [TVar "a"]))
  , ( "GHC.List.replicate"
    , TFun (TCons "Int" []) (TFun (TVar "a") (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.reverse"
    , TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"])
    )
  , ( "GHC.List.scanl"
    , TFun
      (TFun (TVar "b") (TFun (TVar "a") (TVar "b")))
      (TFun (TVar "b")
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
      )
    )
  , ( "GHC.List.scanl'"
    , TFun
      (TFun (TVar "b") (TFun (TVar "a") (TVar "b")))
      (TFun (TVar "b")
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
      )
    )
  , ( "GHC.List.scanl1"
    , TFun (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.scanr"
    , TFun
      (TFun (TVar "a") (TFun (TVar "b") (TVar "b")))
      (TFun (TVar "b")
            (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "b"]))
      )
    )
  , ( "GHC.List.scanr1"
    , TFun (TFun (TVar "a") (TFun (TVar "a") (TVar "a")))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.span"
    , TFun
      (TFun (TVar "a") (TCons "Bool" []))
      (TFun (TCons "List" [TVar "a"])
            (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
      )
    )
  , ( "GHC.List.splitAt"
    , TFun
      (TCons "Int" [])
      (TFun (TCons "List" [TVar "a"])
            (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "a"]])
      )
    )
  , ( "GHC.List.sum"
    , TFun (TCons "@@hplusTC@@Num" [TVar "a"])
           (TFun (TCons "List" [TVar "a"]) (TVar "a"))
    )
  , ("GHC.List.tail", TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
  , ( "GHC.List.take"
    , TFun (TCons "Int" [])
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.takeWhile"
    , TFun (TFun (TVar "a") (TCons "Bool" []))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ( "GHC.List.uncons"
    , TFun (TCons "List" [TVar "a"])
           (TCons "Maybe" [TCons "Pair" [TVar "a", TCons "List" [TVar "a"]]])
    )
  , ( "GHC.List.unzip"
    , TFun (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
           (TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "b"]])
    )
  , ( "GHC.List.unzip3"
    , TFun
      (TCons "List" [TCons "Pair" [TCons "Pair" [TVar "a", TVar "b"], TVar "c"]]
      )
      (TCons
        "Pair"
        [ TCons "Pair" [TCons "List" [TVar "a"], TCons "List" [TVar "b"]]
        , TCons "List" [TVar "c"]
        ]
      )
    )
  , ( "GHC.List.zip"
    , TFun
      (TCons "List" [TVar "a"])
      (TFun (TCons "List" [TVar "b"])
            (TCons "List" [TCons "Pair" [TVar "a", TVar "b"]])
      )
    )
  , ( "GHC.List.zip3"
    , TFun
      (TCons "List" [TVar "a"])
      (TFun
        (TCons "List" [TVar "b"])
        (TFun
          (TCons "List" [TVar "c"])
          (TCons "List"
                 [TCons "Pair" [TCons "Pair" [TVar "a", TVar "b"], TVar "c"]]
          )
        )
      )
    )
  , ( "GHC.List.zipWith"
    , TFun
      (TFun (TVar "a") (TFun (TVar "b") (TVar "c")))
      (TFun (TCons "List" [TVar "a"])
            (TFun (TCons "List" [TVar "b"]) (TCons "List" [TVar "c"]))
      )
    )
  , ( "GHC.List.zipWith3"
    , TFun
      (TFun (TVar "a") (TFun (TVar "b") (TFun (TVar "c") (TVar "d"))))
      (TFun
        (TCons "List" [TVar "a"])
        (TFun (TCons "List" [TVar "b"])
              (TFun (TCons "List" [TVar "c"]) (TCons "List" [TVar "d"]))
        )
      )
    )
  , ("Nil", TCons "List" [TVar "a"])
  , ( "Pair"
    , TFun (TVar "a") (TFun (TVar "b") (TCons "Pair" [TVar "a", TVar "b"]))
    )
  , ( "Text.Show.show"
    , TFun (TCons "@@hplusTC@@Show" [TVar "a"])
           (TFun (TVar "a") (TCons "List" [TCons "Char" []]))
    )
  , ( "Text.Show.showChar"
    , TFun
      (TCons "Char" [])
      (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
    )
  , ( "Text.Show.showList"
    , TFun
      (TCons "@@hplusTC@@Show" [TVar "a"])
      (TFun
        (TCons "List" [TVar "a"])
        (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
      )
    )
  , ( "Text.Show.showListWith"
    , TFun
      (TFun
        (TVar "a")
        (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
      )
      (TFun
        (TCons "List" [TVar "a"])
        (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
      )
    )
  , ( "Text.Show.showParen"
    , TFun
      (TCons "Bool" [])
      (TFun
        (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
        (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
      )
    )
  , ( "Text.Show.showString"
    , TFun
      (TCons "List" [TCons "Char" []])
      (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
    )
  , ( "Text.Show.shows"
    , TFun
      (TCons "@@hplusTC@@Show" [TVar "a"])
      (TFun
        (TVar "a")
        (TFun (TCons "List" [TCons "Char" []]) (TCons "List" [TCons "Char" []]))
      )
    )
  , ( "Text.Show.showsPrec"
    , TFun
      (TCons "@@hplusTC@@Show" [TVar "a"])
      (TFun
        (TCons "Int" [])
        (TFun
          (TVar "a")
          (TFun (TCons "List" [TCons "Char" []])
                (TCons "List" [TCons "Char" []])
          )
        )
      )
    )
  ]

augumentedComponents :: [(Text, TypeSkeleton)]
augumentedComponents =
  [ ( "(Data.Function..)"
    , TFun (TFun (TVar "b") (TVar "c"))
           (TFun (TFun (TVar "a") (TVar "b")) (TFun (TVar "a") (TVar "c")))
    )
  , ( "(Data.Ord.<)"
    , TFun (TCons "@@hplusTC@@Ord" [TVar "a"])
           (TFun (TVar "a") (TFun (TVar "a") (TCons "Bool" [])))
    )
  , ( "Data.Ord.compare"
    , TFun (TCons "@@hplusTC@@Ord" [TVar "a"])
           (TFun (TVar "a") (TFun (TVar "a") (TCons "Ordering" [])))
    )
  , ( "Data.Function.on"
    , TFun
      (TFun (TVar "b") (TFun (TVar "b") (TVar "c")))
      (TFun (TFun (TVar "a") (TVar "b"))
            (TFun (TVar "a") (TFun (TVar "a") (TVar "c")))
      )
    )
  , ( "Data.List.groupBy"
    , TFun
      (TFun (TVar "a") (TFun (TVar "a") (TCons "Bool" [])))
      (TFun (TCons "List" [TVar "a"]) (TCons "List" [TCons "List" [TVar "a"]]))
    )
  , ( "Data.List.sortBy"
    , TFun (TFun (TVar "a") (TFun (TVar "a") (TCons "Ordering" [])))
           (TFun (TCons "List" [TVar "a"]) (TCons "List" [TVar "a"]))
    )
  , ( "Data.Function.flip"
    , TFun (TFun (TVar "a") (TFun (TVar "b") (TVar "c")))
           (TFun (TVar "b") (TFun (TVar "a") (TVar "c")))
    )
  ]

hoogleComponents :: Map TypeSkeleton Text
hoogleComponents = fst (mkGroups hooglePlusComponents)

groupMapping :: Map Text Text
groupMapping = snd (mkGroups hooglePlusComponents)

-- switch to this when you run experiments on stackoverflow benchmarks
-- hoogleComponents :: Map TypeSkeleton Text
-- hoogleComponents = fst (mkGroups $ hooglePlusComponents ++ augumentedComponents)

-- groupMapping :: Map Text Text
-- groupMapping = snd (mkGroups $ hooglePlusComponents ++ augumentedComponents)
