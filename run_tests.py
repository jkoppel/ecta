import argparse
import re
import os
import pickle
from subprocess import Popen, PIPE, STDOUT

RUN_CMD = ["stack", "exec", "--", "compact-coupled-terms-exe"]
PICKLE_FILE = "results.pkl"
CSV_FILE = "results.csv"

hoogleplus_benchmarks = {
    "appBoth": 'Benchmark "appBoth" 5 "app(app(Pair, app(f, x)), app(g, x))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("g",ExportFun (ExportVar "a") (ExportVar "c")),("x",ExportVar "a")],ExportCons "Pair" [ExportVar "b",ExportVar "c"])',
    "test": 'Benchmark "test" 5 "app(app(app(Data.Bool.bool, Data.Maybe.Nothing), app(Data.Maybe.Just, x)), b)" ([("b",ExportCons "Bool" []),("x",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"])',
    "both": 'Benchmark "both" 7 "app(app(Pair, app(f, app(Data.Tuple.fst, p))), app(f, app(Data.Tuple.snd, p)))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("p",ExportCons "Pair" [ExportVar "a",ExportVar "a"])],ExportCons "Pair" [ExportVar "b",ExportVar "b"])',
    "mapEither": 'Benchmark "mapEither" 4 "app(Data.Either.partitionEithers, app(app(GHC.List.map, f), xs))" ([("f",ExportFun (ExportVar "a") (ExportCons "Either" [ExportVar "b",ExportVar "c"])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "b"],ExportCons "List" [ExportVar "c"]])',
    "mapMaybes": 'Benchmark "mapMaybes" 4 "app(Data.Maybe.listToMaybe, app(app(Data.Maybe.mapMaybe, f), xs))" ([("f",ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "b"])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Maybe" [ExportVar "b"])',
    "mergeEither": 'Benchmark "mergeEither" 4 "app(app(app(Data.Either.either, Data.Either.Left), Data.Function.id), e)" ([("e",ExportCons "Either" [ExportVar "a",ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportVar "b"])',
    "mbToEither": 'Benchmark "mbToEither" 5 "app(app(app(Data.Maybe.maybe, app(Data.Either.Left, x)), Data.Either.Right), mb)" ([("x",ExportVar "a"),("mb",ExportCons "Maybe" [ExportVar "b"])],ExportCons "Either" [ExportVar "a",ExportVar "b"])',
    "cartProduct": 'Benchmark "cartProduct" 6 "app(app(GHC.List.map, app(GHC.List.zip, xs)), app(app(GHC.List.map, GHC.List.repeat), ys))" ([("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportVar "b"])],ExportCons "List" [ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]])',
    "multiAppPair": 'Benchmark "multiAppPair" 7 "app(app(Pair, app(app(Data.Tuple.fst, tp), x)), app(app(Data.Tuple.snd, tp), x))" ([("tp",ExportCons "Pair" [ExportFun (ExportVar "a") (ExportVar "b"),ExportFun (ExportVar "a") (ExportVar "c")]),("x",ExportVar "a")],ExportCons "Pair" [ExportVar "b",ExportVar "c"])',
    "map": 'Benchmark "map" 3 "app(app(GHC.List.map, f), xs)" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "b"])',
    "replFuncs": 'Benchmark "replFuncs" 3 "app(app(GHC.List.replicate, n), f)" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("n",ExportCons "Int" [])],ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "b")])',
    "mbAppFirst": 'Benchmark "mbAppFirst" 5 "app(app(app(Data.Maybe.maybe, x), f), app(Data.Maybe.listToMaybe, xs))" ([("x",ExportVar "b"),("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportVar "b")',
    "mapTwice": 'Benchmark "mapTwice" 5 "app(app(GHC.List.map, g), app(app(GHC.List.map, f), xs))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("g",ExportFun (ExportVar "b") (ExportVar "c")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "c"])',
    "resolveEither": 'Benchmark "resolveEither" 4 "app(app(app(Data.Either.either, f), Data.Function.id), e)" ([("e",ExportCons "Either" [ExportVar "a",ExportVar "b"]),("f",ExportFun (ExportVar "a") (ExportVar "b"))],ExportVar "b")',
    "firstJust": 'Benchmark "firstJust" 5 "app(app(Data.Maybe.fromMaybe, x), app(Data.Maybe.listToMaybe, app(Data.Maybe.catMaybes, xs)))" ([("x",ExportVar "a"),("xs",ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]])],ExportVar "a")',
    "appendN": 'Benchmark "appendN" 4 "app(GHC.List.concat, app(app(GHC.List.replicate, n), xs))" ([("n",ExportCons "Int" []),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "applyNtimes": 'Benchmark "applyNtimes" 6 "app(app(app(GHC.List.foldr, $), x), app(app(GHC.List.replicate, n), f))" ([("f",ExportFun (ExportVar "a") (ExportVar "a")),("x",ExportVar "a"),("n",ExportCons "Int" [])],ExportVar "a")',
    "dedupe": 'Benchmark "dedupe" 5 "app(app(GHC.List.map, GHC.List.head), app(app(Data.List.group, tcarg0), xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "inverseMap": 'Benchmark "inverseMap" 5 "app(app(app(GHC.List.zipWith, $), fs), app(GHC.List.repeat, x))" ([("fs",ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "b")]),("x",ExportVar "a")],ExportCons "List" [ExportVar "b"])',
    "app2": 'Benchmark "app2" 4 "app(app(f, x), app(g, x))" ([("f",ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))),("g",ExportFun (ExportVar "a") (ExportVar "b")),("x",ExportVar "a")],ExportVar "c")',
    "singletonList": 'Benchmark "singletonList" 3 "app(app(Cons, x), Nil)" ([("x",ExportVar "a")],ExportCons "List" [ExportVar "a"])',
    "headLast": 'Benchmark "headLast" 5 "app(app(Pair, app(GHC.List.head, xs)), app(GHC.List.last, xs))" ([("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportVar "a",ExportVar "a"])',
    "headRest": 'Benchmark "headRest" 3 "app(Data.Maybe.fromJust, app(GHC.List.uncons, xs))" ([("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportVar "a",ExportCons "List" [ExportVar "a"]])',
    "coundPredMatch": 'Benchmark "coundPredMatch" 4 "app(GHC.List.length, app(app(GHC.List.filter, p), xs))" ([("xs",ExportCons "List" [ExportVar "a"]),("p",ExportFun (ExportVar "a") (ExportCons "Bool" []))],ExportCons "Int" [])',
    "splitStr": 'Benchmark "splitStr" 7 "impossible" ([("str",ExportCons "List" [ExportCons "Char" []]),("c",ExportCons "Char" [])],ExportCons "List" [ExportCons "List" [ExportCons "Char" []]])',
    "splitAtFirst": 'Benchmark "splitAtFirst" 5 "app(app(GHC.List.break, app(app((Data.Eq.==), tcarg0), x)), xs)" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])',
    "hoogle01": 'Benchmark "hoogle01" 3 "app(f, app(GHC.List.head, xs))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportVar "b")',
    "firstMatch": 'Benchmark "firstMatch" 4 "app(GHC.List.head, app(app(GHC.List.filter, p), xs))" ([("xs",ExportCons "List" [ExportVar "a"]),("p",ExportFun (ExportVar "a") (ExportCons "Bool" []))],ExportVar "a")',
    "firstMaybe": 'Benchmark "firstMaybe" 3 "app(GHC.List.head, app(Data.Maybe.catMaybes, mbs))" ([("mbs",ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]])],ExportVar "a")',
    "rights": 'Benchmark "rights" 3 "app(Data.Either.Right, app(Data.Either.rights, es))" ([("es",ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportCons "List" [ExportVar "b"]])',
    "firstKey": 'Benchmark "firstKey" 3 "app(Data.Tuple.fst, app(GHC.List.head, xs))" ([("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportVar "a")',
    "firstRight": 'Benchmark "firstRight" 4 "app(Data.Either.Right, app(GHC.List.head, app(Data.Either.rights, es)))" ([("es",ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportVar "b"])',
    "maybe": 'Benchmark "maybe" 4 "app(Data.Maybe.Just, app(app(Data.Maybe.fromMaybe, x), mb))" ([("mb",ExportCons "Maybe" [ExportVar "a"]),("x",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"])',
    "app3": 'Benchmark "app3" 4 "app(app(app(f, x), z), y)" ([("f",ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportFun (ExportVar "c") (ExportVar "d")))),("x",ExportVar "a"),("y",ExportVar "c"),("z",ExportVar "b")],ExportVar "d")',
    "zipWithResult": 'Benchmark "zipWithResult" 5 "app(app(GHC.List.zip, xs), app(app(GHC.List.map, f), xs))" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])',
    "eitherTriple": 'Benchmark "eitherTriple" 5 "app(app(app(Data.Bool.bool, e2), e1), app(Data.Either.isLeft, e1))" ([("e1",ExportCons "Either" [ExportVar "a",ExportVar "b"]),("e2",ExportCons "Either" [ExportVar "a",ExportVar "b"])],ExportCons "Either" [ExportVar "a",ExportVar "b"])',
    "pipe": 'Benchmark "pipe" 4 "app(app(app(GHC.List.foldr, $), x), fs)" ([("fs",ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "a")]),("x",ExportVar "a")],ExportVar "a")',
    "lookup": 'Benchmark "lookup" 5 "app(Data.Maybe.fromJust, app(app(app(GHC.List.lookup, tcarg0), k), xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]),("k",ExportVar "a")],ExportVar "b")',
    "mbElem": 'Benchmark "mbElem" 6 "app(Data.Maybe.listToMaybe, app(app(GHC.List.filter, app(app((Data.Eq.==), tcarg0), x)), xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Maybe" [ExportVar "a"])',
    "areEq": 'Benchmark "areEq" 7 "app(Data.Maybe.listToMaybe, app(app(GHC.List.filter, app(app((Data.Eq.==), tcarg0), x)), app(GHC.List.repeat, y)))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("y",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"])',
    "applyPair": 'Benchmark "applyPair" 4 "app(app(Data.Tuple.fst, p), app(Data.Tuple.snd, p))" ([("p",ExportCons "Pair" [ExportFun (ExportVar "a") (ExportVar "b"),ExportVar "a"])],ExportVar "b")',
    "flatten": 'Benchmark "flatten" 3 "app(GHC.List.concat, app(GHC.List.concat, xss))" ([("xss",ExportCons "List" [ExportCons "List" [ExportCons "List" [ExportVar "a"]]])],ExportCons "List" [ExportVar "a"])',
    "takeNdropM": 'Benchmark "takeNdropM" 7 "app(app(Pair, app(app(GHC.List.take, n), xs)), app(app(GHC.List.drop, m), xs))" ([("n",ExportCons "Int" []),("m",ExportCons "Int" []),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])',
    "indexesOf": 'Benchmark "indexesOf" 6 "app(app(GHC.List.map, Data.Tuple.snd), app(f, app(app(GHC.List.zip, xs), ys)))" ([("f",ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportCons "Int" []]]) (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportCons "Int" []]])),("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportCons "Int" []])],ExportCons "List" [ExportCons "Int" []])',
    "containsEdge": 'Benchmark "containsEdge" 9 "app(app((Data.Bool.&&), app(app(GHC.List.elem, app(Data.Tuple.fst, edge)), vs)), app(app(GHC.List.elem, app(Data.Tuple.snd, edge)), vs))" ([("vs",ExportCons "List" [ExportCons "Int" []]),("edge",ExportCons "Pair" [ExportCons "Int" [],ExportCons "Int" []])],ExportCons "Bool" [])',
}

hktv_benchmarks = {
    "evalState": 'Benchmark "evalState" 7 "app(app(liftM, fst), app(app(app(runStateT, tc0), m), st)))" ( [ ("tc0", ExportCons "Monad" [ExportVar "a"])   , ("m", ExportCons "StateT" [ExportVar "b", ExportVar "a", ExportVar "c"])   , ("st" , ExportVar "b")   ] , ExportCons "a" [ExportVar "c"] )', 
    "composeMonads": 'Benchmark "composeMonads" 9 "app(app(app((=<<), tc0), app(app((.), app(return, tc0)), app(app((=<<), tc1), f))), sm)" ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])   , ("tc1", ExportCons "Monad" [ExportVar "d"])   , ("sm" , ExportCons "c" [ExportCons "d" [ExportVar "a"]])   , ("f"  , ExportFun (ExportVar "a") (ExportCons "d" [ExportVar "b"]))   ] , ExportCons "c" [ExportCons "d" [ExportVar "b"]] )   ', 
    "traverseDAG": 'Benchmark "traverseDAG" 8 "app(app(app(app(app(foldM, tc0), List@Foldable), f), Nil), app(app(map, fst), dag))" ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])   , ( "f"     , ExportFun   (ExportCons "List" [ExportVar "a"])   (ExportFun (ExportVar "b")      (ExportCons "c" [ExportCons "List" [ExportVar "a"]])   )     )   , ( "dag"     , ExportCons "List" [ExportCons "Pair" [ExportVar "b", ExportVar "a"]]     )   ] , ExportCons "c" [ExportCons "List" [ExportVar "a"]] )   ', 
    "extractEitherValues": 'Benchmark "extractEitherValues" 8 "app(app(app(app(mapM, tc1), tc0), app(app(either, Data.Function.id), Data.Function.id)), eithers)" ( [ ("tc0", ExportCons "Traversable" [ExportVar "d"])   , ("tc1", ExportCons "Monad" [ExportVar "c"])   , ( "eithers"     , ExportCons   "d"   [ ExportCons   "Either"   [ExportCons "c" [ExportVar "b"], ExportCons "c" [ExportVar "b"]]   ]     )   ] , ExportCons "c" [ExportCons "d" [ExportVar "b"]] )   ', 
    "iterateLines": 'Benchmark "iterateLines" 7 "app(app(app(evalStateT, tc0), st), app(app(zip, xs), app(lines, input)))" ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])   , ( "st"     , ExportCons   "StateT"   [ ExportCons     "List"     [ExportCons "Pair" [ExportVar "a", ExportCons "String" []]]   , ExportVar "c"   , ExportVar "b"   ]     )   , ("xs"   , ExportCons "List" [ExportVar "a"])   , ("input", ExportCons "String" [])   ] , ExportCons "c" [ExportVar "b"] )   ', 
    "maybeToTransformer": 'Benchmark "maybeToTransformer" 5 "app(app(MaybeT, tc0), app(app(return, tc0), mb))" ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])   , ("mb" , ExportCons "Maybe" [ExportVar "a"])   ] , ExportCons "MaybeT" [ExportVar "c", ExportVar "a"] )   ', 
    "execThreads": 'Benchmark "execThreads" 8 "app(app(fromMaybe, def), app(app(app(msum, Maybe@MonadPlus), List@Foldable), app(app(map, f), threads)))" ( [ ("f", ExportFun (ExportVar "b") (ExportCons "Maybe" [ExportVar "a"]))   , ("threads", ExportCons "List" [ExportVar "b"])   , ("def", ExportVar "a")   ] , ExportVar "a" )   ', 
    "monadicUpdate": 'Benchmark "monadicUpdate" 9 "" ( [ ("tcarg0", ExportCons "Monad" [ExportVar "c"])   , ("e" , ExportCons "c" [ExportVar "a"])   , ("upd"   , ExportFun (ExportVar "a") (ExportCons "c" [ExportVar "b"]))   , ("mb"    , ExportCons "Maybe" [ExportVar "a"])   ] , ExportCons "c" [ExportCons "Maybe" [ExportVar "b"]] )'
}

stackoverflow_benchmarks = {
    "extractEitherValues": 'Benchmark "extractEitherValues" 5 "app(app(GHC.List.map, app(app(Data.Either.either, Data.Function.id), Data.Function.id)), es)" ([("es",ExportCons "List" [ExportCons "Either" [ExportVar "b",ExportVar "b"]])],ExportCons "List" [ExportVar "b"])',
    "filterMultiple": 'Benchmark "filterMultiple" 5 "app(app(GHC.List.filter, app(app(Data.Function.flip, GHC.List.elem), xs)), ys)" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "flipFilter": 'Benchmark "flipFilter" 5 "app(app(GHC.List.filter, app(app((Data.Function..), Data.Bool.not), p)), xs)" ([("p",ExportFun (ExportVar "a") (ExportCons "Bool" [])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "nextIsGreater": 'Benchmark "nextIsGreater" 8 "app(app(GHC.List.all, app((Data.Ord.<), tcarg0)), app(app(GHC.List.zip, app(GHC.List.init, xs)), app(GHC.List.tail, xs)))" ([("tcarg0",ExportCons "@@hplusTC@@Ord" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Bool" [])',
    "multipleNth": 'Benchmark "multipleNth" 4 "app(app(GHC.List.map, app((GHC.List.!!), xs)), indices)" ([("xs",ExportCons "List" [ExportVar "a"]),("indices",ExportCons "List" [ExportCons "Int" []])],ExportCons "List" [ExportVar "a"])',
    "elemFreq": 'Benchmark "elemFreq" 6 "app(zipWith, app(app(GHC.List.map, GHC.List.length), app(app(Data.List.group, tcarg0), app(Data.List.sort, xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportCons "Int" []])',
    "doubleMap": 'Benchmark "doubleMap" 4 "app(app(map, app(map, f)), xss)" ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xss",ExportCons "List" [ExportCons "List" [ExportVar "a"]])],ExportCons "List" [ExportCons "List" [ExportVar "b"]])',
    "sumTuples": 'Benchmark "sumTuples" 7 "app(app(GHC.List.sum, @@hplusTCInstance@@0NumInt), app(app(GHC.List.map, app(app((Data.Function..), GHC.List.length), Data.Tuple.snd)), ps))" ([("ps",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportCons "List" [ExportVar "b"]]])],ExportCons "Int" [])',
    "lessThanNTimes": 'Benchmark "lessThanNTimes" 8 "app(GHC.List.null, app(app(GHC.List.drop, n), app(app(GHC.List.filter, app(app((Data.Eq.==), tcarg0), x)), xs)))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("n",ExportCons "Int" []),("x",ExportVar "a"),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Bool" [])',
    "groupByFirst": 'Benchmark "groupByFirst" 8 "app(app(Data.List.groupBy, app(app(Data.Function.on, app((Data.Eq.==), tcarg0)), Data.Tuple.fst)), app(app(Data.List.sortOn, Data.Tuple.fst), xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportCons "List" [ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]])',
    "mySortBy": 'Benchmark "mySortBy" 5 "app(app(Data.List.sortBy, app(app(Data.Function.on, cmp), Data.Tuple.fst)), xs)" ([("cmp",ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Ordering" []))),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])',
    "transposeAndCompress": 'Benchmark "transposeAndCompress" 7 "app(GHC.List.concat, app(app(app(GHC.List.foldr, app(GHC.List.zipWith, Cons)), app(GHC.List.repeat, Nil)), xs))" ([("xs",ExportCons "List" [ExportCons "List" [ExportVar "a"]])],ExportCons "List" [ExportVar "a"])',
    "partition": 'Benchmark "partition" 9 "app(app(Pair, app(app(GHC.List.filter, p), xs)), app(app(GHC.List.filter, app(app((Data.Function..), Data.Bool.not), p)), xs))" ([("p",ExportFun (ExportVar "a") (ExportCons "Bool" [])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])',
    "matchedKeys": 'Benchmark "matchedKeys" 7 "app(app(GHC.List.map, Data.Tuple.fst), app(app(GHC.List.filter, app(app((Data.Function..), p), Data.Tuple.snd)), xs))" ([("p",ExportFun (ExportVar "b") (ExportCons "Bool" [])),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportCons "List" [ExportVar "a"])',
    "filterPairs": 'Benchmark "filterPairs" 8 "app(app(GHC.List.filter, app(Data.Tuple.uncurry, f)), app(app(GHC.List.zip, xs), ys))" ([("f",ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportCons "Bool" []))),("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportVar "b"])],ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])',
    "applyNthNTimes": 'Benchmark "applyNthNTimes" 7 "app(app(app(GHC.List.zipWith, ($)), app(app(GHC.List.iterate, app((Data.Function..), f)), f)), xs)" ([("f",ExportFun (ExportVar "a") (ExportVar "a")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "removeMax": 'Benchmark "removeMax" 8 "app(app(GHC.List.filter, app(app((Data.Eq./=), tcarg0), app(app(GHC.List.maximum, tcarg0), xs)), xs)" ([("tcarg0",ExportCons "@@hplusTC@@Ord" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "allSameLength": 'Benchmark "allSameLength" 8 "app(app(GHC.List.all, app(app(app(Data.Function.on, app((Data.Eq.==), @@hplusTCInstance@@0EqInt)), GHC.List.length), xs)), xss)" ([("xs",ExportCons "List" [ExportVar "a"]),("xss",ExportCons "List" [ExportCons "List" [ExportVar "a"]])],ExportCons "Bool" [])',
    "mostFrequent": 'Benchmark "mostFrequent" 8 "app(app(GHC.List.head, app(Data.List.maximumBy, app(app(Data.Function.on, app(Data.Ord.compare, tcarg0)), GHC.List.length))), app(Data.List.group, xs))" ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"])],ExportVar "a")',
}

class BenchmarkResult:
    def __init__(self, name, sol, time):
        self.name = name
        self.sol = sol
        self.time = time

def get_time(s):
    match_result = re.search(r"Time: (\d+\.\d+)s", s)
    return match_result.group(1)

def to_time(str):
    if str:
        return float(str)
    else:
        return None

def run_benchmark(name, bench):
    p = Popen(RUN_CMD + [bench], stdin=PIPE, stdout=PIPE)
    prev_line = None
    syn_prog = None
    syn_time = None
    for line in iter(p.stdout.readline, b''):
        print(line.decode()[:-1])
        syn_prog = prev_line
        if line.decode().startswith("Time:"):
            syn_time = get_time(line)
            print("Success", syn_time)
        else:
            prev_line = line.decode()

    if syn_prog is None:
        print("Fail")

    syn_results.append(BenchmarkResult(name, syn_prog, to_time(syn_time)))

def build_argparser():
    argparser = argparse.ArgumentParser(description='Run benchmarks')
    argparser.add_argument('--suites', choices=['hplus', 'hktv', 'containers', 'all'], default='all', help='which suites to run')
    return argparser

if __name__ == "__main__":
    args = build_argparser().parse_args()

    if args.suites == 'all':
        if os.path.exists(PICKLE_FILE):
            with open(PICKLE_FILE, 'rb') as f:
                syn_results = pickle.load(f)
        else:
            syn_results = []
        
        generated = [x.name for x in syn_results]
        for name, bench in stackoverflow_benchmarks.items():
            print("Running benchmark: " + name)
            if name in generated:
                print("Skip")
                continue

            run_benchmark(name, bench)

            # write results to pickle file
            with open("results.pkl", "wb+") as f:
                pickle.dump(syn_results, f)

        # write results to csv 
        with open("results.csv", "w") as f:
            f.write("name,sol,time\n")
            for result in syn_results:
                f.write("{}\t{}\t{}\n".format(result.name, result.sol, result.time))