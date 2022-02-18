import argparse
import re
import sys
import pickle
from subprocess import Popen, PIPE, STDOUT

RUN_CMD = ["stack", "exec", "--", "compact-coupled-terms-exe"]
PICKLE_FILE = "results.pkl"
CSV_FILE = "results.csv"

hplus_benchmarks = {
    "appBoth": 'Benchmark "appBoth" 5 (Term "app" [Term "app" [Term "Pair" [], Term "app" [Term "f" [], Term "x" []]], Term "app" [Term "g" [], Term "x" []]]) ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("g",ExportFun (ExportVar "a") (ExportVar "c")),("x",ExportVar "a")],ExportCons "Pair" [ExportVar "b",ExportVar "c"])',
    "test": 'Benchmark "test" 5 (Term "app" [Term "app" [Term "app" [Term "Data.Bool.bool" [], Term "Data.Maybe.Nothing" []], Term "app" [Term "Data.Maybe.Just" [], Term "x" []]], Term "b" []]) ([("b",ExportCons "Bool" []),("x",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"])',
    "both": 'Benchmark "both" 7 (Term "app" [Term "app" [Term "Pair" [], Term "app" [Term "f" [], Term "app" [Term "Data.Tuple.fst" [], Term "p" []]]], Term "app" [Term "f" [], Term "app" [Term "Data.Tuple.snd" [], Term "p" []]]]) ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("p",ExportCons "Pair" [ExportVar "a",ExportVar "a"])],ExportCons "Pair" [ExportVar "b",ExportVar "b"])',
    "mapEither": 'Benchmark "mapEither" 4 (Term "app" [Term "Data.Either.partitionEithers" [], Term "app" [Term "app" [Term "GHC.List.map" [], Term "f" []], Term "xs" []]]) ([("f",ExportFun (ExportVar "a") (ExportCons "Either" [ExportVar "b",ExportVar "c"])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "b"],ExportCons "List" [ExportVar "c"]])',
    "mapMaybes": 'Benchmark "mapMaybes" 4 (Term "app" [Term "Data.Maybe.listToMaybe" [], Term "app" [Term "app" [Term "Data.Maybe.mapMaybe" [], Term "f" []], Term "xs" []]]) ([("f",ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "b"])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Maybe" [ExportVar "b"])',
    "mergeEither": 'Benchmark "mergeEither" 4 (Term "app" [Term "app" [Term "app" [Term "Data.Either.either" [], Term "Data.Either.Left" []], Term "id" []], Term "e" []]) ([("e",ExportCons "Either" [ExportVar "a",ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportVar "b"])',
    "mbToEither": 'Benchmark "mbToEither" 5 (Term "app" [Term "app" [Term "app" [Term "Data.Maybe.maybe" [], Term "app" [Term "Data.Either.Left" [], Term "x" []]], Term "Data.Either.Right" []], Term "mb" []]) ([("x",ExportVar "a"),("mb",ExportCons "Maybe" [ExportVar "b"])],ExportCons "Either" [ExportVar "a",ExportVar "b"])',
    "cartProduct": 'Benchmark "cartProduct" 6 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "app" [Term "GHC.List.zip" [], Term "xs" []]], Term "app" [Term "app" [Term "GHC.List.map" [], Term "GHC.List.repeat" []], Term "ys" []]]) ([("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportVar "b"])],ExportCons "List" [ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]])',
    "multiAppPair": 'Benchmark "multiAppPair" 7 (Term "app" [Term "app" [Term "Pair" [], Term "app" [Term "app" [Term "Data.Tuple.fst" [], Term "tp" []], Term "x" []]], Term "app" [Term "app" [Term "Data.Tuple.snd" [], Term "tp" []], Term "x" []]]) ([("tp",ExportCons "Pair" [ExportFun (ExportVar "a") (ExportVar "b"),ExportFun (ExportVar "a") (ExportVar "c")]),("x",ExportVar "a")],ExportCons "Pair" [ExportVar "b",ExportVar "c"])',
    "map": 'Benchmark "map" 3 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "f" []], Term "xs" []]) ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "b"])',
    "replFuncs": 'Benchmark "replFuncs" 3 (Term "app" [Term "app" [Term "GHC.List.replicate" [], Term "n" []], Term "f" []]) ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("n",ExportCons "Int" [])],ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "b")])',
    "mbAppFirst": 'Benchmark "mbAppFirst" 5 (Term "app" [Term "app" [Term "app" [Term "Data.Maybe.maybe" [], Term "x" []], Term "f" []], Term "app" [Term "Data.Maybe.listToMaybe" [], Term "xs" []]]) ([("x",ExportVar "b"),("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportVar "b")',
    "mapTwice": 'Benchmark "mapTwice" 5 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "g" []], Term "app" [Term "app" [Term "GHC.List.map" [], Term "f" []], Term "xs" []]]) ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("g",ExportFun (ExportVar "b") (ExportVar "c")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "c"])',
    "resolveEither": 'Benchmark "resolveEither" 4 (Term "app" [Term "app" [Term "app" [Term "Data.Either.either" [], Term "f" []], Term "id" []], Term "e" []]) ([("e",ExportCons "Either" [ExportVar "a",ExportVar "b"]),("f",ExportFun (ExportVar "a") (ExportVar "b"))],ExportVar "b")',
    "firstJust": 'Benchmark "firstJust" 5 (Term "app" [Term "app" [Term "Data.Maybe.fromMaybe" [], Term "x" []], Term "app" [Term "Data.Maybe.listToMaybe" [], Term "app" [Term "Data.Maybe.catMaybes" [], Term "xs" []]]]) ([("x",ExportVar "a"),("xs",ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]])],ExportVar "a")',
    "appendN": 'Benchmark "appendN" 4 (Term "app" [Term "GHC.List.concat" [], Term "app" [Term "app" [Term "GHC.List.replicate" [], Term "n" []], Term "xs" []]]) ([("n",ExportCons "Int" []),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "applyNtimes": 'Benchmark "applyNtimes" 6 (Term "app" [Term "app" [Term "app" [Term "GHC.List.foldr" [], Term "$" []], Term "x" []], Term "app" [Term "app" [Term "GHC.List.replicate" [], Term "n" []], Term "f" []]]) ([("f",ExportFun (ExportVar "a") (ExportVar "a")),("x",ExportVar "a"),("n",ExportCons "Int" [])],ExportVar "a")',
    "dedupe": 'Benchmark "dedupe" 5 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "GHC.List.head" []], Term "app" [Term "app" [Term "Data.List.group" [], Term "tcarg0" []], Term "xs" []]]) ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "inverseMap": 'Benchmark "inverseMap" 5 (Term "app" [Term "app" [Term "app" [Term "GHC.List.zipWith" [], Term "$" []], Term "fs" []], Term "app" [Term "GHC.List.repeat" [], Term "x" []]]) ([("fs",ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "b")]),("x",ExportVar "a")],ExportCons "List" [ExportVar "b"])',
    "app2": 'Benchmark "app2" 4 (Term "app" [Term "app" [Term "f" [], Term "x" []], Term "app" [Term "g" [], Term "x" []]]) ([("f",ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))),("g",ExportFun (ExportVar "a") (ExportVar "b")),("x",ExportVar "a")],ExportVar "c")',
    "singletonList": 'Benchmark "singletonList" 3 (Term "app" [Term "app" [Term "Cons" [], Term "x" []], Term "Nil" []]) ([("x",ExportVar "a")],ExportCons "List" [ExportVar "a"])',
    "headLast": 'Benchmark "headLast" 5 (Term "app" [Term "app" [Term "Pair" [], Term "app" [Term "GHC.List.head" [], Term "xs" []]], Term "app" [Term "GHC.List.last" [], Term "xs" []]]) ([("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportVar "a",ExportVar "a"])',
    "headRest": 'Benchmark "headRest" 3 (Term "app" [Term "Data.Maybe.fromJust" [], Term "app" [Term "GHC.List.uncons" [], Term "xs" []]]) ([("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportVar "a",ExportCons "List" [ExportVar "a"]])',
    "coundPredMatch": 'Benchmark "coundPredMatch" 4 (Term "app" [Term "GHC.List.length" [], Term "app" [Term "app" [Term "GHC.List.filter" [], Term "p" []], Term "xs" []]]) ([("xs",ExportCons "List" [ExportVar "a"]),("p",ExportFun (ExportVar "a") (ExportCons "Bool" []))],ExportCons "Int" [])',
    "splitStr": 'Benchmark "splitStr" 7 (Term "what is the solutions?" []) ([("str",ExportCons "List" [ExportCons "Char" []]),("c",ExportCons "Char" [])],ExportCons "List" [ExportCons "List" [ExportCons "Char" []]])',
    "splitAtFirst": 'Benchmark "splitAtFirst" 5 (Term "app" [Term "app" [Term "GHC.List.break" [], Term "app" [Term "app" [Term "(Data.Eq.==)" [], Term "tcarg0" []], Term "x" []]], Term "xs" []]) ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])',
    "hoogle01": 'Benchmark "hoogle01" 3 (Term "app" [Term "f" [], Term "app" [Term "GHC.List.head" [], Term "xs" []]]) ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportVar "b")',
    "firstMatch": 'Benchmark "firstMatch" 4 (Term "app" [Term "GHC.List.head" [], Term "app" [Term "app" [Term "GHC.List.filter" [], Term "p" []], Term "xs" []]]) ([("xs",ExportCons "List" [ExportVar "a"]),("p",ExportFun (ExportVar "a") (ExportCons "Bool" []))],ExportVar "a")',
    "firstMaybe": 'Benchmark "firstMaybe" 3 (Term "app" [Term "GHC.List.head" [], Term "app" [Term "Data.Maybe.catMaybes" [], Term "mbs" []]]) ([("mbs",ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]])],ExportVar "a")',
    "rights": 'Benchmark "rights" 3 (Term "app" [Term "Data.Either.Right" [], Term "app" [Term "Data.Either.rights" [], Term "es" []]]) ([("es",ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportCons "List" [ExportVar "b"]])',
    "firstKey": 'Benchmark "firstKey" 3 (Term "app" [Term "Data.Tuple.fst" [], Term "app" [Term "GHC.List.head" [], Term "xs" []]]) ([("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportVar "a")',
    "firstRight": 'Benchmark "firstRight" 4 (Term "app" [Term "Data.Either.Right" [], Term "app" [Term "GHC.List.head" [], Term "app" [Term "Data.Either.rights" [], Term "es" []]]]) ([("es",ExportCons "List" [ExportCons "Either" [ExportVar "a",ExportVar "b"]])],ExportCons "Either" [ExportVar "a",ExportVar "b"])',
    "maybe": 'Benchmark "maybe" 4 (Term "app" [Term "Data.Maybe.Just" [], Term "app" [Term "app" [Term "Data.Maybe.fromMaybe" [], Term "x" []], Term "mb" []]]) ([("mb",ExportCons "Maybe" [ExportVar "a"]),("x",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"])',
    "app3": 'Benchmark "app3" 4 (Term "app" [Term "app" [Term "app" [Term "f" [], Term "x" []], Term "z" []], Term "y" []]) ([("f",ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportFun (ExportVar "c") (ExportVar "d")))),("x",ExportVar "a"),("y",ExportVar "c"),("z",ExportVar "b")],ExportVar "d")',
    "zipWithResult": 'Benchmark "zipWithResult" 5 (Term "app" [Term "app" [Term "GHC.List.zip" [], Term "xs" []], Term "app" [Term "app" [Term "GHC.List.map" [], Term "f" []], Term "xs" []]]) ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])',
    "eitherTriple": 'Benchmark "eitherTriple" 5 (Term "app" [Term "app" [Term "app" [Term "Data.Bool.bool" [], Term "e2" []], Term "e1" []], Term "app" [Term "Data.Either.isLeft" [], Term "e1" []]]) ([("e1",ExportCons "Either" [ExportVar "a",ExportVar "b"]),("e2",ExportCons "Either" [ExportVar "a",ExportVar "b"])],ExportCons "Either" [ExportVar "a",ExportVar "b"])',
    "pipe": 'Benchmark "pipe" 4 (Term "app" [Term "app" [Term "app" [Term "GHC.List.foldr" [], Term "$" []], Term "x" []], Term "fs" []]) ([("fs",ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "a")]),("x",ExportVar "a")],ExportVar "a")',
    "lookup": 'Benchmark "lookup" 5 (Term "app" [Term "Data.Maybe.fromJust" [], Term "app" [Term "app" [Term "app" [Term "GHC.List.lookup" [], Term "tcarg0" []], Term "k" []], Term "xs" []]]) ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]),("k",ExportVar "a")],ExportVar "b")',
    "mbElem": 'Benchmark "mbElem" 6 (Term "app" [Term "Data.Maybe.listToMaybe" [], Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "app" [Term "(Data.Eq.==)" [], Term "tcarg0" []], Term "x" []]], Term "xs" []]]) ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Maybe" [ExportVar "a"])',
    "areEq": 'Benchmark "areEq" 7 (Term "app" [Term "Data.Maybe.listToMaybe" [], Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "app" [Term "(Data.Eq.==)" [], Term "tcarg0" []], Term "x" []]], Term "app" [Term "GHC.List.repeat" [], Term "y" []]]]) ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("x",ExportVar "a"),("y",ExportVar "a")],ExportCons "Maybe" [ExportVar "a"])',
    "applyPair": 'Benchmark "applyPair" 4 (Term "app" [Term "app" [Term "Data.Tuple.fst" [], Term "p" []], Term "app" [Term "Data.Tuple.snd" [], Term "p" []]]) ([("p",ExportCons "Pair" [ExportFun (ExportVar "a") (ExportVar "b"),ExportVar "a"])],ExportVar "b")',
    "flatten": 'Benchmark "flatten" 3 (Term "app" [Term "GHC.List.concat" [], Term "app" [Term "GHC.List.concat" [], Term "xss" []]]) ([("xss",ExportCons "List" [ExportCons "List" [ExportCons "List" [ExportVar "a"]]])],ExportCons "List" [ExportVar "a"])',
    "takeNdropM": 'Benchmark "takeNdropM" 7 (Term "app" [Term "app" [Term "Pair" [], Term "app" [Term "app" [Term "GHC.List.take" [], Term "n" []], Term "xs" []]], Term "app" [Term "app" [Term "GHC.List.drop" [], Term "m" []], Term "xs" []]]) ([("n",ExportCons "Int" []),("m",ExportCons "Int" []),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])',
    "indexesOf": 'Benchmark "indexesOf" 6 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "Data.Tuple.snd" []], Term "app" [Term "f" [], Term "app" [Term "app" [Term "GHC.List.zip" [], Term "xs" []], Term "ys" []]]]) ([("f",ExportFun (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportCons "Int" []]]) (ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportCons "Int" []]])),("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportCons "Int" []])],ExportCons "List" [ExportCons "Int" []])',
    "containsEdge": 'Benchmark "containsEdge" 9 (Term "app" [Term "app" [Term "(Data.Bool.&&)" [], Term "app" [Term "app" [Term "GHC.List.elem" [], Term "app" [Term "Data.Tuple.fst" [], Term "edge" []]], Term "vs" []]], Term "app" [Term "app" [Term "GHC.List.elem" [], Term "app" [Term "Data.Tuple.snd" [], Term "edge" []]], Term "vs" []]]) ([("vs",ExportCons "List" [ExportCons "Int" []]),("edge",ExportCons "Pair" [ExportCons "Int" [],ExportCons "Int" []])],ExportCons "Bool" [])',
}

# hktv_benchmarks = {
#     "evalState": 'Benchmark "evalState" 7 "app(app(liftM, fst), app(app(app(runStateT, tc0), m), st)))" ( [ ("tc0", ExportCons "Monad" [ExportVar "a"])   , ("m", ExportCons "StateT" [ExportVar "b", ExportVar "a", ExportVar "c"])   , ("st" , ExportVar "b")   ] , ExportCons "a" [ExportVar "c"] )', 
#     "composeMonads": 'Benchmark "composeMonads" 9 "app(app(app((=<<), tc0), app(app((.), app(return, tc0)), app(app((=<<), tc1), f))), sm)" ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])   , ("tc1", ExportCons "Monad" [ExportVar "d"])   , ("sm" , ExportCons "c" [ExportCons "d" [ExportVar "a"]])   , ("f"  , ExportFun (ExportVar "a") (ExportCons "d" [ExportVar "b"]))   ] , ExportCons "c" [ExportCons "d" [ExportVar "b"]] )   ', 
#     "traverseDAG": 'Benchmark "traverseDAG" 8 "app(app(app(app(app(foldM, tc0), List@Foldable), f), Nil), app(app(map, fst), dag))" ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])   , ( "f"     , ExportFun   (ExportCons "List" [ExportVar "a"])   (ExportFun (ExportVar "b")      (ExportCons "c" [ExportCons "List" [ExportVar "a"]])   )     )   , ( "dag"     , ExportCons "List" [ExportCons "Pair" [ExportVar "b", ExportVar "a"]]     )   ] , ExportCons "c" [ExportCons "List" [ExportVar "a"]] )   ', 
#     "extractEitherValues": 'Benchmark "extractEitherValues" 8 "app(app(app(app(mapM, tc1), tc0), app(app(either, id), id)), eithers)" ( [ ("tc0", ExportCons "Traversable" [ExportVar "d"])   , ("tc1", ExportCons "Monad" [ExportVar "c"])   , ( "eithers"     , ExportCons   "d"   [ ExportCons   "Either"   [ExportCons "c" [ExportVar "b"], ExportCons "c" [ExportVar "b"]]   ]     )   ] , ExportCons "c" [ExportCons "d" [ExportVar "b"]] )   ', 
#     "iterateLines": 'Benchmark "iterateLines" 7 "app(app(app(evalStateT, tc0), st), app(app(zip, xs), app(lines, input)))" ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])   , ( "st"     , ExportCons   "StateT"   [ ExportCons     "List"     [ExportCons "Pair" [ExportVar "a", ExportCons "String" []]]   , ExportVar "c"   , ExportVar "b"   ]     )   , ("xs"   , ExportCons "List" [ExportVar "a"])   , ("input", ExportCons "String" [])   ] , ExportCons "c" [ExportVar "b"] )   ', 
#     "maybeToTransformer": 'Benchmark "maybeToTransformer" 5 "app(app(MaybeT, tc0), app(app(return, tc0), mb))" ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])   , ("mb" , ExportCons "Maybe" [ExportVar "a"])   ] , ExportCons "MaybeT" [ExportVar "c", ExportVar "a"] )   ', 
#     "execThreads": 'Benchmark "execThreads" 8 "app(app(fromMaybe, def), app(app(app(msum, Maybe@MonadPlus), List@Foldable), app(app(map, f), threads)))" ( [ ("f", ExportFun (ExportVar "b") (ExportCons "Maybe" [ExportVar "a"]))   , ("threads", ExportCons "List" [ExportVar "b"])   , ("def", ExportVar "a")   ] , ExportVar "a" )   ', 
#     "monadicUpdate": 'Benchmark "monadicUpdate" 9 "" ( [ ("tcarg0", ExportCons "Monad" [ExportVar "c"])   , ("e" , ExportCons "c" [ExportVar "a"])   , ("upd"   , ExportFun (ExportVar "a") (ExportCons "c" [ExportVar "b"]))   , ("mb"    , ExportCons "Maybe" [ExportVar "a"])   ] , ExportCons "c" [ExportCons "Maybe" [ExportVar "b"]] )'
# }

stackoverflow_benchmarks = {
    "extractEitherValues": 'Benchmark "extractEitherValues" 5 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "app" [Term "app" [Term "Data.Either.either" [], Term "id" []], Term "id" []]], Term "es" []]) ([("es",ExportCons "List" [ExportCons "Either" [ExportVar "b",ExportVar "b"]])],ExportCons "List" [ExportVar "b"])',
    "filterMultiple": 'Benchmark "filterMultiple" 6 (Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "app" [Term "Data.Function.flip" [], Term "app" [Term "GHC.List.elem" [], Term "tcarg0" []]], Term "xs" []]], Term "ys" []]) ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "filterNot": 'Benchmark "filterNot" 5 (Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "app" [Term "(Data.Function..)" [], Term "Data.Bool.not" []], Term "p" []]], Term "xs" []]) ([("p",ExportFun (ExportVar "a") (ExportCons "Bool" [])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "isSortedBy": 'Benchmark "isSortedBy" 7 (Term "app" [Term "GHC.List.and" [], Term "app" [Term "app" [Term "app" [Term "GHC.List.zipWith" [], Term "cmp" []], Term "app" [Term "GHC.List.init" [], Term "xs" []]], Term "app" [Term "GHC.List.tail" [], Term "xs" []]]]) ([("cmp", ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Bool" []))),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Bool" [])',
    "multipleNth": 'Benchmark "multipleNth" 4 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "app" [Term "(GHC.List.!!)" [], Term "xs" []]], Term "indices" []]) ([("xs",ExportCons "List" [ExportVar "a"]),("indices",ExportCons "List" [ExportCons "Int" []])],ExportCons "List" [ExportVar "a"])',
    "doubleMap": 'Benchmark "doubleMap" 4 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "app" [Term "GHC.List.map" [], Term "f" []]], Term "xss" []]) ([("f",ExportFun (ExportVar "a") (ExportVar "b")),("xss",ExportCons "List" [ExportCons "List" [ExportVar "a"]])],ExportCons "List" [ExportCons "List" [ExportVar "b"]])',
    "lengthOfSnds": 'Benchmark "lengthOfSnds" 5 (Term "app" [Term "GHC.List.length" [], Term "app" [Term "GHC.List.concat" [], Term "app" [Term "app" [Term "GHC.List.map" [], Term "Data.Tuple.snd" []], Term "ps" []]] ]) ([("ps",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportCons "List" [ExportVar "b"]]])],ExportCons "Int" [])',
    "lessThanNTimes": 'Benchmark "lessThanNTimes" 8 (Term "app" [Term "GHC.List.null" [], Term "app" [Term "app" [Term "GHC.List.drop" [], Term "n" []], Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "app" [Term "(Data.Eq.==)" [], Term "tcarg0" []], Term "x" []]], Term "xs" []]]]) ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("n",ExportCons "Int" []),("x",ExportVar "a"),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Bool" [])',
    "groupByFirst": 'Benchmark "groupByFirst" 6 (Term "app" [Term "app" [Term "Data.List.groupBy" [], Term "app" [Term "app" [Term "Data.Function.on" [], Term "app" [Term "(Data.Eq.==)" [], Term "tcarg0" []]], Term "Data.Tuple.fst" []]], Term "xs" []]) ([("tcarg0",ExportCons "@@hplusTC@@Eq" [ExportVar "a"]),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportCons "List" [ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]]])',
    "mySortBy": 'Benchmark "mySortBy" 5 (Term "app" [Term "app" [Term "Data.List.sortBy" [], Term "app" [Term "app" [Term "Data.Function.on" [], Term "cmp" []], Term "Data.Tuple.fst" []]], Term "xs" []]) ([("cmp",ExportFun (ExportVar "a") (ExportFun (ExportVar "a") (ExportCons "Ordering" []))),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])',
    "transpose": 'Benchmark "transpose" 6 (Term "app" [Term "app" [Term "app" [Term "GHC.List.foldr" [], Term "app" [Term "GHC.List.zipWith" [], Term "Cons" []]], Term "app" [Term "GHC.List.repeat" [], Term "Nil" []]], Term "xs" []]) ([("xs",ExportCons "List" [ExportCons "List" [ExportVar "a"]])],ExportCons "List" [ExportCons "List" [ExportVar "a"]])',
    "partition": 'Benchmark "partition" 9 (Term "app" [Term "app" [Term "Pair" [], Term "app" [Term "app" [Term "GHC.List.filter" [], Term "p" []], Term "xs" []]], Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "app" [Term "(Data.Function..)" [], Term "Data.Bool.not" []], Term "p" []]], Term "xs" []]]) ([("p",ExportFun (ExportVar "a") (ExportCons "Bool" [])),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "Pair" [ExportCons "List" [ExportVar "a"],ExportCons "List" [ExportVar "a"]])',
    "matchedKeys": 'Benchmark "matchedKeys" 7 (Term "app" [Term "app" [Term "GHC.List.map" [], Term "Data.Tuple.fst" []], Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "app" [Term "(Data.Function..)" [], Term "p" []], Term "Data.Tuple.snd" []]], Term "xs" []]]) ([("p",ExportFun (ExportVar "b") (ExportCons "Bool" [])),("xs",ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])],ExportCons "List" [ExportVar "a"])',
    "filterPairs": 'Benchmark "filterPairs" 6 (Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "Data.Tuple.uncurry" [], Term "f" []]], Term "app" [Term "app" [Term "GHC.List.zip" [], Term "xs" []], Term "ys" []]]) ([("f",ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportCons "Bool" []))),("xs",ExportCons "List" [ExportVar "a"]),("ys",ExportCons "List" [ExportVar "b"])],ExportCons "List" [ExportCons "Pair" [ExportVar "a",ExportVar "b"]])',
    "applyNthNTimes": 'Benchmark "applyNthNTimes" 7 (Term "app" [Term "app" [Term "app" [Term "GHC.List.zipWith" [], Term "$" []], Term "app" [Term "app" [Term "GHC.List.iterate" [], Term "app" [Term "(Data.Function..)" [], Term "f" []]], Term "f" []]], Term "xs" []]) ([("f",ExportFun (ExportVar "a") (ExportVar "a")),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "removeMax": 'Benchmark "removeMax" 7 (Term "app" [Term "app" [Term "GHC.List.filter" [], Term "app" [Term "app" [Term "(Data.Eq./=)_Ord" [], Term "tcarg0" []], Term "app" [Term "app" [Term "GHC.List.maximum" [], Term "tcarg0" []], Term "xs" []]], Term "xs" []]) ([("tcarg0",ExportCons "@@hplusTC@@Ord" [ExportVar "a"]),("xs",ExportCons "List" [ExportVar "a"])],ExportCons "List" [ExportVar "a"])',
    "allSameLength": 'Benchmark "allSameLength" 7 (Term "app" [Term "app" [Term "GHC.List.all" [], Term "app" [Term "app" [Term "app" [Term "Data.Function.on" [], Term "app" [Term "(Data.Eq.==)" [], Term "@@hplusTCInstance@@0EqInt" []]], Term "GHC.List.length" []], Term "xs" []]], Term "xss" []]) ([("xs",ExportCons "List" [ExportVar "a"]),("xss",ExportCons "List" [ExportCons "List" [ExportVar "a"]])],ExportCons "Bool" [])',
    "mostFrequent": 'Benchmark "mostFrequent" 7 (Term "app" [Term "app" [Term "Data.List.maximumBy" [], Term "app" [Term "app" [Term "Data.Function.on" [], Term "app" [Term "Data.Ord.compare" [], Term "@@hplusTCInstance@@0OrdInt" []]], Term "Data.Tuple.snd" []]], Term "app" [Term "occur" [], Term "xs" []]]) ([("xs",ExportCons "List" [ExportVar "a"]), ("occur", ExportFun (ExportCons "List" [ExportVar "a"]) (ExportCons "List" [ExportCons "Pair" [ExportVar "a", ExportCons "Int" []]]))],ExportCons "Pair" [ExportVar "a", ExportCons "Int" []])',
    "splitOn" : 'Benchmark "splitOn" 7 (Term "app" [Term "app" [Term "Data.List.groupBy" [], Term "app" [Term "app" [Term "Data.Function.on" [], Term "(Data.Bool.&&)" []], Term "app" [Term "app" [Term "(Data.Eq./=)" [], Term "tcarg0" []], Term "x" []]]], Term "xs" []]) ([("tcarg0", ExportCons "@@hplusTC@@Eq" [ExportVar "a"]), ("x", ExportVar "a"), ("xs", ExportCons "List" [ExportVar "a"])], ExportCons "List" [ExportCons "List" [ExportVar "a"]])',
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
        print(line.decode(), end='')
        syn_prog = prev_line
        if line.decode().startswith("Time:"):
            syn_time = get_time(line)
            print("Success", syn_time)
        else:
            prev_line = line.decode()

    if syn_prog is None:
        print("Fail")

    sys.stdout.flush()
    syn_results.append(BenchmarkResult(name, syn_prog, to_time(syn_time)))

def build_argparser():
    argparser = argparse.ArgumentParser(description='Run benchmarks')
    argparser.add_argument('--suites', choices=['hplus', 'hktv', 'stackoverflow', 'all'], default='all', help='which suites to run')
    argparser.add_argument('--benchmarks', nargs='+', help='which benchmarks to run')
    return argparser

if __name__ == "__main__":
    args = build_argparser().parse_args()

    benchmarks = {}
    if 'hplus' in args.suites or 'all' in args.suites:
        if args.benchmarks:
            benchmarks['hplus'] = {name: hplus_benchmarks[name] for name in args.benchmarks}
        else:
            benchmarks['hplus'] = hplus_benchmarks    

    if 'stackoverflow' in args.suites or 'all' in args.suites:
        if args.benchmarks:
            benchmarks['stackoverflow'] = {name: stackoverflow_benchmarks[name] for name in args.benchmarks}
        else:
            benchmarks['stackoverflow'] = stackoverflow_benchmarks

    syn_results = []
    for suite, suite_benches in benchmarks.items():
        print("===============================================================")
        print("Running suite", suite)
        for name, bench in suite_benches.items():
            print("---------------------------------------------------------------")
            print("Running benchmark: " + name)
            run_benchmark(name, bench)

    # write results to csv 
    with open("results.csv", "w") as f:
        f.write("name,sol,time\n")
        for result in syn_results:
            f.write("{}\t{}\t{}\n".format(result.name, result.sol, result.time))