{-# LANGUAGE OverloadedStrings #-}

module Application.TermSearch.Benchmark where

import           Application.TermSearch.Type
import           Data.Text                      ( Text )

hoogleplusBenchmarks :: [Benchmark]
hoogleplusBenchmarks =
  [ Benchmark
    "appBoth"
    5
    "app(app(Pair, app(f, x)), app(g, x))"
    ( [ ("f", ExportFun (ExportVar "a") (ExportVar "b"))
      , ("g", ExportFun (ExportVar "a") (ExportVar "c"))
      , ("x", ExportVar "a")
      ]
    , ExportCons "Pair" [ExportVar "b", ExportVar "c"]
    )
  , Benchmark
    "test"
    5
    "app(app(app(Data.Bool.bool, Data.Maybe.Nothing), app(Data.Maybe.Just, x)), b)"
    ( [("b", ExportCons "Bool" []), ("x", ExportVar "a")]
    , ExportCons "Maybe" [ExportVar "a"]
    )
  , Benchmark
    "both"
    7
    "app(app(Pair, app(f, app(Data.Tuple.fst, p))), app(f, app(Data.Tuple.snd, p)))"
    ( [ ("p", ExportCons "Pair" [ExportVar "a", ExportVar "a"])
      , ("f", ExportFun (ExportVar "a") (ExportVar "b"))
      ]
    , ExportCons "Pair" [ExportVar "b", ExportVar "b"]
    )
  , Benchmark
    "mapEither"
    4
    "app(Data.Either.partitionEithers, app(app(GHC.List.map, f), xs))"
    ( [ ( "f"
        , ExportFun (ExportVar "a")
                    (ExportCons "Either" [ExportVar "b", ExportVar "c"])
        )
      , ("xs", ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons
      "Pair"
      [ExportCons "List" [ExportVar "b"], ExportCons "List" [ExportVar "c"]]
    )
  , Benchmark
    "mapMaybes"
    4
    "app(Data.Maybe.listToMaybe, app(app(Data.Maybe.mapMaybe, f), xs))"
    ( [ ("f" , ExportFun (ExportVar "a") (ExportCons "Maybe" [ExportVar "b"]))
      , ("xs", ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons "Maybe" [ExportVar "b"]
    )
  , Benchmark
    "mergeEither"
    4
    "app(app(app(Data.Either.either, Data.Either.Left), Data.Function.id), e)"
    ( [ ( "e"
        , ExportCons
          "Either"
          [ExportVar "a", ExportCons "Either" [ExportVar "a", ExportVar "b"]]
        )
      ]
    , ExportCons "Either" [ExportVar "a", ExportVar "b"]
    )
  , Benchmark
    "mbToEither"
    5
    "app(app(app(Data.Maybe.maybe, app(Data.Either.Left, x)), Data.Either.Right), mb)"
    ( [("x", ExportVar "a"), ("mb", ExportCons "Maybe" [ExportVar "b"])]
    , ExportCons "Either" [ExportVar "a", ExportVar "b"]
    )
  , Benchmark
    "cartProduct"
    6
    "app(app(GHC.List.map, app(GHC.List.zip, xs)), app(app(GHC.List.map, GHC.List.repeat), ys))"
    ( [ ("xs", ExportCons "List" [ExportVar "a"])
      , ("ys", ExportCons "List" [ExportVar "b"])
      ]
    , ExportCons
      "List"
      [ExportCons "List" [ExportCons "Pair" [ExportVar "a", ExportVar "b"]]]
    )
  , Benchmark
    "multiAppPair"
    7
    "app(app(Pair, app(app(Data.Tuple.fst, tp), x)), app(app(Data.Tuple.snd, tp), x))"
    ( [ ( "tp"
        , ExportCons
          "Pair"
          [ ExportFun (ExportVar "a") (ExportVar "b")
          , ExportFun (ExportVar "a") (ExportVar "c")
          ]
        )
      , ("x", ExportVar "a")
      ]
    , ExportCons "Pair" [ExportVar "b", ExportVar "c"]
    )
  , Benchmark
    "map"
    3
    "app(app(GHC.List.map, f), xs)"
    ( [ ("f" , ExportFun (ExportVar "a") (ExportVar "b"))
      , ("xs", ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons "List" [ExportVar "b"]
    )
  , Benchmark
    "replFuncs"
    3
    "app(app(GHC.List.replicate, n), f)"
    ( [ ("f", ExportFun (ExportVar "a") (ExportVar "b"))
      , ("n", ExportCons "Int" [])
      ]
    , ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "b")]
    )
  , Benchmark
    "mbAppFirst"
    5
    "app(app(app(Data.Maybe.maybe, x), f), app(Data.Maybe.listToMaybe, xs))"
    ( [ ("x" , ExportVar "b")
      , ("f" , ExportFun (ExportVar "a") (ExportVar "b"))
      , ("xs", ExportCons "List" [ExportVar "a"])
      ]
    , ExportVar "b"
    )
  , Benchmark
    "mapTwice"
    5
    "app(app(GHC.List.map, g), app(app(GHC.List.map, f), xs))"
    ( [ ("f" , ExportFun (ExportVar "a") (ExportVar "b"))
      , ("g" , ExportFun (ExportVar "b") (ExportVar "c"))
      , ("xs", ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons "List" [ExportVar "c"]
    )
  , Benchmark
    "resolveEither"
    4
    "app(app(app(Data.Either.either, f), Data.Function.id), e)"
    ( [ ("e", ExportCons "Either" [ExportVar "a", ExportVar "b"])
      , ("f", ExportFun (ExportVar "a") (ExportVar "b"))
      ]
    , ExportVar "b"
    )
  , Benchmark
    "firstJust"
    5
    "app(app(Data.Maybe.fromMaybe, x), app(Data.Maybe.listToMaybe, app(Data.Maybe.catMaybes, xs)))"
    ( [ ("x" , ExportVar "a")
      , ("xs", ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]])
      ]
    , ExportVar "a"
    )
  , Benchmark
    "appendN"
    4
    "app(GHC.List.concat, app(app(GHC.List.replicate, n), xs))"
    ( [("n", ExportCons "Int" []), ("xs", ExportCons "List" [ExportVar "a"])]
    , ExportCons "List" [ExportVar "a"]
    )
  , Benchmark
    "applyNtimes"
    6
    "app(app(app(GHC.List.foldr, $), x), app(app(GHC.List.replicate, n), f))"
    ( [ ("f", ExportFun (ExportVar "a") (ExportVar "a"))
      , ("x", ExportVar "a")
      , ("n", ExportCons "Int" [])
      ]
    , ExportVar "a"
    )
  , Benchmark
    "dedupe"
    5
    "app(app(GHC.List.map, GHC.List.head), app(app(Data.List.group, tcarg0), xs))"
    ( [ ("tcarg0", ExportCons "@@hplusTC@@Eq" [ExportVar "a"])
      , ("xs"    , ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons "List" [ExportVar "a"]
    )
  , Benchmark
    "inverseMap"
    5
    "app(app(app(GHC.List.zipWith, $), fs), app(GHC.List.repeat, x))"
    ( [ ("fs", ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "b")])
      , ("x" , ExportVar "a")
      ]
    , ExportCons "List" [ExportVar "b"]
    )
  , Benchmark
    "app2"
    4
    "app(app(f, x), app(g, x))"
    ( [ ( "f"
        , ExportFun (ExportVar "a") (ExportFun (ExportVar "b") (ExportVar "c"))
        )
      , ("g", ExportFun (ExportVar "a") (ExportVar "b"))
      , ("x", ExportVar "a")
      ]
    , ExportVar "c"
    )
  , Benchmark "singletonList"
              3
              "app(app(Cons, x), Nil)"
              ([("x", ExportVar "a")], ExportCons "List" [ExportVar "a"])
  , Benchmark
    "headLast"
    5
    "app(app(Pair, app(GHC.List.head, xs)), app(GHC.List.last, xs))"
    ( [("xs", ExportCons "List" [ExportVar "a"])]
    , ExportCons "Pair" [ExportVar "a", ExportVar "a"]
    )
  , Benchmark
    "headRest"
    3
    "app(Data.Maybe.fromJust, app(GHC.List.uncons, xs))"
    ( [("xs", ExportCons "List" [ExportVar "a"])]
    , ExportCons "Pair" [ExportVar "a", ExportCons "List" [ExportVar "a"]]
    )
  , Benchmark
    "coundPredMatch"
    4
    "app(GHC.List.length, app(app(GHC.List.filter, p), xs))"
    ( [ ("xs", ExportCons "List" [ExportVar "a"])
      , ("p" , ExportFun (ExportVar "a") (ExportCons "Bool" []))
      ]
    , ExportCons "Int" []
    )
  , Benchmark
    "splitStr"
    7
    "impossible"
    ( [ ("str", ExportCons "List" [ExportCons "Char" []])
      , ("c"  , ExportCons "Char" [])
      ]
    , ExportCons "List" [ExportCons "List" [ExportCons "Char" []]]
    )
  , Benchmark
    "splitAtFirst"
    5
    "app(app(GHC.List.break, app(app((Data.Eq.==), tcarg0), x)), xs)"
    ( [ ("tcarg0", ExportCons "@@hplusTC@@Eq" [ExportVar "a"])
      , ("x"     , ExportVar "a")
      , ("xs"    , ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons
      "Pair"
      [ExportCons "List" [ExportVar "a"], ExportCons "List" [ExportVar "a"]]
    )
  , Benchmark
    "hoogle01"
    3
    "app(f, app(GHC.List.head, xs))"
    ( [ ("f" , ExportFun (ExportVar "a") (ExportVar "b"))
      , ("xs", ExportCons "List" [ExportVar "a"])
      ]
    , ExportVar "b"
    )
  , Benchmark
    "firstMatch"
    4
    "app(GHC.List.head, app(app(GHC.List.filter, p), xs))"
    ( [ ("xs", ExportCons "List" [ExportVar "a"])
      , ("p" , ExportFun (ExportVar "a") (ExportCons "Bool" []))
      ]
    , ExportVar "a"
    )
  , Benchmark
    "firstMaybe"
    3
    "app(GHC.List.head, app(Data.Maybe.catMaybes, mbs))"
    ( [("mbs", ExportCons "List" [ExportCons "Maybe" [ExportVar "a"]])]
    , ExportVar "a"
    )
  , Benchmark
    "rights"
    3
    "app(Data.Either.Right, app(Data.Either.rights, es))"
    ( [ ( "es"
        , ExportCons "List" [ExportCons "Either" [ExportVar "a", ExportVar "b"]]
        )
      ]
    , ExportCons "Either" [ExportVar "a", ExportCons "List" [ExportVar "b"]]
    )
  , Benchmark
    "firstKey"
    3
    "app(Data.Tuple.fst, app(GHC.List.head, xs))"
    ( [ ( "xs"
        , ExportCons "List" [ExportCons "Pair" [ExportVar "a", ExportVar "b"]]
        )
      ]
    , ExportVar "a"
    )
  , Benchmark
    "firstRight"
    4
    "app(Data.Either.Right, app(GHC.List.head, app(Data.Either.rights, es)))"
    ( [ ( "es"
        , ExportCons "List" [ExportCons "Either" [ExportVar "a", ExportVar "b"]]
        )
      ]
    , ExportCons "Either" [ExportVar "a", ExportVar "b"]
    )
  , Benchmark
    "maybe"
    4
    "app(Data.Maybe.Just, app(app(Data.Maybe.fromMaybe, x), mb))"
    ( [("mb", ExportCons "Maybe" [ExportVar "a"]), ("x", ExportVar "a")]
    , ExportCons "Maybe" [ExportVar "a"]
    )
  , Benchmark
    "app3"
    4
    "app(app(app(f, x), z), y)"
    ( [ ( "f"
        , ExportFun
          (ExportVar "a")
          (ExportFun (ExportVar "b") (ExportFun (ExportVar "c") (ExportVar "d"))
          )
        )
      , ("x", ExportVar "a")
      , ("y", ExportVar "c")
      , ("z", ExportVar "b")
      ]
    , ExportVar "d"
    )
  , Benchmark
    "zipWithResult"
    5
    "app(app(GHC.List.zip, xs), app(app(GHC.List.map, f), xs))"
    ( [ ("f" , ExportFun (ExportVar "a") (ExportVar "b"))
      , ("xs", ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons "List" [ExportCons "Pair" [ExportVar "a", ExportVar "b"]]
    )
  , Benchmark
    "eitherTriple"
    5
    "app(app(app(Data.Bool.bool, e2), e1), app(Data.Either.isLeft, e1))"
    ( [ ("e1", ExportCons "Either" [ExportVar "a", ExportVar "b"])
      , ("e2", ExportCons "Either" [ExportVar "a", ExportVar "b"])
      ]
    , ExportCons "Either" [ExportVar "a", ExportVar "b"]
    )
  , Benchmark
    "pipe"
    4
    "app(app(app(GHC.List.foldr, $), x), fs)"
    ( [ ("fs", ExportCons "List" [ExportFun (ExportVar "a") (ExportVar "a")])
      , ("x" , ExportVar "a")
      ]
    , ExportVar "a"
    )
  , Benchmark
    "lookup"
    5
    "app(Data.Maybe.fromJust, app(app(app(GHC.List.lookup, tcarg0), k), xs))"
    ( [ ("tcarg0", ExportCons "@@hplusTC@@Eq" [ExportVar "a"])
      , ( "xs"
        , ExportCons "List" [ExportCons "Pair" [ExportVar "a", ExportVar "b"]]
        )
      , ("k", ExportVar "a")
      ]
    , ExportVar "b"
    )
  , Benchmark
    "mbElem"
    6
    "app(Data.Maybe.listToMaybe, app(app(GHC.List.filter, app(app((Data.Eq.==), tcarg0), x)), xs))"
    ( [ ("tcarg0", ExportCons "@@hplusTC@@Eq" [ExportVar "a"])
      , ("x"     , ExportVar "a")
      , ("xs"    , ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons "Maybe" [ExportVar "a"]
    )
  , Benchmark
    "areEq"
    7
    "app(Data.Maybe.listToMaybe, app(app(GHC.List.filter, app(app((Data.Eq.==), tcarg0), x)), app(GHC.List.repeat, y)))"
    ( [ ("tcarg0", ExportCons "@@hplusTC@@Eq" [ExportVar "a"])
      , ("x"     , ExportVar "a")
      , ("y"     , ExportVar "a")
      ]
    , ExportCons "Maybe" [ExportVar "a"]
    )
  , Benchmark
    "applyPair"
    4
    "app(app(Data.Tuple.fst, p), app(Data.Tuple.snd, p))"
    ( [ ( "p"
        , ExportCons
          "Pair"
          [ExportFun (ExportVar "a") (ExportVar "b"), ExportVar "a"]
        )
      ]
    , ExportVar "b"
    )
  , Benchmark
    "flatten"
    3
    "app(GHC.List.concat, app(GHC.List.concat, xss))"
    ( [ ( "xss"
        , ExportCons "List"
                     [ExportCons "List" [ExportCons "List" [ExportVar "a"]]]
        )
      ]
    , ExportCons "List" [ExportVar "a"]
    )
  , Benchmark
    "takeNdropM"
    7
    "app(app(Pair, app(app(GHC.List.take, n), xs)), app(app(GHC.List.drop, m), xs))"
    ( [ ("n" , ExportCons "Int" [])
      , ("m" , ExportCons "Int" [])
      , ("xs", ExportCons "List" [ExportVar "a"])
      ]
    , ExportCons
      "Pair"
      [ExportCons "List" [ExportVar "a"], ExportCons "List" [ExportVar "a"]]
    )
  , Benchmark
    "indexesOf"
    6
    "app(app(GHC.List.map, Data.Tuple.snd), app(f, app(app(GHC.List.zip, xs), ys)))"
    ( [ ( "f"
        , ExportFun
          (ExportCons "List"
                      [ExportCons "Pair" [ExportVar "a", ExportCons "Int" []]]
          )
          (ExportCons "List"
                      [ExportCons "Pair" [ExportVar "a", ExportCons "Int" []]]
          )
        )
      , ("xs", ExportCons "List" [ExportVar "a"])
      , ("ys", ExportCons "List" [ExportCons "Int" []])
      ]
    , ExportCons "List" [ExportCons "Int" []]
    )
  , Benchmark
    "containsEdge"
    9
    "app(app((Data.Bool.&&), app(app(GHC.List.elem, app(Data.Tuple.fst, edge)), vs)), app(app(GHC.List.elem, app(Data.Tuple.snd, edge)), vs))"
    ( [ ("vs"  , ExportCons "List" [ExportCons "Int" []])
      , ("edge", ExportCons "Pair" [ExportCons "Int" [], ExportCons "Int" []])
      ]
    , ExportCons "Bool" []
    )
  ]

hktvBenchmarks :: [Benchmark]
hktvBenchmarks =
  [ Benchmark
    "evalState"
    7
    "app(app(liftM, fst), app(app(app(runStateT, tc0), m), st)))"
    ( [ ("tc0", ExportCons "Monad" [ExportVar "a"])
      , ("m", ExportCons "StateT" [ExportVar "b", ExportVar "a", ExportVar "c"])
      , ("st" , ExportVar "b")
      ]
    , ExportCons "a" [ExportVar "c"]
    )
  , Benchmark
    "composeMonads"
    9
    "app(app(app((=<<), tc0), app(app((.), app(return, tc0)), app(app((=<<), tc1), f))), sm)"
    ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])
      , ("tc1", ExportCons "Monad" [ExportVar "d"])
      , ("sm" , ExportCons "c" [ExportCons "d" [ExportVar "a"]])
      , ("f"  , ExportFun (ExportVar "a") (ExportCons "d" [ExportVar "b"]))
      ]
    , ExportCons "c" [ExportCons "d" [ExportVar "b"]]
    )
  , Benchmark
    "traverseDAG"
    8
    "app(app(app(app(app(foldM, tc0), List@Foldable), f), Nil), app(app(map, fst), dag))"
    ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])
      , ( "f"
        , ExportFun
          (ExportCons "List" [ExportVar "a"])
          (ExportFun (ExportVar "b")
                     (ExportCons "c" [ExportCons "List" [ExportVar "a"]])
          )
        )
      , ( "dag"
        , ExportCons "List" [ExportCons "Pair" [ExportVar "b", ExportVar "a"]]
        )
      ]
    , ExportCons "c" [ExportCons "List" [ExportVar "a"]]
    )
  , Benchmark
    "extractEitherValues"
    8
    "app(app(app(app(mapM, tc1), tc0), app(app(either, Data.Function.id), Data.Function.id)), eithers)"
    ( [ ("tc0", ExportCons "Traversable" [ExportVar "d"])
      , ("tc1", ExportCons "Monad" [ExportVar "c"])
      , ( "eithers"
        , ExportCons
          "d"
          [ ExportCons
              "Either"
              [ExportCons "c" [ExportVar "b"], ExportCons "c" [ExportVar "b"]]
          ]
        )
      ]
    , ExportCons "c" [ExportCons "d" [ExportVar "b"]]
    )
  , Benchmark
    "iterateLines"
    7
    "app(app(app(evalStateT, tc0), st), app(app(zip, xs), app(lines, input)))"
    ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])
      , ( "st"
        , ExportCons
          "StateT"
          [ ExportCons
            "List"
            [ExportCons "Pair" [ExportVar "a", ExportCons "String" []]]
          , ExportVar "c"
          , ExportVar "b"
          ]
        )
      , ("xs"   , ExportCons "List" [ExportVar "a"])
      , ("input", ExportCons "String" [])
      ]
    , ExportCons "c" [ExportVar "b"]
    )
  , Benchmark
    "maybeToTransformer"
    5
    "app(app(MaybeT, tc0), app(app(return, tc0), mb))"
    ( [ ("tc0", ExportCons "Monad" [ExportVar "c"])
      , ("mb" , ExportCons "Maybe" [ExportVar "a"])
      ]
    , ExportCons "MaybeT" [ExportVar "c", ExportVar "a"]
    )
  , Benchmark
    "execThreads"
    8
    "app(app(fromMaybe, def), app(app(app(msum, Maybe@MonadPlus), List@Foldable), app(app(map, f), threads)))"
    ( [ ("f", ExportFun (ExportVar "b") (ExportCons "Maybe" [ExportVar "a"]))
      , ("threads", ExportCons "List" [ExportVar "b"])
      , ("def", ExportVar "a")
      ]
    , ExportVar "a"
    )
  , Benchmark
    "monadicUpdate"
    9
    ""
    ( [ ("tcarg0", ExportCons "Monad" [ExportVar "c"])
      , ("e"     , ExportCons "c" [ExportVar "a"])
      , ("upd"   , ExportFun (ExportVar "a") (ExportCons "c" [ExportVar "b"]))
      , ("mb"    , ExportCons "Maybe" [ExportVar "a"])
      ]
    , ExportCons "c" [ExportCons "Maybe" [ExportVar "b"]]
    )
  ]
