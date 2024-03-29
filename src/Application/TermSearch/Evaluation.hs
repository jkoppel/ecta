{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module Application.TermSearch.Evaluation
    ( runBenchmark
    ) where

import           Control.Monad                  ( forM_ )
import           Data.Time                      ( diffUTCTime
                                                , getCurrentTime
                                                )
import           System.IO                      ( hFlush
                                                , stdout
                                                )
import           System.Timeout

import qualified Data.Bifunctor                as Bi
import qualified Data.Text                     as Text
import qualified Data.Text.IO                  as Text

import           Data.ECTA
import           Data.ECTA.Term

import           Application.TermSearch.Dataset
import           Application.TermSearch.TermSearch
import           Application.TermSearch.Type
import           Application.TermSearch.Utils

import qualified Data.Interned.Extended.HashTableBased as Interned
import           Data.Interned.Extended.HashTableBased ( cache )
import qualified Data.Memoization                      as Memoization
import           Data.Text.Extended.Pretty

printCacheStatsForReduction :: Node -> IO Node
printCacheStatsForReduction n = do
    let n' = reduceFully n
#ifdef PROFILE_CACHES
    Text.putStrLn $ "Nodes: "        <> Text.pack (show (nodeCount   n'))
    Text.putStrLn $ "Edges: "        <> Text.pack (show (edgeCount   n'))
    Text.putStrLn $ "Max indegree: " <> Text.pack (show (maxIndegree n'))
    Memoization.printAllCacheMetrics
    Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Node))
    Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Edge))
    Text.putStrLn ""
#endif
    hFlush stdout
    return n'

runBenchmark :: Benchmark -> AblationType -> Int -> IO ()
runBenchmark (Benchmark name size sol args res) ablation limit = do
    putStrLn $ "Running benchmark " ++ Text.unpack name

    let argNodes = map (Bi.bimap Symbol typeToFta) args
    let resNode  = typeToFta res

    start <- getCurrentTime
    _ <- timeout (limit * 10 ^ (6 :: Int)) $ forM_ [1..size] $ synthesize argNodes resNode
    end <- getCurrentTime
    print $ "Time: " ++ show (diffUTCTime end start)
    hFlush stdout

  where
    synthesize :: [Argument] -> Node -> Int -> IO ()
    synthesize argNodes resNode sz = do
      let anyArg   = Node (map (uncurry constArg) argNodes)
      let !filterNode = filterType (relevantTermsOfSize anyArg argNodes sz) resNode
      case ablation of
          NoReduction -> do
              prettyPrintAllTerms ablation (substTerm sol) filterNode
          NoOptimize  -> do
              prettyPrintAllTerms ablation (substTerm sol) filterNode
          _           -> do
#ifdef PROFILE_CACHES
              reducedNode <- printCacheStatsForReduction filterNode
#else
              reducedNode <- reduceFullyAndLog filterNode
#endif
              -- let reducedNode = reduceFully filterNode
              let foldedNode = refold reducedNode
              prettyPrintAllTerms ablation (substTerm sol) foldedNode
