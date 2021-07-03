{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List ( nub )
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.IO ( hFlush, stdout )

import Data.Interned.Extended.HashTableBased as Interned
import Data.Memoization as Memoization
import ECTA
import Pretty
import TermSearch

import Language.Dot

----------------------------------------------------------


printCacheStatsForReduction :: Node -> IO ()
printCacheStatsForReduction n = do
    --resetAllEctaCaches_BrokenDoNotUse
    let n' = reducePartially n
    Text.putStrLn $ "Nodes: "        <> Text.pack (show (nodeCount   n'))
    Text.putStrLn $ "Edges: "        <> Text.pack (show (edgeCount   n'))
    Text.putStrLn $ "Max indegree: " <> Text.pack (show (maxIndegree n'))
    Memoization.printAllCacheMetrics
    Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Node))
    Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Edge))
    Text.putStrLn ""
    hFlush stdout

main :: IO ()
main = do printCacheStatsForReduction $ withoutRedundantEdges size6