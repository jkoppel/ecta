{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List ( nub )
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.IO ( hFlush, stdout )

import Text.Pretty.Simple

import Data.Interned.Extended.HashTableBased as Interned
import Data.Memoization as Memoization
import Data.ECTA
import Data.Text.Extended.Pretty
import TermSearch
import Utility.Fixpoint

----------------------------------------------------------

printAllEdgeSymbols :: Node -> IO ()
printAllEdgeSymbols n = print $ nub $ crush (onNormalNodes $ \(Node es) -> map edgeSymbol es) n

reduceFully :: Node -> Node
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)

printCacheStatsForReduction :: Node -> IO ()
printCacheStatsForReduction n = do
    let n' = reducePartially n
    Text.putStrLn $ "Nodes: "        <> Text.pack (show (nodeCount   n'))
    Text.putStrLn $ "Edges: "        <> Text.pack (show (edgeCount   n'))
    Text.putStrLn $ "Max indegree: " <> Text.pack (show (maxIndegree n'))
#ifdef PROFILE_CACHES
    Memoization.printAllCacheMetrics
    Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Node))
    Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Edge))
    Text.putStrLn ""
#endif
    hFlush stdout


prettyPrintAllTerms :: Node -> IO ()
prettyPrintAllTerms n = pPrint $ map pretty $ map prettyTerm $ getAllTruncatedTerms n

main :: IO ()
main = prettyPrintAllTerms $ refold $ reduceFully $ filterType size6 baseType