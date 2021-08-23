{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List ( nub )
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.IO ( hFlush, stdout )

import Data.ECTA
import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Term
import Data.Interned.Extended.HashTableBased as Interned
import Data.Memoization as Memoization
import Data.Persistent.UnionFind
import TermSearch

----------------------------------------------------------

printAllEdgeSymbols :: Node -> IO ()
printAllEdgeSymbols n = print $ nub $ crush (onNormalNodes $ \(Node es) -> map edgeSymbol es) n

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


getTermsNoOccursCheck :: Node -> [Term]
getTermsNoOccursCheck n = map (termFragToTruncatedTerm . fst) $
                          flip runEnumerateM (initEnumerationState n) $ do
                            enumerateOutUVar   (intToUVar 0)
                            getTermFragForUVar (intToUVar 0)



main :: IO ()
main = do
    -- start <- getCurrentTime
    -- let !filterNode = filterType (relevantTermsUptoK 6) baseType
    -- middle1 <- getCurrentTime
    -- print $ "Filter type time: " ++ show (diffUTCTime middle1 start)
    -- -- let !node = filterArgs filterNode 
    -- let !node = filterNode
    -- middle <- getCurrentTime
    -- print $ "Construction time: " ++ show (diffUTCTime middle start)
    -- prettyPrintAllTerms $ refold $ reduceFully node
    -- end <- getCurrentTime
    -- print $ "Reduction time: " ++ show (diffUTCTime end middle)
    -- putStrLn $ renderDot . toDot $ node
    mapM_ runBenchmark benchmarks