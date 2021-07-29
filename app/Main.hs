{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List ( nub )
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.IO ( hFlush, stdout )
import Data.Time
import Text.Pretty.Simple
import Language.Dot.Pretty

import Data.ECTA
import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Term
import Data.Persistent.UnionFind
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


getTermsNoOccursCheck :: Node -> [Term]
getTermsNoOccursCheck n = map (termFragToTruncatedTerm . fst) $
                          flip runEnumerateM (initEnumerationState n) $ do
                            _ <- enumerateOutUVar (intToUVar 0)
                            getTermFragForUVar    (intToUVar 0)

prettyPrintAllTerms :: Node -> IO ()
prettyPrintAllTerms n = let ts = map pretty $ map prettyTerm $ getAllTerms n
                        in do pPrint ts
                              print (length ts)
#ifdef PROFILE_CACHES
                              Memoization.printAllCacheMetrics
                              Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Node))
                              Text.putStrLn =<< (pretty <$> Interned.getMetrics (cache @Edge))
                              Text.putStrLn ""
#endif

main :: IO ()
main = do
    start <- getCurrentTime
    let !filterNode = filterType uptoSize6 baseType
    middle1 <- getCurrentTime
    print $ "Filter type time: " ++ show (diffUTCTime middle1 start)
    let !node = filterArgs filterNode 
    -- let !node = filterNode
    middle <- getCurrentTime
    print $ "Construction time: " ++ show (diffUTCTime middle middle1)
    prettyPrintAllTerms $ refold $ reduceFully node
    end <- getCurrentTime
    print $ "Reduction time: " ++ show (diffUTCTime end middle)
-- main = putStrLn $ renderDot . toDot