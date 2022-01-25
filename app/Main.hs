{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List ( nub )
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.IO ( hFlush, stdout, withFile, IOMode(..) )
import System.Environment (getArgs)
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as BS
import System.Timeout (timeout)

import Data.ECTA
import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Term
import Data.ECTA.Paths
import Data.Interned.Extended.HashTableBased as Interned
import Data.Memoization as Memoization
import Data.Memoization.Metrics
import Data.Persistent.UnionFind
import Data.Text.Extended.Pretty
import TermSearch

import Language.Dot.Pretty
import TermSearch (loop2)

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
    -- benchStr <- getArgs
    -- let bench = read (head benchStr) :: Benchmark
    -- runBenchmark bench

    -- runBenchmark testBenchmark8

    -- test replicator issue
    -- putStrLn $ renderDot . toDot $ counterExample
    -- putStrLn $ renderDot . toDot $ reduceFully counterExample
    -- reduceFullyAndLog loop2
    prettyPrintAllTerms "" loop2
    
    -- test reduction
    -- mapM_ (\f ->
    --     withFile f ReadMode $ \hdl -> do
    --         putStrLn f
    --         contents <- BS.hGetContents hdl
    --         let mbNode = Aeson.decode contents :: Maybe (Node, Node)
    --         case mbNode of
    --             Nothing -> error "cannot decode node"
    --             Just (n, n') -> do
    --                 -- print $ reducePartially n
    --                 -- putStrLn (renderDot $ toDot n) >> print (nodeCount n) >> putStrLn (renderDot $ toDot n') >> print (nodeCount n') -- >> (putStrLn $ renderDot $ toDot $ reducePartially n') -- checkReductionTime n >>= print
    --                 -- putStrLn $ show $ nodeIdentity n
    --                 -- -- print (crush (\n -> [nodeIdentity n]) n)
    --                 let n1 = head $ crush (\n -> if nodeIdentity n == 56520 then [n] else []) n'
    --                 let n2 = head $ crush (\n -> if nodeIdentity n == 60184 then [n] else []) n'
    --                 -- let n3 = intersect n1 n2
    --                 putStrLn $ renderDot $ toDot n1
    --                 putStrLn $ renderDot $ toDot n2
    --                 -- putStrLn $ renderDot $ toDot n3
    --     ) ["smaller-round5-54742.pkl"]
    return ()