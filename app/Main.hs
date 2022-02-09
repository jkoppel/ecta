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
import Data.ECTA.Term
import Data.Persistent.UnionFind
import Application.TermSearch.Evaluation

import Language.Dot.Pretty

----------------------------------------------------------

printAllEdgeSymbols :: Node -> IO ()
printAllEdgeSymbols n = print $ nub $ crush (onNormalNodes $ \(Node es) -> map edgeSymbol es) n

printCacheStatsForReduction :: Node -> IO ()
printCacheStatsForReduction n = do
    let n' = reducePartially [] n
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



main :: IO ()
main = do
    args <- getArgs
    runBenchmark (read $ head args)

    -- runEval

    -- test replicator issue
    -- putStrLn $ renderDot . toDot $ counterExample
    -- putStrLn $ renderDot . toDot $ reduceFully counterExample

    -- test reduction
    -- withFile "reduceError.pkl" ReadMode $ \hdl -> do
    --     contents <- BS.hGetContents hdl
    --     let mbNode = Aeson.decode contents :: Maybe Node
    --     case mbNode of
    --         Nothing -> error "cannot decode node"
    --         Just n -> putStrLn (renderDot $ toDot n) >> print (nodeCount n) >> (reduceFullyAndLog n) -- checkReductionTime n >>= print
    
    return ()