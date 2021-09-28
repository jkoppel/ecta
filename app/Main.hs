{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List ( nub )
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.IO ( hFlush, stdout )
import System.Environment (getArgs)

import Data.ECTA
import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Term
import Data.Interned.Extended.HashTableBased as Interned
import Data.Memoization as Memoization
import Data.Persistent.UnionFind
import TermSearch
import Data.ECTA.Internal.ECTA.Operations as Operations
import Data.ECTA.Internal.Paths
import qualified Data.Vector as Vector
import Data.Monoid (getFirst, First(..))
import Data.ECTA.Internal.ECTA.Type

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
    -- mapM_ runBenchmark benchmarks
    benchStr <- getArgs
    let bench = read (head benchStr) :: Benchmark
    runBenchmark bench

    -- let n00 = Node [mkEdge "->" [theArrowNode, pairType tau tau, pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [1,1], path [2]]])]
    -- let n01 = Node [mkEdge "->" [theArrowNode, pairType tau (pairType (listType tau) (pairType tau tau)), pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,1], path [2]]])]
    -- let n02 = Node [mkEdge "->" [theArrowNode, pairType (pairType (listType tau) (pairType tau tau)) (pairType tau tau), pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [1,1], path [2]]])]
    -- let n03 = Node [mkEdge "->" [theArrowNode, pairType (pairType (listType tau) (pairType tau tau)) (pairType (listType tau) (pairType tau tau)), pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [1,1], path [2]]])]
    -- let n04 = Node [mkEdge "->" [theArrowNode, pairType (pairType (listType tau) (pairType tau tau)) tau, pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [2]]])]
    -- let n10 = Node [mkEdge "->" [theArrowNode, pairType (pairType (listType tau) (pairType tau tau)) tau, pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [1,1], path [2]]])]
    -- let n11 = Node [mkEdge "->" [theArrowNode, pairType (listType tau) (pairType tau tau), pairType (pairType (listType tau) (pairType tau tau)) (pairType (listType tau) (pairType tau tau))] (mkEqConstraints [[path [1,0], path [1,1], path [2]]])]
    -- let n12 = Node [mkEdge "->" [theArrowNode, pairType (pairType (listType tau) (pairType tau tau)) tau, pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [1,1], path [2]]])]
    -- let n13 = Node [mkEdge "->" [theArrowNode, pairType (pairType (listType tau) (pairType tau tau)) (pairType tau tau), pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [1,1], path [2]]])]
    -- let n14 = Node [mkEdge "->" [theArrowNode, pairType tau (pairType (listType tau) (pairType tau tau)), pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,1], path [2]]])]
    -- let n15 = Node [mkEdge "->" [theArrowNode, pairType (pairType (listType tau) (pairType tau tau)) tau, pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [2]]])]
    -- let n16 = Node [mkEdge "->" [theArrowNode, pairType (pairType tau tau) (pairType (listType tau) (pairType tau tau)), pairType (listType tau) (pairType tau tau)] (mkEqConstraints [[path [1,0], path [1,1], path [2]]])]
    -- let n = Operations.intersect (Operations.union [n00, n01, n02, n03, n04]) (Operations.union [n10, n11, n12, n13, n14, n15, n16])
    -- print n
    -- let n1 = (Node [(Edge "var2" []),(Edge "var1" []),(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "var1" [])]),(Node [(Edge "var2" [])])]),(Edge "Pair" [(Node [(Edge "var1" [])]),(Node [(Edge "var1" [])])]),(Edge "var3" []),(Edge "var4" []),(Edge "->" [(Node [(Edge "(->)" [])]),tau,tau]),(Edge "List" [tau]),(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),tau,(Node [(Edge "->" [(Node [(Edge "(->)" [])]),tau,tau])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),tau,(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [tau])]),tau])])])])] EqConstraints {getEclasses = [PathEClass' {getPathTrie = PathTrie $ Vector.fromList [EmptyPathTrie,PathTrieSingleChild 1 TerminalPathTrie,PathTrieSingleChild 2 (PathTrieSingleChild 1 (PathTrieSingleChild 0 TerminalPathTrie))], getOrigPaths = [Path [1,1],Path [2,2,1,0]]},PathEClass' {getPathTrie = PathTrie $ Vector.fromList [EmptyPathTrie,PathTrieSingleChild 2 (PathTrie $ Vector.fromList [EmptyPathTrie,TerminalPathTrie,TerminalPathTrie]),PathTrie $ Vector.fromList [EmptyPathTrie,TerminalPathTrie,PathTrieSingleChild 2 TerminalPathTrie]], getOrigPaths = [Path [1,2,1],Path [1,2,2],Path [2,1],Path [2,2,2]]}]}),(Edge "Pair" [tau,tau]),(mkEdge "->" [(Node [(Edge "(->)" [])]),tau,(Node [(Edge "->" [(Node [(Edge "(->)" [])]),tau,(Node [(Edge "Pair" [tau,tau])])])])] EqConstraints {getEclasses = [PathEClass' {getPathTrie = PathTrie $ Vector.fromList [EmptyPathTrie,TerminalPathTrie,PathTrieSingleChild 2 (PathTrieSingleChild 0 TerminalPathTrie)], getOrigPaths = [Path [1],Path [2,2,0]]},PathEClass' {getPathTrie = PathTrieSingleChild 2 (PathTrie $ Vector.fromList [EmptyPathTrie,TerminalPathTrie,PathTrieSingleChild 1 TerminalPathTrie]), getOrigPaths = [Path [2,1],Path [2,2,1]]}]}),(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Pair" [tau,tau])]),tau] EqConstraints {getEclasses = [PathEClass' {getPathTrie = PathTrie $ Vector.fromList [EmptyPathTrie,PathTrieSingleChild 0 TerminalPathTrie,TerminalPathTrie], getOrigPaths = [Path [1,0],Path [2]]}]}),(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "Pair" [tau,tau])]),tau] EqConstraints {getEclasses = [PathEClass' {getPathTrie = PathTrie $ Vector.fromList [EmptyPathTrie,PathTrieSingleChild 1 TerminalPathTrie,TerminalPathTrie], getOrigPaths = [Path [1,1],Path [2]]}]}),(mkEdge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),tau,(Node [(Edge "->" [(Node [(Edge "(->)" [])]),tau,tau])])])]),(Node [(Edge "->" [(Node [(Edge "(->)" [])]),tau,(Node [(Edge "->" [(Node [(Edge "(->)" [])]),(Node [(Edge "List" [tau])]),tau])])])])] EqConstraints {getEclasses = [PathEClass' {getPathTrie = PathTrie $ Vector.fromList [EmptyPathTrie,PathTrie $ Vector.fromList [EmptyPathTrie,TerminalPathTrie,PathTrieSingleChild 2 TerminalPathTrie],PathTrie $ Vector.fromList [EmptyPathTrie,TerminalPathTrie,PathTrieSingleChild 2 TerminalPathTrie]], getOrigPaths = [Path [1,1],Path [1,2,2],Path [2,1],Path [2,2,2]]},PathEClass' {getPathTrie = PathTrie $ Vector.fromList [EmptyPathTrie,PathTrieSingleChild 2 (PathTrieSingleChild 1 TerminalPathTrie),PathTrieSingleChild 2 (PathTrieSingleChild 1 (PathTrieSingleChild 0 TerminalPathTrie))], getOrigPaths = [Path [1,2,1],Path [2,2,1,0]]}]})])
    -- let n2 = (Node [(Edge "Pair" [(Node [(Edge "var2" [])]),(Node [(Edge "var2" [])])])])
    -- print $ Operations.intersect n1 n2

    -- let firstNode = getFirst $ crush (\case Mu x -> First (Just x)
    --                                         _    -> First Nothing) testNode
    -- case firstNode of
    --     Nothing -> putStrLn "no first found"
    --     Just x  -> print $ Operations.unfoldRec x
    -- print $ Operations.intersect testNode1 testNode2
    -- print $ Operations.intersect testNode1 testNode2