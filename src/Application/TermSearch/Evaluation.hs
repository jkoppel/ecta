module Application.TermSearch.Evaluation
    ( runEval
    , runBenchmark
    ) where

import           Data.Time                      ( diffUTCTime
                                                , getCurrentTime
                                                )
import           System.IO                      ( hFlush
                                                , stdout
                                                )
import           System.Timeout

import qualified Data.Bifunctor                as Bi
import qualified Data.Text                     as Text
import Data.List (permutations)

import           Data.ECTA
import           Data.ECTA.Term

import           Application.TermSearch.Dataset
import           Application.TermSearch.TermSearch
import           Application.TermSearch.Type
import           Application.TermSearch.Utils

runBenchmark :: Mode -> Benchmark -> IO ()
runBenchmark mode (Benchmark name depth sol (args, res)) = do
    start <- getCurrentTime
    putStrLn $ "Running benchmark " ++ Text.unpack name
    let argNodes = map (Bi.bimap Symbol (exportTypeToFta mode)) args
    let resNode  = exportTypeToFta mode res
    let anyArg   = Node (map (uncurry constArg) argNodes)
    let
        !filterNode = filterType
            (union $ concatMap (relevantTermK mode anyArg True depth) (permutations argNodes))
            resNode

    timeout (600 * 10 ^ 6) $ do
        reducedNode <- reduceFullyAndLog filterNode
        -- let reducedNode = reduceFully filterNode
        let foldedNode = refold reducedNode
        -- let foldedNode = reducedNode
        prettyPrintAllTerms (substTerm sol) foldedNode

    end <- getCurrentTime
    print $ "Time: " ++ show (diffUTCTime end start)
    hFlush stdout

runEval :: IO ()
runEval = undefined -- mapM_ runBenchmark hoogleplusBenchmarks
