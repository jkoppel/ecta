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

import           Data.ECTA
import           Data.ECTA.Term

import           Application.TermSearch.Dataset
import           Application.TermSearch.TermSearch
import           Application.TermSearch.Type
import           Application.TermSearch.Utils

runBenchmark :: Benchmark -> AblationType -> IO ()
runBenchmark (Benchmark name depth sol args res) ablation = do
    start <- getCurrentTime
    putStrLn $ "Running benchmark " ++ Text.unpack name
    let argNodes = map (Bi.bimap Symbol typeToFta) args
    let resNode  = typeToFta res
    let anyArg   = Node (map (uncurry constArg) argNodes)
    let
        !filterNode = filterType
            (relevantTermsUptoK anyArg argNodes depth)
            resNode

    _ <- timeout (300 * 10 ^ (6 :: Int)) $ do
        case ablation of
            NoReduction -> do
                prettyPrintAllTerms ablation (substTerm sol) filterNode
            _           -> do
                reducedNode <- reduceFullyAndLog filterNode
                -- let reducedNode = reduceFully filterNode
                let foldedNode = refold reducedNode
                prettyPrintAllTerms ablation (substTerm sol) foldedNode

    end <- getCurrentTime
    print $ "Time: " ++ show (diffUTCTime end start)
    hFlush stdout

runEval :: IO ()
runEval = undefined -- mapM_ runBenchmark hoogleplusBenchmarks
