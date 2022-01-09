module Minimization where

import Control.Monad ( guard )
import System.Timeout ( timeout )
import Data.List ( subsequences )
import Data.Aeson ( encode )
import qualified Data.ByteString.Lazy as B
import System.IO ( withFile, IOMode(..) )

import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.ECTA.Operations
import Utility.Fixpoint
import Language.Dot.Pretty
import Data.ECTA

-- | drop edges bottom up
shrinkNode :: Node -> [Node]
shrinkNode (Node es) = do 
  es' <- mapM shrinkEdge es
  es'' <- dropEdges es'
  return (Node es'')
  where
    dropEdges :: [Edge] -> [[Edge]]
    dropEdges [e] = return [e]
    dropEdges es = do
      es' <- subsequences es
      guard (es' /= [] && es' /= es)
      return es'
shrinkNode n = return n

subnodes :: Node -> [Node]
subnodes (Node es) = concatMap edgeChildren es
subnodes _ = []

shrinkEdge :: Edge -> [Edge]
shrinkEdge e = do
  children <- mapM shrinkNode (edgeChildren e)
  return $ mkEdge (edgeSymbol e) children (edgeEcs e)
    
minReductionFail :: Node -> IO Node
minReductionFail n = do
  res <- checkReductionTime n
  case res of
    Just n' -> return n'
    Nothing -> do
      -- recurse into the subnodes
      timeoutNode <- firstFail (subnodes n)
      case timeoutNode of
        Just n' -> minReductionFail n'
        Nothing -> do
          putStrLn "shrinking"
          res <- firstFail (shrinkNode n)
          let resNode = case res of
                          Just n' -> n'
                          Nothing -> n
          withFile "graph.pkl" WriteMode $ \hdl -> B.hPut hdl (encode resNode)
          putStrLn $ "minimized node:\n" ++ renderDot (toDot resNode)
          -- return resNode
          error "found minimized node"

  where
    firstFail :: [Node] -> IO (Maybe Node)
    firstFail [] = return Nothing
    firstFail (nd:ns) = do
      res <- checkReductionTime nd
      case res of
        Just _ -> firstFail ns
        Nothing -> putStrLn "reduction failed" >> return (Just nd)

    checkReductionTime :: Node -> IO (Maybe Node)
    checkReductionTime n = do
      timeout (30 * 10^6) $ do
        let n' = reducePartially n
        print (nodeIdentity n')
        return n'