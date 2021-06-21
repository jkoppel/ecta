-- | Quick-and-dirty, thread-unsafe, hash-based memoization.

module Memo (
    memoIO
  , memo
  , memo2
  ) where

import Data.IORef ( newIORef, readIORef, writeIORef )
import Data.Hashable ( Hashable )
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.HashTable.IO as HT

-----------------------------------------------------------------

memoIO :: forall a b. (Eq a, Hashable a) => (a -> b) -> IO (a -> IO b)
memoIO f = do
    ht :: HT.BasicHashTable a b <- HT.new
    let f' x = do v <- HT.lookup ht x
                  case v of
                    Nothing -> do let r = f x
                                  HT.insert ht x r
                                  return r

                    Just r  -> return r
    return f'


memo :: (Eq a, Hashable a) => (a -> b) -> (a -> b)
memo f = let f' = unsafePerformIO (memoIO f)
         in \x -> unsafePerformIO (f' x)


memo2 :: (Eq a, Hashable a, Eq b, Hashable b) => (a -> b -> c) -> a -> b -> c
memo2 f = memo (memo . f)