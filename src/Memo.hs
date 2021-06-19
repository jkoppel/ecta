-- | Quick-and-dirty, thread-unsafe, hash-based memoization.

module Memo (
    memoIO
  , memo
  , memo2
  ) where

import Data.IORef ( newIORef, readIORef, writeIORef )
import Data.Hashable ( Hashable )
import qualified Data.HashMap.Strict as HashMap
import System.IO.Unsafe (unsafePerformIO)

-----------------------------------------------------------------

memoIO :: (Eq a, Hashable a) => (a -> b) -> IO (a -> IO b)
memoIO f = do
    v <- newIORef HashMap.empty
    let f' x = do m <- readIORef v
                  case HashMap.lookup x m of
                    Nothing -> do let r = f x
                                  writeIORef v (HashMap.insert x r m)
                                  return r

                    Just r  -> return r
    return f'


memo :: (Eq a, Hashable a) => (a -> b) -> (a -> b)
memo f = let f' = unsafePerformIO (memoIO f)
         in \x -> unsafePerformIO (f' x)


memo2 :: (Eq a, Hashable a, Eq b, Hashable b) => (a -> b -> c) -> a -> b -> c
memo2 f = memo (memo . f)