{-# LANGUAGE CPP                   #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}

-- | Quick-and-dirty, thread-unsafe, hash-based memoization.

module Data.Memoization (
    MemoCacheTag(..)

  , resetAllCaches
#ifdef PROFILE_CACHES
  , getAllCacheMetrics
  , printAllCacheMetrics
#endif

  , memoIO
  , memo2IO
  , memo
  , memo2

  , memoIOCatchCycles
  , memoCatchCycles
  , memo2IOCatchCycles
  , memo2CatchCycles
  ) where

import Control.Monad.ST ( ST )
import Data.IORef ( IORef, newIORef, readIORef, writeIORef, modifyIORef )
import Data.Hashable ( Hashable )
import qualified Data.HashTable.IO as HT
import Data.List ( sort )
import Data.Text ( Text )
import qualified Data.Text    as Text
import qualified Data.Text.IO as Text
import GHC.Generics ( Generic )
import System.IO.Unsafe (unsafePerformIO)

import Data.HashTable.Extended
import Data.Memoization.Metrics ( CacheMetrics(CacheMetrics) )

import Data.Text.Extended.Pretty

-----------------------------------------------------------------

-------------------------------------------------------------
------------------ Caches and cache metrics -----------------
-------------------------------------------------------------

--------------
---- Memo cache
--------------

#ifdef PROFILE_CACHES
-- | Slightly ill-named. Tracks statistics and hash tables for all memo-caches under a given tag.
--   Multiple caches may be collapsed into the same tag.
data MemoCache = MemoCache { queryCount :: !(IORef Int)
                           , missCount  :: !(IORef Int)
                           , contents   :: ![AnyHashTable]
                           }

mkCache:: AnyHashTable -> IO MemoCache
mkCache ht = MemoCache <$> newIORef 0 <*> newIORef 0 <*> pure [ht]

resetCache :: MemoCache -> IO ()
resetCache c = do
  writeIORef (queryCount c) 0
  writeIORef (missCount  c) 0
  mapM_ resetHashTable (contents c)
#else
type MemoCache = ()
resetCache :: MemoCache -> IO ()
resetCache _ = return ()
#endif

bumpQueryCount :: MemoCache -> IO ()
#ifdef PROFILE_CACHES
bumpQueryCount c = modifyIORef (queryCount c) (+1)
#else
bumpQueryCount _ = return ()
#endif


bumpMissCount :: MemoCache -> IO ()
#ifdef PROFILE_CACHES
bumpMissCount c = modifyIORef (missCount c) (+1)
#else
bumpMissCount _ = return ()
#endif

--------------
---- Tags
--------------

data MemoCacheTag = NameTag Text
  deriving ( Eq, Ord, Show, Generic )

instance Hashable MemoCacheTag

mkInnerTag :: MemoCacheTag -> MemoCacheTag
mkInnerTag (NameTag t) = NameTag (t <> "-inner")

instance Pretty MemoCacheTag where
  pretty (NameTag t) = t

--------------
---- Global metrics store
--------------

memoCaches :: HT.BasicHashTable MemoCacheTag MemoCache
memoCaches = unsafePerformIO $ HT.new
{-# NOINLINE memoCaches #-}

initMetrics :: MemoCacheTag -> AnyHashTable -> IO MemoCache
#ifdef PROFILE_CACHES
initMetrics tag ht = do
    newC <- mkCache ht
    HT.mutate memoCaches
              tag
              (\case Nothing -> (Just newC, newC)
                     Just c  -> let c' = c { contents = ht : contents c}
                                 in (Just c', c'))
#else
initMetrics _ _ = return ()
#endif

resetAllCaches :: IO ()
#ifdef PROFILE_CACHES
resetAllCaches = HT.mapM_ (\(_, c) -> resetCache c) memoCaches
#else
resetAllCaches = return ()
#endif

#ifdef PROFILE_CACHES
getAllCacheMetrics :: IO [(MemoCacheTag, CacheMetrics)]
getAllCacheMetrics = HT.foldM (\l (k, v) -> getMetrics v >>= \v' -> return ((k, v') : l)) [] memoCaches
  where
    getMetrics :: MemoCache -> IO CacheMetrics
    getMetrics c = CacheMetrics <$> readIORef (queryCount c) <*> readIORef (missCount c)

printAllCacheMetrics :: IO ()
printAllCacheMetrics = do metrics <- getAllCacheMetrics
                          mapM_ (\(tag, cm)-> Text.putStrLn $ "(" <> pretty tag <> ")\t" <> pretty cm)
                                (sort metrics)
#endif

-------------------------------------------------------------
------------------------ Memoization ------------------------
-------------------------------------------------------------

------------- Normal variants -----------------

-- | TODO: Benchmark performance difference of taking `a -> IO b` vs. `a -> b`.
memoIO :: forall a b. (Eq a, Hashable a) => MemoCacheTag -> (a -> IO b) -> IO (a -> IO b)
memoIO tag f = do
    ht :: HT.BasicHashTable a b <- HT.new
    cache <- initMetrics tag (AnyHashTable ht)
    let f' x = do bumpQueryCount cache
                  v <- HT.lookup ht x
                  case v of
                    Nothing -> do bumpMissCount cache
                                  r <- f x
                                  HT.insert ht x r
                                  return r

                    Just r  -> return r
    return f'

-- Warning: Might be slower than memo2 because it wraps/unwraps a pair. Not yet benchmarked.
memo2IO :: (Eq a, Hashable a, Eq b, Hashable b) => MemoCacheTag -> (a -> b -> IO c) -> IO (a -> b -> IO c)
memo2IO tag f = curry <$> memoIO tag (uncurry f)

memo :: (Eq a, Hashable a) => MemoCacheTag -> (a -> b) -> (a -> b)
memo tag f = let f' = unsafePerformIO (memoIO tag (pure . f))
             in \x -> unsafePerformIO (f' x)

memo2 :: (Eq a, Hashable a, Eq b, Hashable b) => MemoCacheTag -> (a -> b -> c) -> a -> b -> c
memo2 tag f = memo tag (memo (mkInnerTag tag) . f)

------------- Cycle-catching variants -----------------

data ResultOrCycle a = Cycle | Result a

memoIOCatchCycles :: forall a b. (Eq a, Hashable a) => MemoCacheTag -> (a -> Text) -> (a -> IO b) -> IO (a -> IO b)
memoIOCatchCycles tag mkDebugStr f = do
    ht :: HT.BasicHashTable a (ResultOrCycle b) <- HT.new
    cache <- initMetrics tag (AnyHashTable ht)
    let f' x = do bumpQueryCount cache
                  v <- HT.lookup ht x
                  case v of
                    Nothing -> do bumpMissCount cache
                                  HT.insert ht x Cycle
                                  r <- f x
                                  HT.insert ht x (Result r)
                                  return r

                    Just r  -> case r of
                                 Cycle     -> error $ Text.unpack $ pretty tag
                                                                    <> ": Caught cycle when computing on input "
                                                                    <> mkDebugStr x
                                 Result r' -> return r'
    return f'

memo2IOCatchCycles :: forall a b c. (Eq a, Hashable a, Eq b, Hashable b)
                   => MemoCacheTag -> (a -> Text) -> (b -> Text) -> (a -> b -> IO c) -> IO (a -> b -> IO c)
memo2IOCatchCycles tag mkDebugStrA mkDebugStrB f =
  curry <$> memoIOCatchCycles tag
                              (\(a, b) -> mkDebugStrA a <> " " <> mkDebugStrB b)
                              (uncurry f)

memoCatchCycles :: (Eq a, Hashable a) => MemoCacheTag -> (a -> Text) -> (a -> b) -> (a -> b)
memoCatchCycles tag mkDebugStr f = let f' = unsafePerformIO (memoIOCatchCycles tag mkDebugStr (pure . f))
                                   in \x -> unsafePerformIO (f' x)

-- | This function uses pairs instead of currying because the cycle-detector must see both arguments simultaneously
memo2CatchCycles :: (Eq a, Hashable a, Eq b, Hashable b)
                 => MemoCacheTag -> (a -> Text) -> (b -> Text) -> (a -> b -> c) -> (a -> b -> c)
memo2CatchCycles tag mkDebugStrA mkDebugStrB f =
  let f' = unsafePerformIO (memo2IOCatchCycles tag mkDebugStrA mkDebugStrB (\a b -> pure $ f a b))
  in \x y -> unsafePerformIO (f' x y)