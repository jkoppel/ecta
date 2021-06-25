{-# LANGUAGE TypeFamilies
           , FlexibleInstances
           , FlexibleContexts
           , BangPatterns #-}

module Data.Interned.Extended.HashTableBased
  ( Id
  , Cache(..)
  , mkCache
  , cacheSize
  , resetCache

  , Interned(..)
  , intern
  ) where

import Data.Hashable
import qualified Data.HashTable.IO as HT
import Data.IORef
import GHC.IO (unsafeDupablePerformIO, unsafePerformIO)

----------------------------------------------------------------------------------------------------------

--------------------
------- Caches
--------------------

type Id = Int

-- | Tried using the BasicHashtable size function to remove need for this IORef
-- ( see https://github.com/gregorycollins/hashtables/pull/68 ), but it was slower
data Cache t = Cache { fresh :: !(IORef Id), content :: !(HT.BasicHashTable (Description t) t) }

freshCache :: IO (Cache t)
freshCache = Cache <$> newIORef 0 <*> HT.new

mkCache :: Interned t => Cache t
mkCache = unsafePerformIO freshCache

cacheSize :: Cache t -> IO Int
cacheSize (Cache refI _) = readIORef refI

resetCache :: (Interned t) => Cache t -> IO ()
resetCache (Cache refI ht) = do
  writeIORef refI 0
  keys <- map fst <$> HT.toList ht
  mapM_ (\k -> HT.delete ht k) keys

--------------------
------- Interning
--------------------

class ( Eq (Description t)
      , Hashable (Description t)
      ) => Interned t where
  data Description t
  type Uninterned t
  describe :: Uninterned t -> Description t
  identify :: Id -> Uninterned t -> t
  cache        :: Cache t

intern :: Interned t => Uninterned t -> t
intern !bt = unsafeDupablePerformIO $ do
    let Cache refI ht = cache
    v <- HT.lookup ht dt
    case v of
      Nothing -> do i <- readIORef refI
                    let t = identify i bt
                    HT.insert ht dt t
                    writeIORef refI (i+1)
                    return t
      Just t  -> return t
  where
  !dt = describe bt
