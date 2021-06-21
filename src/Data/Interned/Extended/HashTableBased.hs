{-# LANGUAGE TypeFamilies
           , FlexibleInstances
           , FlexibleContexts
           , BangPatterns #-}

module Data.Interned.Extended.HashTableBased
  ( Interned(..)
  , mkCache
  , Cache(..)
  , Id
  , intern
  ) where

import Control.Monad.ST ( stToIO )
import Data.Hashable
import qualified Data.HashTable.ST.Basic as HTBasic
import qualified Data.HashTable.IO as HT
import Data.IORef
import GHC.IO (unsafeDupablePerformIO, unsafePerformIO)


newtype Cache t = Cache { content :: HT.BasicHashTable (Description t) t }

mkCache :: Interned t => Cache t
mkCache = unsafePerformIO $ (Cache <$> HT.new)

type Id = Int

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
    let Cache ht = cache
    v <- HT.lookup ht dt
    case v of
      Nothing -> do i <- stToIO $ HTBasic.size ht
                    let t = identify i bt
                    HT.insert ht dt t
                    return t
      Just t  -> return t
  where
  !dt = describe bt