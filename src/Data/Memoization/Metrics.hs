module Data.Memoization.Metrics (
    CacheMetrics(..)
  ) where

----------------------------------------------------------

data CacheMetrics = CacheMetrics { queryCount :: {-# UNPACK #-} !Int
                                 , missCount  :: {-# UNPACK #-} !Int
                                 }
  deriving ( Eq, Ord, Show )