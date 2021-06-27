module Main where

import Data.List ( nub )

import Data.Interned.Extended.HashTableBased
import Data.Memoization
import ECDFTA
import TermSearch

import Language.Dot

----------------------------------------------------------

main :: IO ()
main = do print $ nodeCount $ reducePartially $ filterType uptoSize6UniqueRep baseType
          print =<< getAllCacheMetrics
          let c = cache @Edge
          print =<< getMetrics c
          let c = cache @Node
          print =<< getMetrics c
