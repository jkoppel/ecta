module Main where

import Data.List ( nub )

import Data.Interned.Extended.HashTableBased
import Data.Memoization
import ECTA
import TermSearch

import Language.Dot

----------------------------------------------------------

main :: IO ()
main = do let g = reducePartially $ filterType size4 baseType
          print $ nodeCount g
          print $ edgeCount g
{-          print =<< getAllCacheMetrics
          let c = cache @Edge
          print =<< getMetrics c
          let c = cache @Node
          print =<< getMetrics c
-}