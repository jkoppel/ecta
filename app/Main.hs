module Main where

import Data.List ( nub )

import Data.Interned.Extended.HashTableBased
import Data.Memoization
import Data.Maybe ( fromJust )
import ECTA
import TermSearch
import DbOpt

import Language.Dot

----------------------------------------------------------

main :: IO ()
main = do let g = fromJust $ rewrite tpch3
          print $ nodeCount g
          print $ edgeCount g
{-          print =<< getAllCacheMetrics
          let c = cache @Edge
          print =<< getMetrics c
          let c = cache @Node
          print =<< getMetrics c
-}
