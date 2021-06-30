module Main where

import Criterion.Main

import ECTA
import TermSearch

-----------------------------------------------------------------------

-- | This exists, but doesn't give useful numbers because everything is cached
main = do
  defaultMain [
                bgroup "termsearch" [
                  bench "reduceTermSearchUpto6" $ whnf nodeCount $ reducePartially $ filterType uptoSize6UniqueRep tau
                ]
              ]