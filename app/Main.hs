module Main where

import Data.List ( nub )

import ECDFTA
import TermSearch

----------------------------------------------------------

main :: IO ()
main = print $ length $ denotation $ reducePartially $ filterType size2 tau
