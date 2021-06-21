module Main where

import Data.List ( nub )

import ECDFTA
import TermSearch

import Language.Dot
----------------------------------------------------------

main :: IO ()
main = print $ nodeCount $ reducePartially $ filterType uptoSize6UniqueRep baseType
