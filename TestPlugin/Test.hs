{-# OPTIONS_GHC -fplugin CCTP.Plugin -fno-max-valid-hole-fits #-}

module Main (main) where
import Data.Maybe (mapMaybe)

import Prelude (Bool(..), not, Eq(..), putStrLn)

f :: Bool -> Bool -> Bool
f = _

s :: Eq a => a -> Bool -> Bool
s = _

h :: Bool -> Bool
h = _


main = putStrLn "hello, ecta"