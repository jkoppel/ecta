{-# OPTIONS_GHC -fplugin CCTP.Plugin -fno-max-valid-hole-fits #-}
module Test (main) where

import TestConstraint
import Prelude (Bool(..), not, putStrLn, undefined, Eq)

s :: (TestConstraint a, Eq a) => a -> Bool -> Bool
s = undefined

f :: Bool -> Bool -> Bool
f = undefined

h :: Bool -> Bool
h = _



main = putStrLn "hello, ecta"