{-# OPTIONS_GHC -fplugin CCTP.Plugin -fno-max-valid-hole-fits #-}
module Test (main) where

import TestConstraint
import Prelude (Bool(..), not, putStrLn, undefined, id)

s :: TestConstraint a => a -> Bool -> Bool
s = undefined

f :: Bool -> Bool -> Bool
f = undefined

h :: Bool -> Bool
h = _

g :: a -> a
g = id

-- h = s TestConstraint[Bool] True


main = putStrLn "hello, ecta"