{-# OPTIONS_GHC -fplugin CCTP.Plugin -fno-max-valid-hole-fits #-}
module Test (main) where

import TestConstraint
import Prelude (Bool(..), putStrLn, undefined, Eq((==)), Int, reverse)

s :: (TestConstraint a, Eq a) => a -> Bool -> Bool
s = undefined

f :: Bool -> Bool -> Bool
f = undefined

eql :: Eq a => [a] -> [a] -> Bool
eql = _

--prop_reverse :: [Int] -> Bool
--prop_reverse xs = _
-- prop_reverse xs = xs == reverse (reverse xs)



main = putStrLn "hello, ecta"
