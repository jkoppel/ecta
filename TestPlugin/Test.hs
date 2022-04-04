{-# OPTIONS_GHC -fplugin CCTP.Plugin -fno-max-valid-hole-fits #-}

module Main (main) where
import Data.Maybe (mapMaybe)


f :: Bool -> Bool -> Bool
f = _

s :: Eq a => a -> Bool -> Bool
s = _

h :: Bool -> Bool
h = _

g :: (a -> Maybe b) -> [a] -> [b]
g = _

main :: IO ()
main = putStrLn "hello, ecta"