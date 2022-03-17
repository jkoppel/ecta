{-# OPTIONS_GHC -fplugin CCTP.Plugin #-}

module Main (main) where


f :: Bool -> Bool -> Bool
f = _

main :: IO ()
main = putStrLn "hello, ecta"