module Main where

import Agda.Main (runAgda)
import Compiler

main :: IO ()
main = runAgda [dkBackend]
