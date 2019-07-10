module Main where

import Agda.Main (runAgda)
import Agda2Dk.Compiler

main :: IO ()
main = runAgda [dkBackend]
