module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import Logic.Propositional.Classical.SAT.DPLL
import Logic.Propositional.Classical.SAT.Tableaux
import Test.Tasty (Timeout (..), localOption)

main :: IO ()
main = putStrLn "Not implemented yet"
