module Main (main) where

import Logic.Propositional.Classical.SAT.CDCL

main :: IO ()
main = do
  print $ solve $ CNF [CNFClause ([] :: [Literal Int])]
  print $ solve $ CNF [CNFClause [Positive (0 :: Int)]]
  print $ solveVarId $ CNF [CNFClause []]
  print $ solveVarId $ CNF [CNFClause [Positive 0]]
