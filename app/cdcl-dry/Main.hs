module Main (main) where

import Data.Maybe (fromMaybe)
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Syntax.General
import qualified Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive as CNF
import Logic.Propositional.Syntax.Transformation.Claassical (dne)

ce :: Formula Full Int
ce = neg (neg (neg (neg (neg (neg (neg (neg (neg (neg (neg (⊥))))))))))) /\ neg ((neg (⊥) ==> (⊤) /\ Atom 0) /\ (neg (⊥) ==> (⊥) \/ Atom 0))

main :: IO ()
main = do
  print $ solve $ CNF [CNFClause ([] :: [Literal Int])]
  print $ solve $ CNF [CNFClause [Positive (0 :: Int)]]
  print $ solveVarId $ CNF [CNFClause []]
  print $ solveVarId $ CNF [CNFClause [Positive 0]]
  print $ solveVarId $ CNF [CNFClause [Negative 0]]
  print $ dne ce
  putStrLn "---------"
  print ce
  print $ solve $ CNF.fromFormulaFast ce
  putStrLn "---------"
  print $ dne ce
  print $ solve $ CNF.fromFormulaFast $ fromMaybe ce (dne ce)
  putStrLn "---------"
  print $ dne =<< dne ce
  print $ solve $ CNF.fromFormulaFast $ fromMaybe ce (dne =<< dne ce)
  putStrLn "---------"
  print $ dne =<< dne =<< dne ce
  print $ solve $ CNF.fromFormulaFast $ fromMaybe ce (dne =<< dne =<< dne ce)
