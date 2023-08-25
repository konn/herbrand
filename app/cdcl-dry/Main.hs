module Main (main) where

import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Syntax.General
import qualified Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive as CNF

fml :: Formula Full Int
fml = neg ((neg (⊥) ==> (⊤) /\ Atom 0) /\ (neg (⊥) ==> (⊥) \/ Atom 0))

main :: IO ()
main = do
  print fml
  let cnf = CNF.fromFormulaFast fml
  print cnf

  print $ solve cnf