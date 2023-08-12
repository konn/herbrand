module Logic.Propositional.Classical.SAT.TableauxSpec (
  test_prove,
  test_solve,
) where

import Logic.Propositional.Classical.SAT.Tableaux
import Logic.Propositional.Classical.Syntax.TestUtils
import Test.Tasty

test_prove :: TestTree
test_prove = testGroup "prove" [testProverSemantics 10 128 prove]

test_solve :: TestTree
test_solve = testGroup "solve" [testSolverSemantics 10 128 solve]
