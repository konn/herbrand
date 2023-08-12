{-# LANGUAGE TypeApplications #-}

module Logic.Propositional.Syntax.NormalForm.Classical.ConjunctiveSpec (
  test_fromFormulaNaive,
  test_fromFormulaOrd,
  test_fromFormulaFast,
) where

import qualified Control.Foldl as L
import Data.Generics.Labels ()
import Logic.Propositional.Classical.SAT.BruteForce (Consistency (..))
import qualified Logic.Propositional.Classical.SAT.Tableaux as Tableaux
import Logic.Propositional.Classical.SAT.Types (SatResult (..))
import Logic.Propositional.Classical.SAT.Types hiding (Unsat)
import Logic.Propositional.Classical.Syntax.TestUtils (Arity, Size, genFormula, modelFor)
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import Test.Tasty
import Test.Tasty.Falsify

test_fromFormulaNaive :: TestTree
test_fromFormulaNaive = testGroup "fromFormulaNaive" [checkCNFSemantics 5 64 fromFormulaNaive]

test_fromFormulaOrd :: TestTree
test_fromFormulaOrd = testGroup "fromFormulaOrd" [checkCNFSemantics 10 32 fromFormulaOrd]

test_fromFormulaFast :: TestTree
test_fromFormulaFast =
  testGroup
    "fromFormulaFast"
    [ testProperty "preserves satisfiability" $ do
        (fml, consis) <- genFormula 5 32
        let cnf = fromFormulaFast fml
        info $ "CNF: " <> show cnf
        -- NOTE: The CNF produced by 'fast' method is considerablly large.
        -- This prevent us from using naïve brute-force solver; we use tableaux method,
        -- as it is slightly faster than brute-force.
        -- Other solvers relying on CNF representation, e.g. DPLL, cannot be used here
        -- as it relies on the correctness of CNF transformation itself!
        assert
          $ P.eq
          .$ ("original", fromConsis consis)
          .$ ("cnf", fromSat $ Tableaux.solve $ toFormula @Full cnf)
    ]

fromSat :: SatResult (Model v) -> S
fromSat Satisfiable {} = Sat
fromSat Unsat {} = Nosat

data S = Sat | Nosat
  deriving (Show, Eq, Ord)

fromConsis :: Consistency v -> S
fromConsis Consistent {} = Sat
fromConsis Tautology = Sat
fromConsis Inconsistent = Nosat

checkCNFSemantics :: Arity -> Size -> (Formula Full Int -> CNF Int) -> TestTree
checkCNFSemantics ar sz cnfy =
  testGroup
    "Behaves semantically correctly"
    [ testProperty
        "preserves semantics"
        $ do
          (fml, _consis) <- genFormula ar sz
          model <- gen $ modelFor $ L.fold L.hashSet fml
          let cnf = cnfy fml
          info $ "Model: " <> show model
          info $ "CNF: " <> show cnf
          assert
            $ P.eq
            .$ ("expected", eval model fml)
            .$ ("answer", eval model $ toFormula @Full cnf)
    ]
