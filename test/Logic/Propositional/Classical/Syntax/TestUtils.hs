{-# LANGUAGE LambdaCase #-}

module Logic.Propositional.Classical.Syntax.TestUtils (
  fullFormula,
  testProverSemantics,
  genFormula,
  testSolverSemantics,
  modelFor,
  Arity,
  Size,
  testSolverSemanticsWith,
  literal,
  cnfGen,
  projModel,
) where

import Herbrand.Test
import Logic.Propositional.Classical.SAT.BruteForce
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Syntax.General
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify

testProverSemantics ::
  Arity ->
  Size ->
  (Formula Full Int -> ProofResult (Model Int)) ->
  TestTree
testProverSemantics vs sz prove =
  testGroup
    "behaves semantically correctly"
    [ testProperty "determines provability correctly" $ do
        (phi, consis) <- genFormula vs sz
        let ans = prove phi
        case consis of
          Tautology -> assert $ P.expect Proven .$ ("answer", ans)
          _ ->
            assert
              $ P.satisfies
                ("Refuted", \case Refuted {} -> True; _ -> False)
              .$ ("answer", ans)
    , testProperty "gives a correct counterexample" $ do
        (phi, consis) <- genFormula vs sz
        let phi' = case consis of
              Tautology -> neg phi
              _ -> phi
        info $ "Refutable formula: " <> show phi'
        case prove phi' of
          Proven -> testFailed "Expected a counterexample, but got Provable"
          Refuted m -> do
            info $ "Given counterexample: " <> show m
            assert
              $ P.eq
              .$ ("expected", Just False)
              .$ ("answer", eval m phi')
    ]

testSolverSemantics ::
  Arity ->
  Size ->
  (Formula Full Int -> SatResult (Model Int)) ->
  TestTree
testSolverSemantics = testSolverSemanticsWith Just id

testSolverSemanticsWith ::
  (Show v, Show x) =>
  (v -> Maybe Int) ->
  (Formula Full Int -> x) ->
  Arity ->
  Size ->
  (x -> SatResult (Model v)) ->
  TestTree
testSolverSemanticsWith projVar toInput vs sz solver =
  testGroup
    "behaves sematically correctly"
    [ testProperty "Gives a correct decision" $ do
        (phi, consis) <- genFormula vs sz
        let inp = toInput phi
        info $ "Direct Input: " <> show inp
        let ans = solver inp
        case consis of
          Inconsistent ->
            assert
              $ P.eq
              .$ ("expected", Unsat)
              .$ ("answer", projModel projVar <$> ans)
          _ ->
            assert
              $ P.satisfies
                ("Satisfiable", \case Satisfiable {} -> True; _ -> False)
              .$ ("answer", projModel projVar <$> ans)
    , testProperty "Gives a correct model" $ do
        (phi, consis) <- genFormula vs sz
        label
          "consistency"
          [ case consis of
              Tautology -> "Tautology"
              Consistent {} -> "Satsifiable"
              Inconsistent -> "Unsatisfiable"
          ]
        let phi' = case consis of
              Inconsistent -> neg phi
              _ -> phi
        info $ "Satsifiable Formula: " <> show phi'
        let inp = toInput phi'
        info $ "Direct Input: " <> show inp
        case solver inp of
          Unsat -> testFailed "Expected Satisfiable, but got Unsat"
          Satisfiable m -> do
            info $ "Given model: " <> show m
            assert
              $ P.eq
              .$ ("expected", Just True)
              .$ ("answer", eval (projModel projVar m) phi')
    ]
