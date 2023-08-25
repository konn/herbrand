{-# LANGUAGE BlockArguments #-}
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
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

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
    [ testGroup
        "Gives a correct decision"
        [ testProperty "Random" $ do
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
              resl ->
                assert
                  $ P.satisfies
                    ("Satisfiable (" <> show resl <> ")", \case Satisfiable {} -> True; _ -> False)
                  .$ ("answer", projModel projVar <$> ans)
        , testGroup
            "Regressions"
            [ testCase "show phi" do
              let consis = classifyFormula phi
                  ans = solver $ toInput phi
              case consis of
                Inconsistent ->
                  (projModel projVar <$> ans) @?= Unsat
                resl ->
                  assertBool
                    ("Must be satisfiable (" <> show resl <> "), but got: " <> show ans)
                    $ case projModel projVar <$> ans of
                      Satisfiable {} -> True
                      _ -> False
            | phi <- testFormulae
            ]
        ]
    , testGroup
        "Gives a correct model"
        [ testProperty "Random" $ do
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
        , testGroup
            "Regressions"
            [ testCase "show phi" do
              let consis = classifyFormula phi
                  phi' = case consis of
                    Inconsistent -> neg phi
                    _ -> phi
              case solver $ toInput phi' of
                Unsat -> assertFailure "Expected Satisfiable, but got Unsat"
                Satisfiable m -> do
                  eval (projModel projVar m) phi' @?= Just True
            | phi <- testFormulae
            ]
        ]
    ]

testFormulae :: [Formula Full Int]
testFormulae =
  [ neg (⊥) /\ neg ((neg (⊥) ==> (⊤) /\ Atom 0) /\ (neg (⊥) ==> (⊥) \/ Atom 0))
  , neg (neg (neg (⊥))) /\ neg ((neg (⊥) ==> (⊤) /\ Atom 0) /\ (neg (⊥) ==> (⊥) \/ Atom 0))
  , neg (neg (neg (neg (neg (⊥))))) /\ neg ((neg (⊥) ==> (⊤) /\ Atom 0) /\ (neg (⊥) ==> (⊥) \/ Atom 0))
  , neg (neg (neg (neg (neg (neg (neg (neg (neg (neg (neg (⊥))))))))))) /\ neg ((neg (⊥) ==> (⊤) /\ Atom 0) /\ (neg (⊥) ==> (⊥) \/ Atom 0))
  ]
