{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Logic.Propositional.Classical.Syntax.TestUtils (
  fullFormula,
  testProverSemantics,
  genFormula,
  testSolverSemantics,
) where

import qualified Control.Foldl as L
import Data.Maybe
import Logic.Propositional.Classical.SAT.BruteForce
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Syntax.General
import Test.Falsify.Generator
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import qualified Test.Falsify.Range as R
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify

type Size = Word

type Arity = Word

fullFormula ::
  -- | Number of variables
  Arity ->
  -- | Size parameter
  Size ->
  Gen (Formula Full Int)
fullFormula vars = go
  where
    baseCases =
      [ (1, pure $ Bot NoExtField)
      , (1, pure $ Top NoExtField)
      , (vars, Atom <$> int (R.between (0, fromIntegral vars - 1)))
      ]
    go !sz
      | sz <= 0 = frequency baseCases
      | otherwise =
          frequency $
            map
              (1,)
              [ Not NoExtField <$> go (sz - 1)
              , Impl NoExtField <$> go (sz `quot` 2) <*> go (sz `quot` 2)
              , (:/\) <$> go (sz `quot` 2) <*> go (sz `quot` 2)
              , (:\/) <$> go (sz `quot` 2) <*> go (sz `quot` 2)
              ]

genFormula :: Arity -> Size -> Property (Formula Full Int, Consistency Int)
genFormula ar sz = do
  arity <- gen $ integral $ R.between (1, ar)
  collect "arity" [arity]

  size <- gen $ integral $ R.between (1, sz)
  collect "size" [size]

  phi <- gen $ fullFormula arity size
  collect
    "# of maximum occurrence"
    [ L.fold
        ( L.premap (,1 :: Int) $
            L.fold (fromMaybe 0 <$> L.maximum) <$> L.foldByKeyMap L.sum
        )
        phi
    ]
  let consis = classifyFormula phi
  label
    "consistency"
    [ case consis of
        Tautology -> "Tautology"
        Consistent {} -> "Satsifiable"
        Inconsistent -> "Unsatisfiable"
    ]
  pure (phi, consis)

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
            assert $
              P.satisfies
                ("Refuted", \case Refuted {} -> True; _ -> False)
                .$ ("answer", ans)
    , testProperty "gives a correct counterexample" $ do
        (phi, consis) <- genFormula vs sz
        let phi' = case consis of
              Tautology -> Not NoExtField phi
              _ -> phi
        info $ "Refutable formula: " <> show phi'
        case prove phi' of
          Proven -> testFailed "Expected a counterexample, but got Provable"
          Refuted m -> do
            info $ "Given counterexample: " <> show m
            assert $
              P.eq
                .$ ("expected", Just False)
                .$ ("answer", eval m phi')
    ]

testSolverSemantics ::
  Arity ->
  Size ->
  (Formula Full Int -> SatResult (Model Int)) ->
  TestTree
testSolverSemantics vs sz solver =
  testGroup
    "behaves sematically correctly"
    [ testProperty "Gives a correct answer" $ do
        (phi, consis) <- genFormula vs sz
        let ans = solver phi
        case consis of
          Inconsistent ->
            assert $
              P.eq .$ ("expected", Unsat) .$ ("answer", ans)
          _ ->
            assert $
              P.satisfies
                ("Satisfiable", \case Satisfiable {} -> True; _ -> False)
                .$ ("answer", ans)
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
              Inconsistent -> Not NoExtField phi
              _ -> phi
        info $ "Satsifiable Formula: " <> show phi'
        case solver phi' of
          Unsat -> testFailed "Expected Satisfiable, but got Unsat"
          Satisfiable m -> do
            info $ "Given model: " <> show m
            assert $
              P.eq
                .$ ("expected", Just True)
                .$ ("answer", eval m phi')
    ]
