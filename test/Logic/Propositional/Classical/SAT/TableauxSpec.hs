{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Logic.Propositional.Classical.SAT.TableauxSpec (
  test_prove,
  test_solve,
) where

import qualified Control.Foldl as L
import Data.Maybe (fromMaybe)
import Logic.Propositional.Classical.SAT.BruteForce
import Logic.Propositional.Classical.SAT.Tableaux
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Classical.SAT.Types (eval)
import Logic.Propositional.Classical.Syntax.TestUtils
import Logic.Propositional.Syntax.General
import qualified Test.Falsify.Generator as F
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import qualified Test.Falsify.Property as F
import qualified Test.Falsify.Range as F
import Test.Tasty
import Test.Tasty.Falsify

test_prove :: TestTree
test_prove =
  testGroup
    "prove"
    [ testProperty "Gives a correct answer" $ do
        arity <- gen $ F.integral $ F.between (1, 5)
        F.collect "arity" [arity]

        size <- gen $ F.integral $ F.between (1, 128)
        F.collect "size" [size]

        phi <- gen $ fullFormula arity size
        F.collect
          "# of maximum occurrence"
          [ L.fold
              ( L.premap (,1 :: Int) $
                  L.fold (fromMaybe 0 <$> L.maximum) <$> L.foldByKeyMap L.sum
              )
              phi
          ]
        F.label
          "consistency"
          [ case classifyFormula phi of
              Tautology -> "Tautology"
              Consistent {} -> "Satsifiable"
              Inconsistent -> "Unsatisfiable"
          ]
        let ans = prove phi
        case classifyFormula phi of
          Tautology -> assert $ P.expect Proven .$ ("answer", ans)
          _ ->
            assert $
              P.satisfies
                ("Refuted", \case Refuted {} -> True; _ -> False)
                .$ ("answer", ans)
    , testProperty "Gives a correct counterexample" $ do
        arity <- gen $ F.integral $ F.between (1, 5)
        F.collect "arity" [arity]

        size <- gen $ F.integral $ F.between (1, 128)
        F.collect "size" [size]

        phi <- gen $ fullFormula arity size
        F.collect
          "# of maximum occurrence"
          [ L.fold
              ( L.premap (,1 :: Int) $
                  L.fold (fromMaybe 0 <$> L.maximum) <$> L.foldByKeyMap L.sum
              )
              phi
          ]
        let consis = classifyFormula phi

        F.label
          "consistency"
          [ case consis of
              Tautology -> "Tautology"
              Consistent {} -> "Satsifiable"
              Inconsistent -> "Unsatisfiable"
          ]
        let phi' = case consis of
              Tautology -> Not NoExtField phi
              _ -> phi
        info $ "Refutable Formula: " <> show phi'
        case prove phi' of
          Proven -> testFailed "Expected Refuted, but got Proven"
          Refuted m -> do
            info $ "Given counterexample: " <> show m
            assert $
              P.eq
                .$ ("expected", Just False)
                .$ ("answer", eval m phi')
    ]

test_solve :: TestTree
test_solve =
  testGroup
    "solve"
    [ testProperty "Gives a correct answer" $ do
        arity <- gen $ F.integral $ F.between (1, 5)
        F.collect "arity" [arity]

        size <- gen $ F.integral $ F.between (1, 128)
        F.collect "size" [size]

        phi <- gen $ fullFormula arity size
        F.collect
          "# of maximum occurrence"
          [ L.fold
              ( L.premap (,1 :: Int) $
                  L.fold (fromMaybe 0 <$> L.maximum) <$> L.foldByKeyMap L.sum
              )
              phi
          ]
        F.label
          "consistency"
          [ case classifyFormula phi of
              Tautology -> "Tautology"
              Consistent {} -> "Satsifiable"
              Inconsistent -> "Unsatisfiable"
          ]
        let ans = solve phi
        case classifyFormula phi of
          Inconsistent ->
            assert $
              P.eq .$ ("expected", Unsat) .$ ("answer", ans)
          _ ->
            assert $
              P.satisfies
                ("Satisfiable", \case Satisfiable {} -> True; _ -> False)
                .$ ("answer", ans)
    , testProperty "Gives a correct model" $ do
        arity <- gen $ F.integral $ F.between (1, 5)
        F.collect "arity" [arity]

        size <- gen $ F.integral $ F.between (1, 128)
        F.collect "size" [size]

        phi <- gen $ fullFormula arity size
        F.collect
          "# of maximum occurrence"
          [ L.fold
              ( L.premap (,1 :: Int) $
                  L.fold (fromMaybe 0 <$> L.maximum) <$> L.foldByKeyMap L.sum
              )
              phi
          ]
        let consis = classifyFormula phi

        F.label
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
        case solve phi' of
          Unsat -> testFailed "Expected Satisfiable, but got Unsat"
          Satisfiable m -> do
            info $ "Given model: " <> show m
            assert $
              P.eq
                .$ ("expected", Just True)
                .$ ("answer", eval m phi')
    ]
