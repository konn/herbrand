{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}

module Logic.Propositional.Classical.SAT.CDCLSpec (test_solve, test_solveVarId) where

import qualified Control.Foldl as L
import Control.Lens (folded, maximumOf)
import qualified Control.Lens.Getter as Lens
import Data.Generics.Labels ()
import qualified Data.Set as Set
import Logic.Propositional.Classical.SAT.BruteForce
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Classical.SAT.Types (SatResult (..), eval)
import Logic.Propositional.Classical.Syntax.TestUtils
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import Test.Falsify.Range (withOrigin)
import Test.Tasty
import Test.Tasty.Falsify

test_solve :: TestTree
test_solve =
  testGroup
    "solve"
    [ testGroup
        "solve (CNF input)"
        [ testProperty "Gives a correct decision" $ do
            cnf <- gen $ cnfGen 10 10 ((0, 10) `withOrigin` 5)
            collectCNF cnf
            let ans = solve cnf
            case classifyFormula $ toFormula @Full cnf of
              Inconsistent ->
                assert
                  $ P.eq
                  .$ ("expected", Unsat)
                  .$ ("answer", ans)
              f ->
                assert
                  $ P.satisfies
                    ("Satisfiable (" <> show f <> ")", \case Satisfiable {} -> True; _ -> False)
                  .$ ("answer", ans)
        , testProperty "Gives a correct model" $ do
            cnf <- gen $ cnfGen 10 10 ((0, 10) `withOrigin` 5)
            collectCNF cnf

            case solve cnf of
              Unsat -> discard
              Satisfiable m -> do
                info $ "Given model: " <> show m
                assert
                  $ P.eq
                  .$ ("expected", Just True)
                  .$ ("answer", eval m $ toFormula @Full cnf)
        ]
    , testGroup
        "solve . fromWithFree . fromFormulaFast"
        [ testSolverSemanticsWith
            projVar
            (fmap fromWithFree . fromFormulaFast)
            10
            128
            solve
        ]
    ]

test_solveVarId :: TestTree
test_solveVarId =
  testGroup
    "solveVarId"
    [ testGroup
        "solveVarId (CNF input)"
        [ testProperty "Gives a correct decision" $ do
            cnf <- gen $ fmap toEnum <$> cnfGen 10 10 ((0, 10) `withOrigin` 5)
            collectCNF cnf
            let ans = solveVarId cnf
            case classifyFormula $ toFormula @Full cnf of
              Inconsistent ->
                assert
                  $ P.eq
                  .$ ("expected", Unsat)
                  .$ ("answer", ans)
              _ ->
                assert
                  $ P.satisfies
                    ("Satisfiable", \case Satisfiable {} -> True; _ -> False)
                  .$ ("answer", ans)
        , testProperty "Gives a correct model" $ do
            cnf <- gen $ fmap toEnum <$> cnfGen 10 10 ((0, 10) `withOrigin` 5)
            collectCNF cnf

            case solveVarId cnf of
              Unsat -> discard
              Satisfiable m -> do
                info $ "Given model: " <> show m
                assert
                  $ P.eq
                  .$ ("expected", Just True)
                  .$ ("answer", eval m $ toFormula @Full cnf)
        ]
    ]

collectCNF :: (Ord v) => CNF v -> Property ()
collectCNF cnf@(CNF cls) = do
  collect "# of clauses" [length cls]
  collect "# of summands" [maximumOf (folded . #_CNFClause . Lens.to length) cls]
  collect "arity" [Set.size $ L.fold L.set cnf]

projVar :: Int -> Maybe Int
projVar i
  | even i = Just $ i `quot` 2
  | otherwise = Nothing

fromWithFree :: WithFresh Int -> Int
fromWithFree (Var i) = 2 * i
fromWithFree (Fresh i) = 2 * fromIntegral i + 1
