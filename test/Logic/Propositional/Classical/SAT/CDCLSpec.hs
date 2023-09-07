{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeApplications #-}

module Logic.Propositional.Classical.SAT.CDCLSpec (test_solve, test_solveVarId, test_sudoku) where

import qualified Control.Foldl as L
import Control.Lens (folded, maximumOf, view, _3)
import Control.Lens.Extras (is)
import qualified Control.Lens.Getter as Lens
import Control.Monad ((<=<))
import qualified Data.ByteString.Lazy as LBS
import Data.Generics.Labels ()
import qualified Data.HashSet as HS
import Data.List (intercalate)
import qualified Data.Set as Set
import Logic.Propositional.Classical.SAT.BruteForce
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Classical.SAT.Format.DIMACS
import Logic.Propositional.Classical.SAT.Types (Model (..), SatResult (..), eval)
import Logic.Propositional.Classical.Syntax.TestUtils
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import Test.Falsify.Range (withOrigin)
import Test.Tasty
import Test.Tasty.Falsify
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

cdclOptions :: [(String, CDCLOptions)]
cdclOptions =
  [ ( intercalate "; " [decayLabel, vsidsType, restLabel]
    , CDCLOptions
        { restartStrategy = rest
        , decayFactor = decayFac
        , activateResolved = mVSIDS
        }
    )
  | (restLabel, rest) <-
      [ ("NoRestart", NoRestart)
      , ("ExponentialRestart(100, 2)", defaultExponentialRestart)
      , ("LubyRestart(100, 2)", defaultLubyRestart)
      ]
  , (vsidsType, mVSIDS) <- [("VSIDS", False), ("mVSIDS", True)]
  , (decayLabel, decayFac) <-
      [ ("Const Decay " <> show f, ConstantFactor f)
      | f <- [0.5, 0.75, 0.95]
      ]
        ++ [("Adaptive Decay (default)", defaultAdaptiveFactor)]
  ]

test_solve :: TestTree
test_solve =
  testGroup
    "solveWith"
    [ testGroup
      optName
      [ testGroup
          "CNF input"
          [ testProperty "Gives a correct decision" $ do
              cnf <- gen $ cnfGen 10 10 ((0, 10) `withOrigin` 5)
              collectCNF cnf
              let ans = solveWith opt cnf
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

              case solveWith opt cnf of
                Unsat -> discard
                Satisfiable m -> do
                  info $ "Given model: " <> show m
                  assert
                    $ P.eq
                    .$ ("expected", Just True)
                    .$ ("answer", eval m $ toFormula @Full cnf)
          ]
      , testGroup
          "solveWith . fromWithFree . fromFormulaFast"
          [ testSolverSemanticsWith
              projVar
              (fmap fromWithFree . fromFormulaFast)
              10
              128
              (solveWith opt)
          ]
      ]
    | (optName, opt) <- cdclOptions
    ]

decodeCNFFile :: FilePath -> IO (CNF Word)
decodeCNFFile =
  either error (pure . view _3) . parseCNFLazy <=< LBS.readFile

test_sudoku :: TestTree
test_sudoku =
  testGroup
    "Sudoku Regression Test"
    [ withResource (decodeCNFFile "data/tests/sudoku-9x9.cnf") mempty \cnf ->
        testGroup
          "9x9 (Satisfiable)"
          [ testCase optName do
            ans <- solveWith opt <$> cnf
            case ans of
              Unsat -> assertFailure "Must be satisfiable, but got Unsat!"
              Satisfiable m -> do
                HS.size (positive m) @?= 81
                let leftovers = HS.fromList [1 .. 46] `HS.difference` positive m
                assertBool ("Initial solution must be met, but following failed: " <> show (HS.toList leftovers)) (HS.null leftovers)
          | (optName, opt) <- cdclOptions
          ]
    ]

test_solveVarId :: TestTree
test_solveVarId =
  testGroup
    "solveVarIdWith"
    [ testGroup
      optName
      [ testGroup
          "CNF input"
          [ testGroup
              "Gives a correct decision"
              [ testProperty "Random" $ do
                  cnf <- gen $ fmap toEnum <$> cnfGen 10 10 ((0, 10) `withOrigin` 5)
                  collectCNF cnf
                  let ans = solveVarIdWith opt cnf
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
              , testGroup
                  "regressions"
                  [ testCase (show cnf) do
                    let ans = solveVarIdWith opt cnf
                    case classifyFormula $ toFormula @Full cnf of
                      Inconsistent -> ans @?= Unsat
                      _ ->
                        assertBool ("Satisfiable expected, but got: " <> show ans)
                          $ is #_Satisfiable ans
                  | cnf <- regressionCNFs
                  ]
              ]
          , testGroup
              "Gives a correct model"
              [ testProperty "Random" $ do
                  cnf <- gen $ fmap toEnum <$> cnfGen 10 10 ((0, 10) `withOrigin` 5)
                  collectCNF cnf

                  case solveVarIdWith opt cnf of
                    Unsat -> discard
                    Satisfiable m -> do
                      info $ "Given model: " <> show m
                      assert
                        $ P.eq
                        .$ ("expected", Just True)
                        .$ ("answer", eval m $ toFormula @Full cnf)
              , testGroup
                  "regressions"
                  [ testCase (show cnf) do
                    case solveVarIdWith opt cnf of
                      Unsat -> pure ()
                      Satisfiable m -> do
                        eval m (toFormula @Full cnf) @?= Just True
                  | cnf <- regressionCNFs
                  ]
              ]
          ]
      ]
    | (optName, opt) <- cdclOptions
    ]

regressionCNFs :: [CNF VarId]
regressionCNFs =
  [ CNF [[Negative 0, Negative 1], [Negative 0, Positive 1]]
  , CNF [[Negative 1, Negative 0], [Negative 1, Positive 0]]
  , CNF [[Negative 1], [Positive 1]]
  , CNF [[Negative 2], [Positive 2]]
  , CNF [CNFClause [Positive 1, Negative 0, Positive 1, Positive 1, Positive 1]]
  , CNF
      [ [Positive 1, Negative 0, Positive 1, Positive 1, Positive 1]
      , [Positive 0, Positive 0, Positive 0, Positive 0, Positive 1]
      ]
  , CNF
      [ [Positive 13]
      , [Positive 1]
      , [Negative 3, Positive 1]
      , [Negative 3, Positive 0]
      , [Positive 3, Negative 1, Negative 0]
      , [Negative 5, Negative 1, Positive 3]
      , [Positive 5, Positive 1]
      , [Positive 5, Negative 3]
      , [Negative 7, Negative 1, Positive 0]
      , [Positive 7, Positive 1]
      , [Positive 7, Negative 0]
      , [Negative 9, Negative 1, Positive 7]
      , [Positive 9, Positive 1]
      , [Positive 9, Negative 7]
      , [Negative 11, Positive 5]
      , [Negative 11, Positive 9]
      , [Positive 11, Negative 5, Negative 9]
      , [Negative 13, Positive 1]
      , [Negative 13, Negative 11]
      , [Positive 13, Negative 1, Positive 11]
      ]
  , CNF [[Negative 5], [Positive 1], [Negative 3, Positive 1], [Negative 3, Positive 0], [Positive 3, Negative 1, Negative 0], [Negative 5, Negative 3], [Negative 5, Negative 1], [Positive 5, Positive 3, Positive 1]]
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
