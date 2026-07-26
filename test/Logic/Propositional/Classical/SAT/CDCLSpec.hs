{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeApplications #-}

module Logic.Propositional.Classical.SAT.CDCLSpec (test_solve, test_solve_file, test_solveVarId, test_sudoku) where

import qualified Control.Foldl as L
import Control.Lens (both, folded, maximumOf, view, (%~), _3)
import Control.Lens.Extras (is)
import qualified Control.Lens.Getter as Lens
import Control.Monad ((<=<))
import qualified Data.ByteString.Lazy as LBS
import qualified Data.DList as DL
import Data.Foldable (foldMap')
import Data.Generics.Labels ()
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Hashable (Hashable)
import Data.List (intercalate)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import Data.Monoid (Ap (..))
import qualified Data.Set as Set
import Logic.Propositional.Classical.SAT.BruteForce
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Classical.SAT.Format.DIMACS
import Logic.Propositional.Classical.SAT.Types (Model (..), SatResult (..), eval)
import Logic.Propositional.Classical.Syntax.TestUtils
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import System.FilePath (takeFileName, (</>))
import System.FilePattern.Directory (getDirectoryFiles)
import qualified Test.Falsify.Generator as F
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import Test.Falsify.Range (withOrigin)
import Test.Tasty
import Test.Tasty.Falsify
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
#ifdef HERBRAND_CDCL_INSTRUMENTED
import Test.Tasty.HUnit (testCaseSteps)
#endif

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
      , ("LubyRestart(100)", defaultLubyRestart)
      ]
  , (vsidsType, mVSIDS) <- [("VSIDS", False), ("mVSIDS", True)]
  , (decayLabel, decayFac) <-
      [ ("Const Decay " <> show f, ConstantFactor f)
      | f <- [0.5, 0.75, 0.95]
      ]
        <> [("Adaptive Decay", defaultAdaptiveFactor)]
  ]

test_solve_file :: IO TestTree
test_solve_file = do
  uf20_91 <-
    mapM loadCNF
      =<< getDirectoryFiles "data/satlib/uf20-91-full" ["*.cnf"]
  pure $
    testGroup
      "solveWith (fixedInput)"
      [ testGroup
          optName
          [ testCase name do
              case solveWith opt cnf of
                Satisfiable model ->
                  eval model (toFormula @Full cnf) @?= Just True
                Unsat ->
                  assertFailure "Must be satisfiable, but got Unsat!"
          | (name, cnf) <- uf20_91
          ]
      | (optName, opt) <- cdclOptions
      ]
  where
    loadCNF fp = do
      cnf <- decodeCNFFile ("data/satlib/uf20-91-full" </> fp)
      pure (takeFileName fp, cnf)

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
                    assert $
                      P.eq
                        .$ ("expected", Unsat)
                        .$ ("answer", ans)
                  f ->
                    assert $
                      P.satisfies
                        ("Satisfiable (" <> show f <> ")", \case Satisfiable {} -> True; _ -> False)
                        .$ ("answer", ans)
            , testProperty "Gives a correct model" $ do
                cnf <- gen $ cnfGen 10 10 ((0, 10) `withOrigin` 5)
                collectCNF cnf

                case solveWith opt cnf of
                  Unsat -> discard
                  Satisfiable m -> do
                    info $ "Given model: " <> show m
                    complete <-
                      gen $
                        F.elem $
                          fromMaybe (NE.singleton m) $
                            NE.nonEmpty $
                              completedModels (L.fold L.hashSet cnf) m
                    assert $
                      P.eq
                        .$ ("expected", Just True)
                        .$ ("answer", eval complete $ toFormula @Full cnf)
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
    ( [ testGroup
          "threshold-1 restart regressions"
          [ testGroup
              restartName
              [ testCase "preserves roots and skips a non-unit learned assertion" $
                  assertSolverResult restartOptions restartWitnessCNF
              , testCase "reports UNSAT after a conflict and restart" $
                  solveVarIdWith restartOptions allBinaryTwoCNF @?= Unsat
              , testCase "retains contradictory-root behavior" $
                  solveVarIdWith restartOptions (CNF [[Positive 1], [Negative 1]]) @?= Unsat
              ]
          | (restartName, restart) <-
              [ ("ExponentialRestart(1, 2)", ExponentialRestart 1 2)
              , ("LubyRestart(1)", LubyRestart 1)
              ]
          , let restartOptions =
                  defaultOptions
                    { restartStrategy = restart
                    , activateResolved = False
                    }
          ]
      , testGroup
          "exhaustive normalized CNFs with at most three variables and three clauses"
          [ testCase strategyName $
              mapM_ (assertSolverResult options) exhaustiveSmallCNFs
          | (strategyName, strategy) <-
              [ ("NoRestart", NoRestart)
              , ("ExponentialRestart(1, 2)", ExponentialRestart 1 2)
              , ("LubyRestart(1)", LubyRestart 1)
              ]
          , let options = defaultOptions {restartStrategy = strategy}
          ]
      , testGroup
          "restart configuration"
          [ testCase "uses the standard Luby sequence" $
              map luby [0 .. 6] @?= [1, 1, 2, 1, 1, 2, 4]
          , testCase "default Luby constructor has threshold 100" $
              defaultLubyRestart @?= LubyRestart 100
          , testCase "default solver behavior remains no-restart" $
              restartStrategy defaultOptions @?= NoRestart
          ]
      , testGroup
          "watch occurrence regressions"
          [ testCase "handles opposite polarities in distinct buckets" $
              case solveVarIdWith defaultOptions mixedPolarityWatchCNF of
                Unsat -> assertFailure "mixed-polarity watch witness must be satisfiable"
                Satisfiable {} -> pure ()
          , testCase "moves watches through a long implication chain" $
              solveVarIdWith defaultOptions longWatchMoveCNF @?= Unsat
          , testCase "restores the unread bucket suffix after a conflict" $
              case solveVarIdWith defaultOptions watchSuffixRestoreCNF of
                Unsat -> assertFailure "watch-suffix restoration witness must be satisfiable"
                Satisfiable {} -> pure ()
          ]
      , testCase "solves sparse formulas by iterative pure-literal elimination" $ do
          case solveVarIdWith defaultOptions sparsePureLiteralCNF of
            Unsat -> assertFailure "sparse pure-literal witness must be satisfiable"
            Satisfiable model ->
              eval model (toFormula @Full sparsePureLiteralCNF) @?= Just True
          let genericCNF =
                fmap (fromIntegral . fromEnum) sparsePureLiteralCNF ::
                  CNF Word
          case solveWith defaultOptions genericCNF of
            Unsat -> assertFailure "generic pure-literal witness must be satisfiable"
            Satisfiable model ->
              eval model (toFormula @Full genericCNF) @?= Just True
      , testCase "falls back after partial pure-literal elimination" $
          solveVarIdWith defaultOptions sparsePureLiteralFallbackCNF @?= Unsat
      ]
        <> instrumentationTests
        <> [ testGroup
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
                               assert $
                                 P.eq
                                   .$ ("expected", Unsat)
                                   .$ ("answer", ans)
                             _ ->
                               assert $
                                 P.satisfies
                                   ("Satisfiable", \case Satisfiable {} -> True; _ -> False)
                                   .$ ("answer", ans)
                       , testCase "learns a singleton root first-UIP clause" $
                           case solveVarIdWith opt singletonUIPCNF of
                             Unsat -> assertFailure "Must learn root unit x0, but returned Unsat"
                             Satisfiable m ->
                               assertBool "Every model must assign x0 positively" $
                                 HS.member 0 $
                                   positive m
                       , testGroup
                           "regressions"
                           [ testCase (show cnf) do
                               let ans = solveVarIdWith opt cnf
                               case classifyFormula $ toFormula @Full cnf of
                                 Inconsistent -> ans @?= Unsat
                                 _ ->
                                   assertBool ("Satisfiable expected, but got: " <> show ans) $
                                     is #_Satisfiable ans
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
                               complete <-
                                 gen $
                                   F.elem $
                                     fromMaybe (NE.singleton m) $
                                       NE.nonEmpty $
                                         completedModels (L.fold L.hashSet cnf) m
                               assert $
                                 P.eq
                                   .$ ("expected", Just True)
                                   .$ ("answer", eval complete $ toFormula @Full cnf)
                       , testGroup
                           "regressions"
                           [ testCase (show cnf) do
                               case solveVarIdWith opt cnf of
                                 Unsat -> pure ()
                                 Satisfiable m -> do
                                   let models = completedModels (L.fold L.hashSet cnf) m
                                       modVals =
                                         filter ((/= Just True) . snd) $
                                           map ((,) <$> id <*> flip eval (toFormula @Full cnf)) models
                                   assertBool
                                     ( unlines
                                         [ "       expected: Just True"
                                         , "        but got: " <> show (map snd modVals)
                                         , "  partial model: " <> show m
                                         , " complete model: " <> show (map fst modVals)
                                         ]
                                     )
                                     $ null modVals
                           | cnf <- regressionCNFs
                           ]
                       ]
                   ]
               ]
           | (optName, opt) <- cdclOptions
           ]
    )

instrumentationTests :: [TestTree]
#ifdef HERBRAND_CDCL_INSTRUMENTED
instrumentationTests =
  [ testCase "instrumented root propagation preserves trail and scan invariants" do
      let (_, stats) =
            solveVarIdWithStats
              defaultOptions
              (CNF [[Positive 0], [Positive 2]])
      seedScanCount stats @?= 1
      postDrainScanCount stats @?= 0
      assignmentCount stats @?= trailAppendCount stats
      propagationEventCount stats @?= assignmentCount stats
      watchVisitCount stats @?= 0
  , testGroup
      "instrumented threshold-1 restarts"
      [ testCase restartName do
          let (_, stats) =
                solveVarIdWithStats
                  defaultOptions {restartStrategy = restart}
                  restartWitnessCNF
          assertBool "the threshold-1 witness must actually restart" $
            observedRestartCount stats > 0
          seedScanCount stats @?= 1
          postDrainScanCount stats @?= 0
          assignmentCount stats @?= trailAppendCount stats
          assertBool "the restart witness must exercise conflict analysis" $
            conflictCount stats > 0
      | (restartName, restart) <-
          [ ("ExponentialRestart(1, 2)", ExponentialRestart 1 2)
          , ("LubyRestart(1)", LubyRestart 1)
          ]
      ]
  , testCaseSteps "reports watch-structure stress counters" \step -> do
      let (mixedResult, mixedStats) = solveVarIdWithStats defaultOptions mixedPolarityWatchCNF
          (longResult, longStats) = solveVarIdWithStats defaultOptions longWatchMoveCNF
      step $ "mixed-polarity: " <> show mixedStats
      step $ "long-clause: " <> show longStats
      case mixedResult of
        Unsat -> assertFailure "mixed-polarity watch witness must be satisfiable"
        Satisfiable {} -> pure ()
      longResult @?= Unsat
      watchVisitCount mixedStats @?= 128
      watchMoveCount longStats @?= 126
      literalInspectionCount longStats @?= 252
  , testCase "exercises conflict-time watch-suffix restoration" $ do
      let (result, stats) = solveVarIdWithStats defaultOptions watchSuffixRestoreCNF
      case result of
        Unsat -> assertFailure "watch-suffix restoration witness must be satisfiable"
        Satisfiable {} -> pure ()
      assertBool "the restoration witness must encounter a conflict" $
        conflictCount stats > 0
  , testCase "traces reverse-trail first-UIP analysis with a nonzero target" $ do
      let (result, stats) =
            solveVarIdWithStats defaultOptions nonzeroTargetUIPCNF
      case result of
        Unsat -> assertFailure "first-UIP trace witness must be satisfiable"
        Satisfiable model ->
          eval model (toFormula @Full nonzeroTargetUIPCNF) @?= Just True
      analysisCount stats @?= 1
      analysisRootConflictCount stats @?= 0
      analysisConflictClauseVisitCount stats @?= 1
      analysisReasonClauseVisitCount stats @?= 1
      analysisConflictLiteralVisitCount stats @?= 3
      analysisReasonLiteralVisitCount stats @?= 3
      analysisTrailReadCount stats @?= 2
      analysisPivotCount stats @?= 2
      analysisMarkCount stats @?= 3
      analysisDuplicateMarkCount stats @?= 2
      analysisLearnedLiteralCount stats @?= 2
      analysisEpochClearCount stats @?= 1
      analysisLastTargetLevel stats @?= 1
      analysisLastPivotTrace stats
        @?= [Positive 2, Negative 1]
      analysisLastLearnedClause stats
        @?= [Positive 1, Positive 0]
  , testProperty "every bounded-random learned clause is entailed and asserting" $ do
      cnf <-
        gen $
          fmap toEnum
            <$> cnfGen 6 8 ((0, 6) `withOrigin` 4)
      let (_, stats) = solveVarIdWithStats defaultOptions cnf
          traces = analysisLearnedTrace stats
      collect "learned clauses" [length traces]
      assert $
        P.eq
          .$ ("expected", True)
          .$ ( "answer"
             , all (validLearnedTrace cnf) traces
             )
  , testCaseSteps "reports trail-suffix backtrack counters" \step -> do
      let (result, stats) =
            solveVarIdWithStats defaultOptions watchSuffixRestoreCNF
          (rootResult, rootStats) =
            solveVarIdWithStats defaultOptions restartWitnessCNF
          (restartResult, restartStats) =
            solveVarIdWithStats
              defaultOptions {restartStrategy = ExponentialRestart 1 2}
              restartWitnessCNF
          (noOpResult, noOpStats) =
            solveVarIdWithStats
              defaultOptions {restartStrategy = ExponentialRestart 1 2}
              allBinaryTwoCNF
      step $ "empty-root witness: " <> show stats
      step $ "root-prefix witness: " <> show rootStats
      step $ "restart witness: " <> show restartStats
      step $ "no-op restart witness: " <> show noOpStats
      case result of
        Unsat -> assertFailure "backtrack witness must be satisfiable"
        Satisfiable {} -> pure ()
      case rootResult of
        Unsat -> assertFailure "root-prefix witness must be satisfiable"
        Satisfiable {} -> pure ()
      case restartResult of
        Unsat -> assertFailure "restart witness must be satisfiable"
        Satisfiable {} -> pure ()
      noOpResult @?= Unsat
      assertBool "the witness must backtrack" $ backtrackCallCount stats > 0
      assertBool "the witness must undo assignments" $ backtrackClearedCount stats > 0
      backtrackBoundaryReadCount stats
        @?= backtrackCallCount stats - backtrackNoOpCount stats
      backtrackTrailReadCount stats @?= backtrackClearedCount stats
      backtrackValuationReadCount stats @?= 0
      backtrackValuationWriteCount stats @?= backtrackClearedCount stats
      backtrackQueueRestoreCount stats @?= backtrackClearedCount stats
      backtrackBoundaryProbeCount stats @?= 0
      ordinaryBacktrackCount stats @?= backtrackCallCount stats
      restartBacktrackCount stats @?= 0
      assertBool "the root-prefix witness must use an indexed boundary" $
        backtrackBoundaryReadCount rootStats > 0
      backtrackBoundaryReadCount rootStats
        @?= backtrackCallCount rootStats - backtrackNoOpCount rootStats
      backtrackTrailReadCount rootStats @?= backtrackClearedCount rootStats
      backtrackValuationReadCount rootStats @?= 0
      backtrackBoundaryProbeCount rootStats @?= 0
      assertBool "the threshold-1 witness must perform a restart rollback" $
        restartBacktrackCount restartStats > 0
      ordinaryBacktrackCount restartStats + restartBacktrackCount restartStats
        @?= backtrackCallCount restartStats
      backtrackBoundaryReadCount restartStats
        @?= backtrackCallCount restartStats - backtrackNoOpCount restartStats
      backtrackTrailReadCount restartStats
        @?= backtrackClearedCount restartStats
      backtrackValuationReadCount restartStats @?= 0
      backtrackValuationWriteCount restartStats
        @?= backtrackClearedCount restartStats
      backtrackQueueRestoreCount restartStats
        @?= backtrackClearedCount restartStats
      backtrackBoundaryProbeCount restartStats @?= 0
      seedScanCount restartStats @?= 1
      assertBool "the root-level restart witness must exercise a no-op rollback" $
        backtrackNoOpCount noOpStats > 0
      assertBool "the no-op witness must perform a restart" $
        restartBacktrackCount noOpStats > 0
      assertBool "the no-op witness must observe restart scheduling" $
        observedRestartCount noOpStats > 0
      seedScanCount noOpStats @?= 1
      backtrackBoundaryReadCount noOpStats
        @?= backtrackCallCount noOpStats - backtrackNoOpCount noOpStats
      backtrackTrailReadCount noOpStats @?= backtrackClearedCount noOpStats
      backtrackValuationReadCount noOpStats @?= 0
      backtrackValuationWriteCount noOpStats
        @?= backtrackClearedCount noOpStats
      backtrackQueueRestoreCount noOpStats
        @?= backtrackClearedCount noOpStats
      backtrackBoundaryProbeCount noOpStats @?= 0
  , testCase "bypasses CDCL state for sparse pure-literal formulas" $ do
      let (result, stats) = solveVarIdWithStats defaultOptions sparsePureLiteralCNF
      case result of
        Unsat -> assertFailure "sparse pure-literal witness must be satisfiable"
        Satisfiable model ->
          eval model (toFormula @Full sparsePureLiteralCNF) @?= Just True
      assignmentCount stats @?= 0
  , testCase "uses CDCL after partial pure-literal elimination stalls" $ do
      let (result, stats) =
            solveVarIdWithStats defaultOptions sparsePureLiteralFallbackCNF
      result @?= Unsat
      seedScanCount stats @?= 1
  ]
#else
instrumentationTests = []
#endif

assertSolverResult :: CDCLOptions -> CNF VarId -> IO ()
assertSolverResult options cnf =
  case (classifyFormula formula, solveVarIdWith options cnf) of
    (Inconsistent, actual) -> actual @?= Unsat
    (_, Unsat) -> assertFailure $ "Expected SAT, but got UNSAT for " <> show cnf
    (_, Satisfiable model) ->
      assertBool ("Returned model does not satisfy " <> show cnf) $
        all ((== Just True) . flip eval formula) $
          completedModels (L.fold L.hashSet cnf) model
  where
    formula = toFormula @Full cnf

restartWitnessCNF :: CNF VarId
restartWitnessCNF =
  CNF
    [ [Positive 0, Positive 1, Positive 2]
    , [Positive 0, Positive 1, Negative 2]
    , [Positive 3]
    , [Negative 3, Negative 1, Positive 4]
    , [Negative 3, Negative 1, Negative 4]
    ]

allBinaryTwoCNF :: CNF VarId
allBinaryTwoCNF =
  CNF
    [ [Positive 0, Positive 1]
    , [Positive 0, Negative 1]
    , [Negative 0, Positive 1]
    , [Negative 0, Negative 1]
    ]

mixedPolarityWatchCNF :: CNF VarId
mixedPolarityWatchCNF =
  CNF $
    [[Positive 0]]
      <> [[Positive 0, Positive i] | i <- [1 .. 64]]
      <> [[Negative 0, Positive i] | i <- [65 .. 128]]

longWatchMoveCNF :: CNF VarId
longWatchMoveCNF =
  CNF $
    [CNFClause [Negative 0]]
      <> [CNFClause [Positive i, Negative (i + 1)] | i <- [0 .. 126]]
      <> [CNFClause [Positive i | i <- [0 .. 127]]]

watchSuffixRestoreCNF :: CNF VarId
watchSuffixRestoreCNF =
  CNF
    [ [Positive 1, Positive 2]
    , [Positive 1, Positive 3]
    , [Positive 1, Positive 4]
    , [Positive 0, Negative 1]
    , [Positive 0, Negative 2]
    , [Positive 0, Positive 5]
    , [Positive 0, Positive 6]
    , [Positive 0, Positive 7]
    , [Positive 0, Positive 8]
    , [Positive 0, Positive 9]
    ]

#ifdef HERBRAND_CDCL_INSTRUMENTED
nonzeroTargetUIPCNF :: CNF VarId
nonzeroTargetUIPCNF =
  CNF
    [ [Positive 0, Positive 1, Positive 2]
    , [Positive 0, Positive 1, Negative 2]
    ]

validLearnedTrace ::
  CNF VarId ->
  ([Literal Word], Int, [Literal Word]) ->
  Bool
validLearnedTrace original (pivots, target, learned) =
  target >= 0
    && learnedClauseEntailed original learned
    && case (reverse pivots, learned) of
      (finalPivot : _, assertingLit : _) ->
        assertingLit == negateLiteral finalPivot
      _ -> False

learnedClauseEntailed :: CNF VarId -> [Literal Word] -> Bool
learnedClauseEntailed original learned =
  case classifyFormula $ toFormula @Full counterexample of
    Inconsistent -> True
    _ -> False
  where
    CNF originalClauses =
      fmap (fromIntegral . fromEnum) original
    counterexample =
      CNF $
        originalClauses
          <> map (CNFClause . pure . negateLiteral) learned

negateLiteral :: Literal a -> Literal a
negateLiteral = \case
  Positive var -> Negative var
  Negative var -> Positive var
#endif

sparsePureLiteralCNF :: CNF VarId
sparsePureLiteralCNF =
  CNF
    [ CNFClause $ Negative 0 : [Negative i | i <- [1 .. 8]]
    , CNFClause [Positive i | i <- [1 .. 8]]
    ]

sparsePureLiteralFallbackCNF :: CNF VarId
sparsePureLiteralFallbackCNF =
  CNF
    [ CNFClause [Positive i | i <- [1 .. 30]]
    , CNFClause [Positive 0]
    , CNFClause [Negative 0]
    ]

exhaustiveSmallCNFs :: [CNF VarId]
exhaustiveSmallCNFs =
  CNF [] : CNF [[]] : map CNF (chooseAtMost 3 normalizedClauses)
  where
    normalizedClauses :: [CNFClause VarId]
    normalizedClauses =
      map CNFClause $
        filter (not . null) $
          map
            ( concat
                . zipWith
                  ( \var -> \case
                      Nothing -> []
                      Just True -> [Positive var]
                      Just False -> [Negative var]
                  )
                  [0 .. 2]
            )
            (sequence $ replicate 3 [Nothing, Just False, Just True])

chooseAtMost :: Int -> [a] -> [[a]]
chooseAtMost limit = go limit
  where
    go _ [] = [[]]
    go 0 _ = [[]]
    go remaining (value : values) =
      let without = go remaining values
          with = map (value :) $ go (remaining - 1) values
       in without <> with

completedModels :: (Hashable w) => HashSet w -> Model w -> [Model w]
completedModels vars m =
  let missings = HS.toList $ vars `HS.difference` L.fold L.hashSet m
   in map ((m <>) . uncurry Model . (both %~ L.fold L.hashSet)) $
        getAp $
          foldMap' (\w -> Ap [(DL.singleton w, mempty), (mempty, DL.singleton w)]) missings

regressionCNFs :: [CNF VarId]
regressionCNFs =
  [ CNF []
  , CNF [[Positive 0], [Positive 2]]
  , CNF [[Positive 0], [Positive 0, Positive 1], [Positive 0, Negative 1]]
  , CNF [[Positive 0], [Negative 0, Positive 1], [Negative 1]]
  , CNF [[Negative 0, Negative 1], [Negative 0, Positive 1]]
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
  , CNF
      [ [Positive 0, Positive 0, Negative 7, Positive 7, Negative 1]
      , [Negative 6, Positive 5, Positive 0, Positive 0, Positive 0]
      , [Positive 6, Positive 0, Positive 5]
      ]
  ]

singletonUIPCNF :: CNF VarId
singletonUIPCNF =
  CNF
    [ [Positive 0, Positive 1]
    , [Positive 0, Negative 1]
    , [Positive 0, Positive 2]
    , [Positive 0, Negative 2]
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
