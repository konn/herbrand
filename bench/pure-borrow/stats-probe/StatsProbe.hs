{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}

{- | The CDCL trajectory oracle.

Dumps everything the instrumentation exposes about one solve, so that two
implementations can be compared exactly rather than through aggregate timings:
all 39 integral 'SolverStats' counters, all three list-valued fields --
including 'analysisLearnedTrace', a complete ordered per-conflict transcript of
pivot sequence, backjump target and learned clause -- the returned model, and
the normalized clause list that fixes clause identity.

The clause list is the gate that the benchmark corpus cannot supply: that corpus
contains no duplicate clauses, repeated literals or tautologies, so
normalization is the identity on every case in it. Comparing the list directly
catches a reordering that leaves every counter unchanged.

Build out of tree against a given side's build directory, e.g.

> cabal exec -w ghc-9.12.4 --builddir=DIR -f cdcl-instrumented -- \
>   ghc-9.12.4 -O1 -package herbrand -o oracle StatsProbe.hs

so the benchmarked worktrees stay clean and their provenance checks keep
passing.
-}
module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import qualified Data.ByteString.Lazy as LBS
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Classical.SAT.Format.DIMACS (parseCNFLazy)
import System.Environment (getArgs)

main :: IO ()
main = do
  paths <- getArgs
  mapM_ report paths

report :: FilePath -> IO ()
report path = do
  raw <- LBS.readFile path
  !cnf <- case parseCNFLazy raw of
    Left message -> error message
    Right (_, _, parsed) -> evaluate (force (fmap VarId parsed))
  let (result, SolverStats {..}) = solveVarIdWithStats defaultOptions cnf
  !_ <- evaluate (force (() <$ result))
  putStrLn ("# " <> path)
  putStrLn ("result " <> show (() <$ result))
  putStrLn ("model " <> show result)
  case normalizedClausesForTest cnf of
    Nothing -> putStrLn "normalized short-circuited"
    Just (variables, clauses, normalized) -> do
      putStrLn ("normalizedVariableCount " <> show variables)
      putStrLn ("normalizedClauseCount " <> show clauses)
      putStrLn ("normalizedClauses " <> show normalized)
  putStrLn ("analysisLastPivotTrace " <> show analysisLastPivotTrace)
  putStrLn ("analysisLastLearnedClause " <> show analysisLastLearnedClause)
  putStrLn ("analysisLearnedTraceLength " <> show (length analysisLearnedTrace))
  putStrLn ("analysisLearnedTrace " <> show analysisLearnedTrace)
  mapM_
    (\(label, value) -> putStrLn (label <> " " <> show value))
    [ ("seedScanCount", seedScanCount)
    , ("postDrainScanCount", postDrainScanCount)
    , ("assignmentCount", assignmentCount)
    , ("trailAppendCount", trailAppendCount)
    , ("duplicateEnqueueCount", duplicateEnqueueCount)
    , ("propagationEventCount", propagationEventCount)
    , ("watchVisitCount", watchVisitCount)
    , ("watchMoveCount", watchMoveCount)
    , ("literalInspectionCount", literalInspectionCount)
    , ("decisionCount", decisionCount)
    , ("conflictCount", conflictCount)
    , ("backtrackCallCount", backtrackCallCount)
    , ("backtrackBoundaryReadCount", backtrackBoundaryReadCount)
    , ("backtrackTrailReadCount", backtrackTrailReadCount)
    , ("backtrackClearedCount", backtrackClearedCount)
    , ("backtrackValuationReadCount", backtrackValuationReadCount)
    , ("backtrackValuationWriteCount", backtrackValuationWriteCount)
    , ("backtrackQueueRestoreCount", backtrackQueueRestoreCount)
    , ("backtrackBoundaryProbeCount", backtrackBoundaryProbeCount)
    , ("backtrackNoOpCount", backtrackNoOpCount)
    , ("backtrackMaxSuffix", backtrackMaxSuffix)
    , ("ordinaryBacktrackCount", ordinaryBacktrackCount)
    , ("restartBacktrackCount", restartBacktrackCount)
    , ("observedRestartCount", observedRestartCount)
    , ("analysisCount", analysisCount)
    , ("analysisRootConflictCount", analysisRootConflictCount)
    , ("analysisConflictClauseVisitCount", analysisConflictClauseVisitCount)
    , ("analysisReasonClauseVisitCount", analysisReasonClauseVisitCount)
    , ("analysisConflictLiteralVisitCount", analysisConflictLiteralVisitCount)
    , ("analysisReasonLiteralVisitCount", analysisReasonLiteralVisitCount)
    , ("analysisTrailReadCount", analysisTrailReadCount)
    , ("analysisPivotCount", analysisPivotCount)
    , ("analysisMarkCount", analysisMarkCount)
    , ("analysisDuplicateMarkCount", analysisDuplicateMarkCount)
    , ("analysisLearnedLiteralCount", analysisLearnedLiteralCount)
    , ("analysisEpochClearCount", analysisEpochClearCount)
    , ("analysisSortComparisonCount", analysisSortComparisonCount)
    , ("analysisSortSwapCount", analysisSortSwapCount)
    , ("analysisLastTargetLevel", analysisLastTargetLevel)
    ]
