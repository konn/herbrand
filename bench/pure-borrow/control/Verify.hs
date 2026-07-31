{-# LANGUAGE GHC2021 #-}

module Main (main) where

import Logic.Propositional.Classical.SAT.CDCL qualified as CDCL
import Logic.Propositional.Classical.SAT.CDCL.Types (SolverStats (..))
import Logic.Propositional.Classical.SAT.Types (SatResult (..))
import Workloads (learnedInsertionCNF, propagationCNF)

main :: IO ()
main = do
  rootStats <- verifyRootPropagation
  analysisStats <- verifyConflictAnalysis
  putStrLn $ "root-propagation stats: " <> show rootStats
  putStrLn $ "analysis-insertion stats: " <> show analysisStats
  putStrLn "production-control trajectory verification passed"

verifyRootPropagation :: IO SolverStats
verifyRootPropagation =
  case CDCL.solveVarIdWithStats CDCL.defaultOptions propagationCNF of
    (Unsat, stats)
      | propagationEventCount stats > 0
      , decisionCount stats == 0
      , analysisRootConflictCount stats > 0
      , analysisLearnedLiteralCount stats == 0
      , ordinaryBacktrackCount stats == 0 ->
          pure stats
      | otherwise ->
          error $ "root-propagation stats do not prove the expected path: " <> show stats
    (Satisfiable _, _) ->
      error "root-propagation control unexpectedly returned SAT"

verifyConflictAnalysis :: IO SolverStats
verifyConflictAnalysis =
  case CDCL.solveVarIdWithStats CDCL.defaultOptions learnedInsertionCNF of
    (Unsat, stats)
      | conflictCount stats > 0
      , analysisCount stats > 0
      , analysisLearnedLiteralCount stats > 0
      , ordinaryBacktrackCount stats > 0 ->
          pure stats
      | otherwise ->
          error $ "PHP stats do not prove conflict analysis and learning: " <> show stats
    (Satisfiable _, _) ->
      error "PHP control unexpectedly returned SAT"
