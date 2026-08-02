{-# LANGUAGE GHC2021 #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Logic.Propositional.Classical.SAT.CDCL qualified as CDCL
import Logic.Propositional.Classical.SAT.CDCL.Types (VarId)
import Logic.Propositional.Classical.SAT.Types (SatResult (..))
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive (CNF)
import Test.Tasty.Bench (bench, defaultMain, nf)
import Workloads (learnedInsertionCNF, propagationCNF)

main :: IO ()
main = do
  propagation <- evaluate $ force propagationCNF
  learnedInsertion <- evaluate $ force learnedInsertionCNF
  defaultMain
    [ bench "production/propagation/root-chain-4096" $
        nf solveExpectedUnsat propagation
    , bench "production/analysis-and-insertion/php-7-6" $
        nf solveExpectedUnsat learnedInsertion
    ]

solveExpectedUnsat :: CNF VarId -> ()
solveExpectedUnsat cnf =
  case CDCL.solveVarId cnf of
    Unsat -> ()
    Satisfiable _ -> error "production control unexpectedly returned SAT"
