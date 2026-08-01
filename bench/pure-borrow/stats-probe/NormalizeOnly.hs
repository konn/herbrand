{- | Normalize-only allocation driver.

Isolates the allocation cost of CDCL clause normalization from the rest of a
solve. Parses a DIMACS file, forces __only__ the normalized clause list, and
exits; run under @+RTS -s@ on two sides, the difference is that slice's true
normalization cost, measured on the real implementation rather than modelled.

The forcing is deep on purpose. 'normalizedClausesForTest' returns a lazy
@[[Lit]]@, so forcing to WHNF would report a cost near zero and make any gate
built on it trivially passable. Production consumes every clause and every
literal through @buildClause@, so this does too.
-}
module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import qualified Data.ByteString.Lazy as LBS
import Logic.Propositional.Classical.SAT.CDCL (VarId (..), normalizedClausesForTest)
import Logic.Propositional.Classical.SAT.CDCL.Types (litVar, unVarId)
import Logic.Propositional.Classical.SAT.Format.DIMACS (parseCNFLazy)
import System.Environment (getArgs)

main :: IO ()
main = getArgs >>= mapM_ report

report :: FilePath -> IO ()
report path = do
  raw <- LBS.readFile path
  cnf <- case parseCNFLazy raw of
    Left message -> error message
    Right (_, _, parsed) -> evaluate (force (fmap VarId parsed))
  case normalizedClausesForTest cnf of
    Nothing -> putStrLn (path <> " short-circuited")
    Just (variables, clauses, normalized) -> do
      -- Deep-force every literal of every clause, as buildClause does.
      total <- evaluate (sum (map (sum . map (unVarId . litVar)) normalized))
      putStrLn
        ( path
            <> " variables="
            <> show variables
            <> " clauses="
            <> show clauses
            <> " literalChecksum="
            <> show total
        )
