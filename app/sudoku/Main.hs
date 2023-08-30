module Main (main) where

import qualified Data.ByteString.Builder as BB
import qualified Data.DList as DL
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Classical.SAT.Format.DIMACS
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive.Sudoku

a :: Word -> Word -> Word -> Literal Placement
a = fmap (fmap Positive) . Placement

puzzle0 :: [Literal Placement]
puzzle0 = [a 0 0 2, a 1 0 3, a 2 0 4, a 0 1 1, a 1 1 4, a 2 1 3, a 1 2 2, a 0 3 4, a 1 3 1]

makePuzzle :: Word -> [Literal Placement] -> CNF Placement
makePuzzle n initial =
  CNF
    $ DL.toList
    $ DL.fromList (map (CNFClause . pure) initial)
    <> sudokuRules n

main :: IO ()
main = do
  BB.writeFile "data/sudoku/4x4/1.cnf"
    $ formatDIMACS
    $ toDIMACS
    $ makePuzzle 2 puzzle0
  print $ solve (makePuzzle 2 puzzle0)
