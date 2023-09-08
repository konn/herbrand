{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import qualified Control.Foldl as L
import Control.Lens (ifoldMap)
import qualified Data.ByteString.Builder as BB
import qualified Data.DList as DL
import Data.Foldable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import Data.Semigroup.Foldable
import Data.String
import qualified Data.Vector as V
import Logic.Propositional.Classical.SAT.CDCL
import Logic.Propositional.Classical.SAT.Format.DIMACS
import Logic.Propositional.Classical.SAT.Types (SatResult (..), positive)
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive.Sudoku
import Math.NumberTheory.Logarithms (integerLog10')
import System.Directory (createDirectoryIfMissing)
import System.IO (stdout)
import System.Random.Stateful (globalStdGen, uniformM)

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

maxDigit :: Word -> Int
maxDigit = (+ 1) . (* 2) . integerLog10' . fromIntegral

fromBoard :: (Foldable t) => t Placement -> HashMap (Word, Word) Word
fromBoard = L.fold $ L.premap (\(Placement i j d) -> ((i, j), d)) L.hashMap

prettyBoardWith :: Word -> HashMap (Word, Word) Word -> BB.Builder
prettyBoardWith n dic =
  let d = maxDigit n
      wall = "|" <> fold (L.intersperse "+" $ replicate (fromIntegral $ n * n) (fromString $ replicate d '-')) <> "|\n"
   in wall
        <> intercalateMap1
          wall
          ( \i ->
              "|"
                <> intercalateMap1
                  "|"
                  ( \j ->
                      case HM.lookup (i, j) dic of
                        Nothing -> fromString $ replicate d ' '
                        Just p ->
                          let pad = max 0 $ d - (integerLog10' (fromIntegral p) + 1)
                           in fromString (replicate pad ' ') <> BB.wordDec p
                  )
                  (NE.fromList [0 .. (n * n) - 1])
                <> "|\n"
          )
          (NE.fromList [0 .. (n * n) - 1])
        <> wall

toPlacements :: V.Vector (V.Vector Word) -> [Literal Placement]
toPlacements =
  DL.toList . ifoldMap \i -> ifoldMap \j d ->
    if d > 0
      then DL.singleton $ Positive $ Placement (fromIntegral i) (fromIntegral j) d
      else mempty

problem9x9_1 :: CNF Placement
problem9x9_1 =
  makePuzzle 3
    $ toPlacements
      [ [8, 0, 3, 0, 4, 2, 1, 0, 6]
      , [0, 2, 0, 8, 0, 0, 4, 0, 0]
      , [0, 6, 9, 7, 0, 3, 0, 2, 8]
      , [3, 0, 0, 9, 6, 0, 2, 0, 0]
      , [9, 4, 0, 2, 0, 0, 0, 6, 5]
      , [0, 1, 6, 0, 3, 5, 7, 0, 9]
      , [5, 0, 4, 1, 0, 0, 0, 7, 3]
      , [0, 3, 1, 6, 0, 8, 9, 0, 2]
      , [0, 9, 0, 0, 7, 4, 8, 5, 0]
      ]

problem9x9_2 :: CNF Placement
problem9x9_2 =
  makePuzzle 3
    $ toPlacements
      [ [8, 0, 3, 0, 4, 0, 1, 0, 6]
      , [0, 2, 0, 8, 0, 0, 4, 0, 0]
      , [0, 6, 9, 7, 0, 3, 0, 2, 0]
      , [3, 0, 0, 9, 6, 0, 0, 0, 0]
      , [0, 4, 0, 2, 0, 0, 0, 6, 5]
      , [0, 1, 6, 0, 3, 5, 7, 0, 9]
      , [5, 0, 4, 1, 0, 0, 0, 7, 3]
      , [0, 0, 1, 6, 0, 8, 9, 0, 2]
      , [0, 9, 0, 0, 7, 4, 8, 5, 0]
      ]

main :: IO ()
main = do
  createDirectoryIfMissing True "data/gen/sudoku/9x9"
  BB.writeFile "data/gen/sudoku/9x9/1.cnf"
    $ formatDIMACS
    $ toDIMACS problem9x9_1
  BB.writeFile "data/gen/sudoku/9x9/2.cnf"
    $ formatDIMACS
    $ toDIMACS problem9x9_2
  let ans =
        solveWith
          defaultOptions
            { restartStrategy = defaultLubyRestart
            , decayFactor = defaultAdaptiveFactor
            }
          problem9x9_2
  case ans of
    Unsat -> putStrLn "Unsat"
    Satisfiable m -> do
      putStrLn $ "Satisfiable: " <> show m
      BB.hPutBuilder stdout $ prettyBoardWith 3 $ fromBoard $ positive m
