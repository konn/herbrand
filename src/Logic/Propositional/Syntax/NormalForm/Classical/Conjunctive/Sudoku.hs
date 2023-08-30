{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive.Sudoku (
  Placement (..),
  sudokuRules,
) where

import Control.DeepSeq
import Data.DList (DList)
import qualified Data.DList as DL
import Data.Hashable
import qualified Data.Vector as V
import GHC.Generics
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive

data Placement = Placement {x, y, digit :: {-# UNPACK #-} !Word}
  deriving (Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

instance Show Placement where
  showsPrec _ (Placement i j d) = showString "a" . shows i . shows j . shows d

-- | @'sudokuRules' k@ generates a basic rule for \(k^2 \times k^2\)-sudoku.
sudokuRules :: Word -> DList (CNFClause Placement)
sudokuRules k = cellHasUniqueDigit <> rowDigits <> colDigits <> cellDigits
  where
    !n = k * k
    cellDigits =
      foldMap
        ( \(bi, bj, d) ->
            DL.singleton
              $ CNFClause
                [ Positive $ Placement (k * bi + i) (k * bj + j) d
                | i <- [0 .. k - 1]
                , j <- [0 .. k - 1]
                ]
        )
        [(bi, bj, d) | bi <- [0 .. k - 1], bj <- [0 .. k - 1], d <- [1 .. n]]
    rowDigits =
      foldMap
        ( \(j, d) ->
            DL.singleton $ CNFClause [Positive $ Placement i j d | i <- [0 .. n - 1]]
        )
        [ (j, d)
        | j <- [0 .. n - 1]
        , d <- [1 .. n]
        ]
    colDigits =
      foldMap
        ( \(i, d) ->
            DL.singleton $ CNFClause [Positive (Placement i j d) | j <- [0 .. n - 1]]
        )
        [ (i, d)
        | i <- [0 .. n - 1]
        , d <- [1 .. n]
        ]
    cellHasUniqueDigit =
      foldMap
        ( \(i, j) -> xors $ V.generate (fromIntegral n) $ Placement i j . fromIntegral . (+ 1)
        )
        [(i, j) | i <- [0 .. n - 1], j <- [0 .. n - 1]]

xors :: V.Vector x -> DList (CNFClause x)
xors xs =
  let n = V.length xs
   in DL.cons
        (CNFClause $ V.toList $ V.map Positive xs)
        $ foldMap
          ( \i ->
              foldMap
                ( \j ->
                    DL.singleton
                      $ CNFClause
                        [Negative (xs V.! i), Negative (xs V.! j)]
                )
                [0 .. i - 1]
          )
          [0 .. n - 1]
