{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import Logic.Propositional.Classical.SAT.CDCL (CDCLOptions (..), defaultAdaptiveFactor)
import qualified Logic.Propositional.Classical.SAT.CDCL as CDCL
import qualified Logic.Propositional.Classical.SAT.DPLL as DPLL
import qualified Logic.Propositional.Classical.SAT.Tableaux as Tableaux
import Logic.Propositional.Syntax.General
import System.Mem (performGC)
import Test.Tasty (Timeout (..), localOption)

main :: IO ()
main = do
  !larges <- evaluate . force =<< findCnfsIn "data/sat/large"
  !huges <- evaluate . force =<< findCnfsIn "data/sat/huge"
  !sudoku <- evaluate . force =<< findCnfsIn "data/sudoku"
  !satlib <- evaluate . force =<< findCnfsIn "data/satlib"
  performGC
  defaultMain
    [ bgroup
        "solve"
        [ withCnfs "large" larges $ \fml ->
            [ allowFailureBecause "O(n^2)"
                $ localOption (Timeout (30 * 10 ^ (6 :: Int)) "30s")
                $ bench "tableaux"
                $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
              ++ cdclBenches fml
        , withCnfs "huge" huges $ \fml ->
            [ allowFailureBecause "O(n^2)"
                $ timeout 30
                $ bench "tableaux"
                $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
              ++ cdclBenches fml
        , withCnfs "Sudoku" sudoku $ \fml ->
            allowFailureBecause
              "Large input"
              ( timeout 240
                  $ bench "DPLL"
                  $ nfAppIO (fmap $ DPLL.solve . fst) fml
              )
              : cdclBenches fml
        , withCnfs "SATLIB" satlib $ \fml ->
            allowFailureBecause
              "Large input"
              ( timeout 240
                  $ bench "DPLL"
                  $ nfAppIO (fmap $ DPLL.solve . fst) fml
              )
              : cdclBenches fml
        ]
    ]

cdclBenches :: IO (DPLL.CNF Word, Formula Full Word) -> [Benchmark]
cdclBenches fml =
  [ bench "CDCL (α = 0.75)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.75, activateResolved = False}) . fst) fml
  , bench "CDCL (α = 0.75, mVISDS)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.75, activateResolved = True}) . fst) fml
  , bench "CDCL (α = 0.95)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.95, activateResolved = False}) . fst) fml
  , bench "CDCL (α = 0.95, mVISDS)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.95, activateResolved = True}) . fst) fml
  , bench "CDCL (α = 0.99)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.99, activateResolved = False}) . fst) fml
  , bench "CDCL (α = 0.99, mVISDS)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.99, activateResolved = True}) . fst) fml
  , bench "CDCL (adaptive)"
      $ nfAppIO
        ( fmap
            $ CDCL.solveWith
              ( CDCL.defaultOptions
                  { decayFactor = defaultAdaptiveFactor
                  , activateResolved = False
                  }
              )
            . fst
        )
        fml
  , bench "CDCL (adaptive, mVSIDS)"
      $ nfAppIO
        ( fmap
            $ CDCL.solveWith
              ( CDCL.defaultOptions
                  { decayFactor = defaultAdaptiveFactor
                  , activateResolved = True
                  }
              )
            . fst
        )
        fml
  ]
