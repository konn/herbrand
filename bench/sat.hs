{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import Logic.Propositional.Classical.SAT.CDCL (CDCLOptions (..))
import qualified Logic.Propositional.Classical.SAT.CDCL as CDCL
import qualified Logic.Propositional.Classical.SAT.DPLL as DPLL
import qualified Logic.Propositional.Classical.SAT.Tableaux as Tableaux
import Logic.Propositional.Syntax.General
import System.Mem (performGC)
import System.Random.Stateful (Uniform (uniformM), globalStdGen)
import Test.Tasty (Timeout (..), localOption)

main :: IO ()
main = do
  !tinys <- evaluate . force =<< findCnfsIn "data/sat/tiny"
  !smalls <- evaluate . force =<< findCnfsIn "data/sat/small"
  !mediums <- evaluate . force =<< findCnfsIn "data/sat/medium"
  !larges <- evaluate . force =<< findCnfsIn "data/sat/large"
  !huges <- evaluate . force =<< findCnfsIn "data/sat/huge"
  !sudoku <- evaluate . force =<< findCnfsIn "data/sudoku"
  !satlib <- evaluate . force =<< findCnfsIn "data/satlib"
  performGC
  defaultMain
    [ bgroup
        "solve"
        [ withCnfs "tiny" tinys $ \fml ->
            [ bench "tableaux" $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
              ++ cdclBenches fml
        , withCnfs "small" smalls $ \fml ->
            [ bench "tableaux" $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
              ++ cdclBenches fml
        , withCnfs "medium" mediums $ \fml ->
            [ allowFailureBecause "O(n^2)"
                $ localOption (Timeout (30 * 10 ^ (6 :: Int)) "30s")
                $ bench "tableaux"
                $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
              ++ cdclBenches fml
        , withCnfs "large" larges $ \fml ->
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
  [ bench "CDCL (α = 0.75)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.75}) . fst) fml
  , bench "CDCL (α = 0.75, mVISDS)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.75, activateResolved = True}) . fst) fml
  , bench "CDCL (α = 0.75, mVISDS)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.75, activateResolved = True}) . fst) fml
  , bench "CDCL (α = 0.95)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.95}) . fst) fml
  , bench "CDCL (α = 0.95, mVISDS)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.95, activateResolved = True}) . fst) fml
  , bench "CDCL (α = 0.99)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.99}) . fst) fml
  , bench "CDCL (α = 0.99, mVISDS)" $ nfAppIO (fmap $ CDCL.solveWith (CDCL.defaultOptions {decayFactor = 0.99, activateResolved = True}) . fst) fml
  ]
    ++ [ bench ("CDCL (α = 0.99, mVISDS, random " <> show n <> "%)")
        $ flip nfAppIO fml
        $ \alloc -> do
          (phi, _) <- alloc
          seed <- uniformM globalStdGen
          pure
            $! CDCL.solveWith
              CDCL.defaultOptions {decayFactor = 0.99, activateResolved = True, randomSeed = seed, randomVSIDSFreq = Just $ fromIntegral n / 100}
              phi
       | n <- [10, 25, 50 :: Int]
       ]
