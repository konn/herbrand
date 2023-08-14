{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import qualified Logic.Propositional.Classical.SAT.DPLL as DPLL
import qualified Logic.Propositional.Classical.SAT.Tableaux as Tableaux
import System.Mem (performGC)
import Test.Tasty (Timeout (..), localOption)

main :: IO ()
main = do
  !tinys <- evaluate . force =<< findCnfsIn "data/sat/tiny"
  !smalls <- evaluate . force =<< findCnfsIn "data/sat/small"
  !mediums <- evaluate . force =<< findCnfsIn "data/sat/medium"
  !larges <- evaluate . force =<< findCnfsIn "data/sat/large"
  !huges <- evaluate . force =<< findCnfsIn "data/sat/huge"
  performGC
  defaultMain
    [ bgroup
        "solve"
        [ withCnfs "tiny" tinys $ \fml ->
            [ bench "tableaux" $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
        , withCnfs "small" smalls $ \fml ->
            [ bench "tableaux" $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
        , withCnfs "medium" mediums $ \fml ->
            [ allowFailureBecause "O(n^2)"
                $ localOption (Timeout (10 * 10 ^ (6 :: Int)) "10s")
                $ bench "tableaux"
                $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
        , withCnfs "large" larges $ \fml ->
            [ allowFailureBecause "O(n^2)"
                $ localOption (Timeout (10 * 10 ^ (6 :: Int)) "10s")
                $ bench "tableaux"
                $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
        , withCnfs "huge" huges $ \fml ->
            [ allowFailureBecause "O(n^2)"
                $ localOption (Timeout (10 * 10 ^ (6 :: Int)) "10s")
                $ bench "tableaux"
                $ nfAppIO (fmap $ Tableaux.solve . snd) fml
            , bench "DPLL" $ nfAppIO (fmap $ DPLL.solve . fst) fml
            ]
        ]
    ]
