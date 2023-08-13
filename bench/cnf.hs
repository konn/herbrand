{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Test.Tasty (Timeout (..), localOption)

main :: IO ()
main = do
  !smalls <- evaluate . force =<< findSatsIn "data/formula-to-cnf/small"
  !mediums <- evaluate . force =<< findSatsIn "data/formula-to-cnf/medium"
  !larges <- evaluate . force =<< findSatsIn "data/formula-to-cnf/large"
  defaultMain
    [ withSats "small" smalls $ \fml ->
        [ bench "naive" $ nfAppIO (fmap fromFormulaNaive) fml
        , bench "ord" $ nfAppIO (fmap fromFormulaOrd) fml
        , bench "fast" $ nfAppIO (fmap fromFormulaFast) fml
        ]
    , withSats "medium" mediums $ \fml ->
        [ localOption (Timeout (10 * 10 ^ (6 :: Int)) "10s")
            $ bench "naive"
            $ nfAppIO (fmap fromFormulaNaive) fml
        , localOption (Timeout (10 * 10 ^ (6 :: Int)) "10s")
            $ bench "ord"
            $ nfAppIO (fmap fromFormulaOrd) fml
        , bench "fast" $ nfAppIO (fmap fromFormulaFast) fml
        ]
    , withSats "large" larges $ \fml ->
        [ localOption (Timeout (10 * 10 ^ (6 :: Int)) "10s")
            $ bench "naive"
            $ nfAppIO (fmap fromFormulaNaive) fml
        , localOption (Timeout (10 * 10 ^ (6 :: Int)) "10s")
            $ bench "ord"
            $ nfAppIO (fmap fromFormulaOrd) fml
        , bench "fast" $ nfAppIO (fmap fromFormulaFast) fml
        ]
    ]
