{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive

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
        [ bench "fast" $ nfAppIO (fmap fromFormulaFast) fml
        ]
    , withSats "large" larges $ \fml ->
        [ bench "fast" $ nfAppIO (fmap fromFormulaFast) fml
        ]
    ]
