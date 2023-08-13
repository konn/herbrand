{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive

main :: IO ()
main = do
  !targs <- evaluate . force =<< findSatsIn "data/formula-to-cnf"
  defaultMain
    [ withSats "All" targs $ \fml ->
        [ bench "naive" $ nfAppIO (fmap fromFormulaNaive) fml
        , bench "ord" $ nfAppIO (fmap fromFormulaOrd) fml
        , bench "fast" $ nfAppIO (fmap fromFormulaFast) fml
        ]
    ]
