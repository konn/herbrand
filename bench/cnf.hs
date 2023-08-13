module Main (main) where

import Herbrand.Bench
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive

main :: IO ()
main = do
  targs <- findSatsIn "data/formula-to-cnf"
  defaultMain
    [ withSats "All" targs $ \fml ->
        [ bench "naive" $ nfAppIO (fmap fromFormulaNaive) fml
        , bench "ord" $ nfAppIO (fmap fromFormulaOrd) fml
        , bench "fast" $ nfAppIO (fmap fromFormulaFast) fml
        ]
    ]
