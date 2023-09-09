{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import Logic.Propositional.Classical.SAT.CDCL (CDCLOptions (..), RestartStrategy (..), defaultAdaptiveFactor, defaultExponentialRestart, defaultLubyRestart)
import qualified Logic.Propositional.Classical.SAT.CDCL as CDCL
import qualified Logic.Propositional.Classical.SAT.DPLL as DPLL
import qualified Logic.Propositional.Classical.SAT.Tableaux as Tableaux
import Logic.Propositional.Syntax.General
import System.Mem (performGC)

main :: IO ()
main = do
  !huges <- evaluate . force =<< findCnfsIn "data/sat/huge"
  !sudoku <- evaluate . force =<< findCnfsIn "data/sudoku"
  !satlib <- evaluate . force =<< findCnfsIn "data/satlib"
  performGC
  defaultMain
    [ bgroup
        "solve"
        [ withCnfs "huge" huges $ \fml ->
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
              ( timeout 180
                  $ bench "DPLL"
                  $ nfAppIO (fmap $ DPLL.solve . fst) fml
              )
              : cdclBenches fml
        , withCnfs "SATLIB" satlib $ \fml ->
            allowFailureBecause
              "Large input"
              ( timeout 180
                  $ bench "DPLL"
                  $ nfAppIO (fmap $ DPLL.solve . fst) fml
              )
              : cdclBenches fml
        ]
    ]

cdclBenches :: IO (DPLL.CNF Word, Formula Full Word) -> [Benchmark]
cdclBenches fml =
  [ allowFailureBecause "Large input"
    $ timeout 100
    $ bench lab
    $ nfAppIO (fmap $ CDCL.solveWith opt . fst) fml
  | (lab, opt) <- cdclSolvers
  ]

cdclSolvers :: [(String, CDCLOptions)]
cdclSolvers =
  [
    ( "CDCL (α = 0.75)"
    , CDCLOptions
        { decayFactor = 0.75
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , activateResolved = False
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS)"
    , CDCLOptions
        { decayFactor = 0.75
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, ExpRestart(100, 2))"
    , CDCLOptions
        { decayFactor = 0.75
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = defaultExponentialRestart
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { decayFactor = 0.75
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = defaultLubyRestart
        }
    )
  ,
    ( "CDCL (α = 0.95)"
    , CDCLOptions
        { decayFactor = 0.95
        , activateResolved = False
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS)"
    , CDCLOptions
        { decayFactor = 0.95
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, ExpRestart(100, 2))"
    , CDCLOptions
        { decayFactor = 0.95
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = defaultExponentialRestart
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { decayFactor = 0.95
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = defaultLubyRestart
        }
    )
  ,
    ( "CDCL (adaptive)"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = False
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVSIDS)"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, ExpRestart(100, 2))"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = defaultExponentialRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Nothing
        , restartStrategy = defaultLubyRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, LubyRestart(100, 2), random sel 50%)"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Just 0.5
        , restartStrategy = defaultLubyRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, LubyRestart(100, 2), random sel 25%)"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Just 0.25
        , restartStrategy = defaultLubyRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, LubyRestart(100, 2), random sel 10%)"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Just 0.1
        , restartStrategy = defaultLubyRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, LubyRestart(100, 2), random sel 1%)"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , randomSeed = 42
        , randomVarSelectionFreq = Just 0.01
        , restartStrategy = defaultLubyRestart
        }
    )
  ]
