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
    , CDCL.CDCLOptions
        { variableDecayFactor = 0.75
        , activateResolved = False
        , restartStrategy = NoRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS)"
    , CDCL.defaultOptions
        { variableDecayFactor = 0.75
        , activateResolved = True
        , restartStrategy = NoRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, Clause Decay 0.999)"
    , CDCL.defaultOptions
        { variableDecayFactor = 0.75
        , activateResolved = True
        , restartStrategy = NoRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, ExpRestart(100, 2))"
    , CDCL.defaultOptions
        { variableDecayFactor = 0.75
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, ExpRestart(100, 2), Clause Decay 0.999)"
    , CDCL.defaultOptions
        { variableDecayFactor = 0.75
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { variableDecayFactor = 0.75
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, LubyRestart(100, 2), Clause Decay 0.999)"
    , CDCLOptions
        { variableDecayFactor = 0.75
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ,
    ( "CDCL (α = 0.95)"
    , CDCLOptions
        { variableDecayFactor = 0.95
        , activateResolved = False
        , restartStrategy = NoRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS)"
    , CDCLOptions
        { variableDecayFactor = 0.95
        , activateResolved = True
        , restartStrategy = NoRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, Clause Decay 0.999)"
    , CDCLOptions
        { variableDecayFactor = 0.95
        , activateResolved = True
        , restartStrategy = NoRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, ExpRestart(100, 2))"
    , CDCLOptions
        { variableDecayFactor = 0.95
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, ExpRestart(100, 2), Clause Decay 0.999)"
    , CDCLOptions
        { variableDecayFactor = 0.95
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { variableDecayFactor = 0.95
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, LubyRestart(100, 2), Clause Decay 0.999)"
    , CDCLOptions
        { variableDecayFactor = 0.95
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ,
    ( "CDCL (adaptive)"
    , CDCLOptions
        { variableDecayFactor = defaultAdaptiveFactor
        , activateResolved = False
        , restartStrategy = NoRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (adaptive, mVSIDS)"
    , CDCLOptions
        { variableDecayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = NoRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (adaptive, mVSIDS, Clause Decay 0.999)"
    , CDCLOptions
        { variableDecayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = NoRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, ExpRestart(100, 2))"
    , CDCL.defaultOptions
        { variableDecayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, ExpRestart(100, 2), Clause Decay 0.999)"
    , CDCL.defaultOptions
        { variableDecayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { variableDecayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        , clauseDecayFactor = Nothing
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, LubyRestart(100, 2), Clause Decay)"
    , CDCLOptions
        { variableDecayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        , clauseDecayFactor = Just 0.999
        }
    )
  ]
