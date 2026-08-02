{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Herbrand.Bench
import Logic.Propositional.Classical.SAT.CDCL (CDCLOptions (..), RestartStrategy (..), defaultAdaptiveFactor, defaultExponentialRestart, defaultLubyRestart)
import qualified Logic.Propositional.Classical.SAT.CDCL as CDCL
import Logic.Propositional.Syntax.General
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive (CNF)
import System.Mem (performGC)

main :: IO ()
main = do
  !huges <- evaluate . force =<< findCnfsIn "data/sat/huge"
  !sudoku <- evaluate . force =<< findCnfsIn "data/sudoku"
  !satlib <-
    evaluate
      . force
      . filterFileTreeRoots (`elem` satlibBenchmarkRoots)
      =<< findCnfsIn "data/satlib"
  -- allowFailureBecause is dropped under measurement or nothing is instrumented
  -- at all; see 'allowFailureUnlessMeasuring'.
  --
  -- The timeout stays, but only as a safety net. Measured, the slowest selected
  -- leaf is ~1.5 s, so 120 s is ~24x headroom and fires only on a genuine hang.
  -- It must never be the thing that enforces a time budget: a wall-clock cap
  -- that actually fires under simulation truncates the benchmark while the
  -- instrument still reports the truncated count, and which leaves get cut
  -- shifts with runner load. Budget is controlled by case selection instead --
  -- see the --pattern in the codspeed job.
  allowFailure <- allowFailureUnlessMeasuring "Large input"
  measuring <- isMeasuring
  let benches = cdclBenches (allowFailure . timeout (if measuring then 120 else 100))
  performGC
  defaultMain
    [ bgroup
        "solve"
        [ withCnfs "huge" huges benches
        , withCnfs "Sudoku" sudoku benches
        , withCnfs "SATLIB" satlib benches
        ]
    ]

satlibBenchmarkRoots :: [String]
satlibBenchmarkRoots =
  [ "Bejing"
  , "flat200-479"
  , "uf100-430"
  , "uf20-91"
  , -- The unsatisfiable counterpart of uf100-430: same 100 variables, same 430
    -- clauses, same clause/variable ratio, opposite satisfiability. Refuting
    -- one exercises conflict analysis and clause learning to exhaustion rather
    -- than stopping at the first satisfying assignment, and pairing it with an
    -- otherwise identical satisfiable instance is what isolates that.
    "uuf100-430"
  ]

cdclBenches ::
  (Benchmark -> Benchmark) ->
  IO (CNF Word, Formula Full Word) ->
  [Benchmark]
cdclBenches guard fml =
  [ guard $
      bench lab $
        nfAppIO (fmap $ CDCL.solveWith opt . fst) fml
  | (lab, opt) <- cdclSolvers
  ]

cdclSolvers :: [(String, CDCLOptions)]
cdclSolvers =
  [
    ( "CDCL (α = 0.75)"
    , CDCL.CDCLOptions
        { decayFactor = 0.75
        , activateResolved = False
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS)"
    , CDCL.defaultOptions
        { decayFactor = 0.75
        , activateResolved = True
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, ExpRestart(100, 2))"
    , CDCL.defaultOptions
        { decayFactor = 0.75
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        }
    )
  ,
    ( "CDCL (α = 0.75, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { decayFactor = 0.75
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        }
    )
  ,
    ( "CDCL (α = 0.95)"
    , CDCLOptions
        { decayFactor = 0.95
        , activateResolved = False
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS)"
    , CDCLOptions
        { decayFactor = 0.95
        , activateResolved = True
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, ExpRestart(100, 2))"
    , CDCLOptions
        { decayFactor = 0.95
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        }
    )
  ,
    ( "CDCL (α = 0.95, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { decayFactor = 0.95
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        }
    )
  ,
    ( "CDCL (adaptive)"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = False
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVSIDS)"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = NoRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, ExpRestart(100, 2))"
    , CDCL.defaultOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = defaultExponentialRestart
        }
    )
  ,
    ( "CDCL (adaptive, mVISDS, LubyRestart(100, 2))"
    , CDCLOptions
        { decayFactor = defaultAdaptiveFactor
        , activateResolved = True
        , restartStrategy = defaultLubyRestart
        }
    )
  ]
