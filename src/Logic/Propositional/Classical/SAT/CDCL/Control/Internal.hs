{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Logic.Propositional.Classical.SAT.CDCL.Control.Internal (
  SolverControl,
  initialControl,
  finishControl,
  propagationCursor,
  advancePropagation,
  assignmentContext,
  appendAssignment,
  pushDecisionLevel,
  currentDecideLevel,
  levelStartsLength,
  setBacktrackState,
  tryRestart,
  bumpSeedScan,
  bumpPostDrainScan,
  bumpDuplicateEnqueue,
  bumpWatchVisit,
  bumpWatchVisits,
  bumpWatchMove,
  bumpWatchMoves,
  bumpLiteralInspections,
  bumpConflict,
  recordBacktrack,
  modifyStats,
) where

import Logic.Propositional.Classical.SAT.CDCL.Types
import Prelude.Linear
import Prelude qualified as NonLinear

#ifdef HERBRAND_CDCL_INSTRUMENTED
newtype Instrumentation = Instrumentation SolverStats
#else
data Instrumentation = Instrumentation
#endif

data SolverControl where
  SolverControl ::
    -- propagation cursor
    {-# UNPACK #-} !Int ->
    {-# UNPACK #-} -- active trail length
    !Int ->
    {-# UNPACK #-} -- active level-start length
    !Int ->
    {-# UNPACK #-} -- conflicts since the last restart
    !Word ->
    {-# UNPACK #-} -- next restart threshold
    !Word ->
    {-# UNPACK #-} -- completed restart count
    !Word ->
    !Instrumentation %1 ->
    SolverControl

instance Consumable SolverControl where
  consume (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    consume qhead `lseq`
      consume trailLength `lseq`
        consume levels `lseq`
          consume runs `lseq`
            consume threshold `lseq`
              consume restarts `lseq`
                consumeInstrumentation instrumentation

consumeInstrumentation :: Instrumentation %1 -> ()
#ifdef HERBRAND_CDCL_INSTRUMENTED
consumeInstrumentation (Instrumentation stats) = consume stats
#else
consumeInstrumentation Instrumentation = ()
#endif

initialControl :: CDCLOptions -> SolverControl
initialControl options =
  SolverControl
    0
    0
    1
    0
    (initialRestartThreshold (restartStrategy options))
    0
    initialInstrumentation

initialRestartThreshold :: RestartStrategy -> Word
initialRestartThreshold NoRestart = 0
initialRestartThreshold ExponentialRestart {initialRestart} =
  initialRestart
initialRestartThreshold LubyRestart {initialRestart} =
  initialRestart

initialInstrumentation :: Instrumentation
#ifdef HERBRAND_CDCL_INSTRUMENTED
initialInstrumentation = Instrumentation zeroSolverStats
#else
initialInstrumentation = Instrumentation
#endif

finishControl :: SolverControl %1 -> Ur SolverStats
finishControl
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    qhead `lseq`
      trailLength `lseq`
        levels `lseq`
          runs `lseq`
            threshold `lseq`
              restarts `lseq`
                finishInstrumentation instrumentation

finishInstrumentation :: Instrumentation %1 -> Ur SolverStats
#ifdef HERBRAND_CDCL_INSTRUMENTED
finishInstrumentation (Instrumentation stats) = move stats
#else
finishInstrumentation Instrumentation = Ur zeroSolverStats
#endif

modifyStats ::
  (SolverStats -> SolverStats) ->
  SolverControl %1 ->
  SolverControl
#ifdef HERBRAND_CDCL_INSTRUMENTED
modifyStats update =
  mapInstrumentation (updateStats update)
#else
{-# INLINE modifyStats #-}
modifyStats _ control = control
#endif

propagationCursor :: SolverControl %1 -> (Ur (Int, Int), SolverControl)
propagationCursor
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    ( Ur (qhead, trailLength)
    , SolverControl
        qhead
        trailLength
        levels
        runs
        threshold
        restarts
        instrumentation
    )

advancePropagation :: SolverControl %1 -> SolverControl
advancePropagation
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    SolverControl
      (qhead + 1)
      trailLength
      levels
      runs
      threshold
      restarts
      (bumpPropagationEventI instrumentation)

assignmentContext ::
  SolverControl %1 ->
  (Ur (DecideLevel, Step), SolverControl)
assignmentContext
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    ( Ur
        ( DecideLevel (levels - 1)
        , Step (NonLinear.fromIntegral trailLength)
        )
    , SolverControl
        qhead
        trailLength
        levels
        runs
        threshold
        restarts
        instrumentation
    )

appendAssignment :: SolverControl %1 -> SolverControl
appendAssignment
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    SolverControl
      qhead
      (trailLength + 1)
      levels
      runs
      threshold
      restarts
      (bumpTrailAppendI (bumpAssignmentI instrumentation))

pushDecisionLevel :: SolverControl %1 -> SolverControl
pushDecisionLevel
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    SolverControl
      qhead
      trailLength
      (levels + 1)
      runs
      threshold
      restarts
      (bumpDecisionI instrumentation)

currentDecideLevel ::
  SolverControl %1 ->
  (Ur DecideLevel, SolverControl)
currentDecideLevel
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    ( Ur (DecideLevel (levels - 1))
    , SolverControl
        qhead
        trailLength
        levels
        runs
        threshold
        restarts
        instrumentation
    )

levelStartsLength :: SolverControl %1 -> (Ur Int, SolverControl)
levelStartsLength
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    ( Ur levels
    , SolverControl
        qhead
        trailLength
        levels
        runs
        threshold
        restarts
        instrumentation
    )

setBacktrackState ::
  DecideLevel ->
  Int ->
  SolverControl %1 ->
  SolverControl
setBacktrackState
  target
  cutoff
  (SolverControl qhead _ _ runs threshold restarts instrumentation) =
    SolverControl
      (min qhead cutoff)
      cutoff
      (unDecideLevel target + 1)
      runs
      threshold
      restarts
      instrumentation

tryRestart ::
  CDCLOptions ->
  SolverControl %1 ->
  (Ur RestartResult, SolverControl)
tryRestart options control =
  case restartStrategy options of
    NoRestart -> (Ur Continued, control)
    strategy ->
      case control of
        SolverControl qhead trailLength levels runs threshold restarts instrumentation ->
          let !nextRuns = runs + 1
           in if threshold NonLinear.<= nextRuns
                then
                  ( Ur Restarted
                  , SolverControl
                      qhead
                      trailLength
                      levels
                      0
                      ( nextRestartThreshold
                          strategy
                          threshold
                          (restarts + 1)
                      )
                      (restarts + 1)
                      (bumpRestartI instrumentation)
                  )
                else
                  ( Ur Continued
                  , SolverControl
                      qhead
                      trailLength
                      levels
                      nextRuns
                      threshold
                      restarts
                      instrumentation
                  )

nextRestartThreshold ::
  RestartStrategy ->
  Word ->
  Word ->
  Word
nextRestartThreshold NoRestart threshold _ = threshold
nextRestartThreshold ExponentialRestart {increaseFactor} threshold _ =
  threshold * increaseFactor
nextRestartThreshold LubyRestart {initialRestart} _ restartCount =
  initialRestart * luby restartCount

bumpSeedScan
  , bumpPostDrainScan
  , bumpDuplicateEnqueue
  , bumpWatchVisit
  , bumpWatchMove
  , bumpConflict ::
    SolverControl %1 -> SolverControl
bumpSeedScan = mapInstrumentation bumpSeedScanI
bumpPostDrainScan = mapInstrumentation bumpPostDrainScanI
bumpDuplicateEnqueue = mapInstrumentation bumpDuplicateEnqueueI
bumpWatchVisit = mapInstrumentation bumpWatchVisitI

bumpWatchVisits :: Int -> SolverControl %1 -> SolverControl
bumpWatchVisits count = mapInstrumentation (bumpWatchVisitsI count)

bumpWatchMove = mapInstrumentation bumpWatchMoveI

bumpWatchMoves :: Int -> SolverControl %1 -> SolverControl
bumpWatchMoves count = mapInstrumentation (bumpWatchMovesI count)

bumpConflict = mapInstrumentation bumpConflictI

bumpLiteralInspections :: Int -> SolverControl %1 -> SolverControl
bumpLiteralInspections count =
  mapInstrumentation (bumpLiteralInspectionsI count)

recordBacktrack ::
  Bool ->
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  SolverControl %1 ->
  SolverControl
recordBacktrack isRestart boundaryReads trailReads clears valuationReads boundaryProbes =
  mapInstrumentation
    ( recordBacktrackI
        isRestart
        boundaryReads
        trailReads
        clears
        valuationReads
        boundaryProbes
    )

mapInstrumentation ::
  (Instrumentation %1 -> Instrumentation) %1 ->
  SolverControl %1 ->
  SolverControl
mapInstrumentation
  update
  (SolverControl qhead trailLength levels runs threshold restarts instrumentation) =
    SolverControl
      qhead
      trailLength
      levels
      runs
      threshold
      restarts
      (update instrumentation)

#ifdef HERBRAND_CDCL_INSTRUMENTED
updateStats ::
  (SolverStats -> SolverStats) ->
  Instrumentation %1 ->
  Instrumentation
updateStats function (Instrumentation stats) =
  case move stats of
    Ur unrestrictedStats ->
      Instrumentation (function unrestrictedStats)

bumpSeedScanI,
  bumpPostDrainScanI,
  bumpAssignmentI,
  bumpTrailAppendI,
  bumpDuplicateEnqueueI,
  bumpPropagationEventI,
  bumpWatchVisitI,
  bumpWatchMoveI,
  bumpDecisionI,
  bumpConflictI,
  bumpRestartI ::
    Instrumentation %1 -> Instrumentation
bumpSeedScanI =
  updateStats \stats ->
    stats {seedScanCount = seedScanCount stats + 1}
bumpPostDrainScanI =
  updateStats \stats ->
    stats {postDrainScanCount = postDrainScanCount stats + 1}
bumpAssignmentI =
  updateStats \stats ->
    stats {assignmentCount = assignmentCount stats + 1}
bumpTrailAppendI =
  updateStats \stats ->
    stats {trailAppendCount = trailAppendCount stats + 1}
bumpDuplicateEnqueueI =
  updateStats \stats ->
    stats
      { duplicateEnqueueCount =
          duplicateEnqueueCount stats + 1
      }
bumpPropagationEventI =
  updateStats \stats ->
    stats
      { propagationEventCount =
          propagationEventCount stats + 1
      }
bumpWatchVisitI =
  updateStats \stats ->
    stats {watchVisitCount = watchVisitCount stats + 1}
bumpWatchVisitsI ::
  Int ->
  Instrumentation %1 ->
  Instrumentation
bumpWatchVisitsI count =
  updateStats \stats ->
    stats {watchVisitCount = watchVisitCount stats + count}
bumpWatchMoveI =
  updateStats \stats ->
    stats {watchMoveCount = watchMoveCount stats + 1}
bumpWatchMovesI ::
  Int ->
  Instrumentation %1 ->
  Instrumentation
bumpWatchMovesI count =
  updateStats \stats ->
    stats {watchMoveCount = watchMoveCount stats + count}
bumpDecisionI =
  updateStats \stats ->
    stats {decisionCount = decisionCount stats + 1}
bumpConflictI =
  updateStats \stats ->
    stats {conflictCount = conflictCount stats + 1}
bumpRestartI =
  updateStats \stats ->
    stats
      { observedRestartCount =
          observedRestartCount stats + 1
      }

bumpLiteralInspectionsI ::
  Int ->
  Instrumentation %1 ->
  Instrumentation
bumpLiteralInspectionsI count =
  updateStats \stats ->
    stats
      { literalInspectionCount =
          literalInspectionCount stats + count
      }

recordBacktrackI ::
  Bool ->
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  Instrumentation %1 ->
  Instrumentation
recordBacktrackI isRestart boundaryReads trailReads clears valuationReads boundaryProbes =
  updateStats \stats ->
    stats
      { backtrackCallCount = backtrackCallCount stats + 1
      , backtrackBoundaryReadCount =
          backtrackBoundaryReadCount stats + boundaryReads
      , backtrackTrailReadCount =
          backtrackTrailReadCount stats + trailReads
      , backtrackClearedCount =
          backtrackClearedCount stats + clears
      , backtrackValuationReadCount =
          backtrackValuationReadCount stats + valuationReads
      , backtrackValuationWriteCount =
          backtrackValuationWriteCount stats + clears
      , backtrackQueueRestoreCount =
          backtrackQueueRestoreCount stats + clears
      , backtrackBoundaryProbeCount =
          backtrackBoundaryProbeCount stats + boundaryProbes
      , backtrackNoOpCount =
          backtrackNoOpCount stats
            + if clears == 0 then 1 else 0
      , backtrackMaxSuffix =
          max (backtrackMaxSuffix stats) clears
      , ordinaryBacktrackCount =
          ordinaryBacktrackCount stats
            + if isRestart then 0 else 1
      , restartBacktrackCount =
          restartBacktrackCount stats
            + if isRestart then 1 else 0
      }
#else
bumpSeedScanI,
  bumpPostDrainScanI,
  bumpAssignmentI,
  bumpTrailAppendI,
  bumpDuplicateEnqueueI,
  bumpPropagationEventI,
  bumpWatchVisitI,
  bumpWatchMoveI,
  bumpDecisionI,
  bumpConflictI,
  bumpRestartI ::
    Instrumentation %1 -> Instrumentation
bumpSeedScanI = id
bumpPostDrainScanI = id
bumpAssignmentI = id
bumpTrailAppendI = id
bumpDuplicateEnqueueI = id
bumpPropagationEventI = id
bumpWatchVisitI = id
bumpWatchVisitsI ::
  Int ->
  Instrumentation %1 ->
  Instrumentation
bumpWatchVisitsI _ = id
bumpWatchMoveI = id
bumpWatchMovesI ::
  Int ->
  Instrumentation %1 ->
  Instrumentation
bumpWatchMovesI _ = id
bumpDecisionI = id
bumpConflictI = id
bumpRestartI = id

bumpLiteralInspectionsI ::
  Int ->
  Instrumentation %1 ->
  Instrumentation
bumpLiteralInspectionsI _ = id

recordBacktrackI ::
  Bool ->
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  Instrumentation %1 ->
  Instrumentation
recordBacktrackI _ _ _ _ _ _ = id
#endif
