{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoImplicitPrelude #-}

{- |
Canonical first-UIP analysis over already-split, rank-2 pinned stores.

This is the analysis counterpart of the propagation kernel: it is the sole
unsafe boundary for the bulk loop, and every pin is returned unchanged.
-}
module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Analysis.Kernel.Internal (
  AnalysisPins (..),
  ConflictAnalysis (..),
  analyzeConflict,
  applyAnalysisStats,
) where

import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.BO.Unsafe (unsafeSystemIOToBO)
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.IntPSQ qualified as PSQ
import Data.Ord (Down (..))
import Data.Semigroup (Max (..))
import Data.Vector.Mutable qualified as MV
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import Data.Word (Word64)
import Logic.Propositional.Classical.SAT.CDCL.Types
#ifdef HERBRAND_CDCL_INSTRUMENTED
import Logic.Propositional.Syntax.General (Literal)
#endif
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as NonLinear

data AnalysisPins literalsPin valuationPin trailPin epochPin stampsPin scratchPin where
  AnalysisPins ::
    Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit)) %1 ->
    Fixed.Pinned valuationPin Variable %1 ->
    Fixed.Pinned trailPin Lit %1 ->
    Fixed.Pinned epochPin Word64 %1 ->
    Fixed.Pinned stampsPin Word64 %1 ->
    Fixed.Pinned scratchPin Lit %1 ->
    AnalysisPins literalsPin valuationPin trailPin epochPin stampsPin scratchPin

data ConflictAnalysis
  = RootConflict {-# UNPACK #-} !Int
  | LearnedClause
      {-# UNPACK #-} !DecideLevel
      !Clause
      {-# UNPACK #-} !Lit
      !AnalysisMetrics

#ifdef HERBRAND_CDCL_INSTRUMENTED
data AnalysisMetrics = AnalysisMetrics
  { metricConflictClauseVisitCount :: {-# UNPACK #-} !Int
  , metricReasonClauseVisitCount :: {-# UNPACK #-} !Int
  , metricConflictLiteralVisitCount :: {-# UNPACK #-} !Int
  , metricReasonLiteralVisitCount :: {-# UNPACK #-} !Int
  , metricTrailReadCount :: {-# UNPACK #-} !Int
  , metricPivotCount :: {-# UNPACK #-} !Int
  , metricMarkCount :: {-# UNPACK #-} !Int
  , metricDuplicateMarkCount :: {-# UNPACK #-} !Int
  , metricEpochClearCount :: {-# UNPACK #-} !Int
  , metricSortComparisonCount :: {-# UNPACK #-} !Int
  , metricSortSwapCount :: {-# UNPACK #-} !Int
  , metricPivotTraceRev :: ![Lit]
  }
#else
data AnalysisMetrics = AnalysisMetrics
#endif

data AnalysisAcc = AnalysisAcc
  { analysisPathCount :: {-# UNPACK #-} !Int
  , analysisScratchLength :: {-# UNPACK #-} !Int
  , analysisTargetLevel :: {-# UNPACK #-} !DecideLevel
  , analysisTargetLit :: {-# UNPACK #-} !Lit
  , analysisMetrics :: !AnalysisMetrics
  }

analyzeConflict ::
  CDCLOptions ->
  DecideLevel ->
  Int ->
  ClauseId ->
  VSIDSState s %1 ->
  AnalysisPins literalsPin valuationPin trailPin epochPin stampsPin scratchPin %1 ->
  BO
    scope
    ( Ur ConflictAnalysis
    , VSIDSState s
    , AnalysisPins literalsPin valuationPin trailPin epochPin stampsPin scratchPin
    )
{-# NOINLINE analyzeConflict #-}
analyzeConflict options currentLevel trailLength conflictClause =
  Unsafe.toLinear \vsids ->
    Unsafe.toLinear
      \pins@(AnalysisPins (Boxed.PinnedBuffer literals) (Fixed.Pinned valuation) (Fixed.Pinned trail) (Fixed.Pinned epochStore) (Fixed.Pinned stamps) (Fixed.Pinned scratch)) ->
        unsafeSystemIOToBO do
          !oldEpoch <- UM.unsafeRead epochStore 0
          (!result, !newEpoch, !updatedVSIDS) <-
            analyzeIO
              options
              currentLevel
              trailLength
              conflictClause
              oldEpoch
              vsids
              literals
              valuation
              trail
              stamps
              scratch
          UM.unsafeWrite epochStore 0 newEpoch
          NonLinear.pure
            (Ur result, updatedVSIDS, pins)

analyzeIO ::
  CDCLOptions ->
  DecideLevel ->
  Int ->
  ClauseId ->
  Word64 ->
  VSIDSState s ->
  MV.IOVector (Ur (U.Vector Lit)) ->
  UM.IOVector Variable ->
  UM.IOVector Lit ->
  UM.IOVector Word64 ->
  UM.IOVector Lit ->
  NonLinear.IO (ConflictAnalysis, Word64, VSIDSState s)
analyzeIO options currentLevel trailLength conflictClause oldEpoch vsids literals valuation trail stamps scratch = do
  Ur conflictLits <- MV.unsafeRead literals (unClauseId conflictClause)
  let !decayedVSIDS = decayActivities options vsids
  if currentLevel NonLinear.== 0
    then
      NonLinear.pure
        (RootConflict (U.length conflictLits), oldEpoch, decayedVSIDS)
    else do
      (!epoch, !epochCleared) <-
        if oldEpoch == maxBound
          then do
            UM.set stamps 0
            NonLinear.pure (1, True)
          else NonLinear.pure (oldEpoch + 1, False)
      !initialAcc <-
        scanAnalysisClause
          currentLevel
          epoch
          Nothing
          conflictLits
          (initialAnalysisAcc (U.length conflictLits) epochCleared)
          stamps
          scratch
          valuation
      if analysisPathCount initialAcc <= 0
        then
          NonLinear.error
            ( "positive-level conflict has no current-level path: "
                <> NonLinear.show (conflictClause, currentLevel)
            )
        else
          seek
            options
            currentLevel
            (trailLength - 1)
            initialAcc
            epoch
            decayedVSIDS
            literals
            valuation
            trail
            stamps
            scratch

seek ::
  CDCLOptions ->
  DecideLevel ->
  Int ->
  AnalysisAcc ->
  Word64 ->
  VSIDSState s ->
  MV.IOVector (Ur (U.Vector Lit)) ->
  UM.IOVector Variable ->
  UM.IOVector Lit ->
  UM.IOVector Word64 ->
  UM.IOVector Lit ->
  NonLinear.IO (ConflictAnalysis, Word64, VSIDSState s)
seek options currentLevel cursor acc epoch vsids literals valuation trail stamps scratch
  | cursor < 0 =
      NonLinear.error
        "first-UIP analysis exhausted the trail before finding a marked pivot"
  | otherwise = do
      !assignedLit <- UM.unsafeRead trail cursor
      let !accRead = noteAnalysisTrailRead acc
          !variableIndex = fromVarId (litVar assignedLit)
      !stamp <- UM.unsafeRead stamps variableIndex
      if stamp /= epoch
        then
          seek
            options
            currentLevel
            (cursor - 1)
            accRead
            epoch
            vsids
            literals
            valuation
            trail
            stamps
            scratch
        else do
          let !remainingPaths = analysisPathCount accRead - 1
              !nextAcc =
                noteAnalysisPivot
                  assignedLit
                  accRead {analysisPathCount = remainingPaths}
          UM.unsafeWrite stamps variableIndex 0
          if remainingPaths == 0
            then do
              !result <-
                finishAnalysis
                  (negL assignedLit)
                  nextAcc
                  scratch
              NonLinear.pure (result, epoch, vsids)
            else
              if remainingPaths < 0
                then
                  NonLinear.error
                    "first-UIP path counter became negative"
                else do
                  !variable <- UM.unsafeRead valuation variableIndex
                  case variable of
                    Indefinite ->
                      NonLinear.error
                        ( "marked trail pivot is unassigned: "
                            <> NonLinear.show assignedLit
                        )
                    Definite {antecedent = Nothing} ->
                      NonLinear.error
                        ( "reasonless decision selected before the final UIP: "
                            <> NonLinear.show assignedLit
                        )
                    Definite
                      { antecedent = Just reason
                      , decisionStep = pivotStep
                      } -> do
                        Ur reasonLits <-
                          MV.unsafeRead literals (unClauseId reason)
                        let !updatedVSIDS =
                              if activateResolved options
                                then incrementActivity assignedLit vsids
                                else vsids
                        !scannedAcc <-
                          scanAnalysisClause
                            currentLevel
                            epoch
                            (Just (assignedLit, pivotStep))
                            reasonLits
                            nextAcc
                            stamps
                            scratch
                            valuation
                        seek
                          options
                          currentLevel
                          (cursor - 1)
                          scannedAcc
                          epoch
                          updatedVSIDS
                          literals
                          valuation
                          trail
                          stamps
                          scratch

scanAnalysisClause ::
  DecideLevel ->
  Word64 ->
  Maybe (Lit, Step) ->
  U.Vector Lit ->
  AnalysisAcc ->
  UM.IOVector Word64 ->
  UM.IOVector Lit ->
  UM.IOVector Variable ->
  NonLinear.IO AnalysisAcc
scanAnalysisClause currentLevel epoch pivot clause initialAcc stamps scratch valuation =
  go 0 (noteAnalysisClauseScan pivot literalCount initialAcc) 0
  where
    !literalCount = U.length clause

    go :: Int -> AnalysisAcc -> Int -> NonLinear.IO AnalysisAcc
    go !index !acc !pivotOccurrences
      | index == literalCount =
          case pivot of
            Nothing -> NonLinear.pure acc
            Just {}
              | pivotOccurrences == 1 -> NonLinear.pure acc
              | otherwise ->
                  NonLinear.error
                    ( "analysis reason contains its pivot "
                        <> NonLinear.show pivotOccurrences
                        <> " times"
                    )
      | otherwise = do
          let !literal = U.unsafeIndex clause index
          case pivot of
            Just (pivotLit, _)
              | litVar literal NonLinear.== litVar pivotLit ->
                  if literal NonLinear.== pivotLit
                    then go (index + 1) acc (pivotOccurrences + 1)
                    else
                      NonLinear.error
                        ( "analysis reason contains the pivot with opposite polarity: "
                            <> NonLinear.show (pivotLit, literal)
                        )
            _ -> do
              let !variableIndex = fromVarId (litVar literal)
              !variable <- UM.unsafeRead valuation variableIndex
              case variable of
                Indefinite ->
                  NonLinear.error
                    ( "analysis clause contains an unassigned literal: "
                        <> NonLinear.show literal
                    )
                Definite
                  { decideLevel
                  , decisionStep
                  , value
                  }
                    | literalValue literal value ->
                        NonLinear.error
                          ( "analysis clause contains a true literal: "
                              <> NonLinear.show literal
                          )
                    | decideLevel NonLinear.> currentLevel ->
                        NonLinear.error
                          ( "analysis clause literal exceeds the conflict level: "
                              <> NonLinear.show
                                (literal, decideLevel, currentLevel)
                          )
                    | otherwise -> do
                        validateReasonPrecedence pivot literal decisionStep
                        !stamp <- UM.unsafeRead stamps variableIndex
                        if stamp == epoch
                          then
                            go
                              (index + 1)
                              (noteAnalysisDuplicateMark acc)
                              pivotOccurrences
                          else do
                            UM.unsafeWrite stamps variableIndex epoch
                            let !markedAcc = noteAnalysisMark acc
                            if decideLevel NonLinear.== currentLevel
                              then
                                go
                                  (index + 1)
                                  markedAcc
                                    { analysisPathCount =
                                        analysisPathCount markedAcc + 1
                                    }
                                  pivotOccurrences
                              else do
                                let !scratchIndex =
                                      analysisScratchLength markedAcc
                                    (!targetLevel, !targetLit)
                                      | scratchIndex
                                          == 0
                                          || decideLevel
                                          NonLinear.> analysisTargetLevel markedAcc
                                            || ( decideLevel
                                                   NonLinear.== analysisTargetLevel markedAcc
                                                     && literal
                                                   NonLinear.< analysisTargetLit markedAcc
                                               ) =
                                          (decideLevel, literal)
                                      | otherwise =
                                          ( analysisTargetLevel markedAcc
                                          , analysisTargetLit markedAcc
                                          )
                                UM.unsafeWrite
                                  scratch
                                  scratchIndex
                                  literal
                                go
                                  (index + 1)
                                  markedAcc
                                    { analysisScratchLength =
                                        scratchIndex + 1
                                    , analysisTargetLevel = targetLevel
                                    , analysisTargetLit = targetLit
                                    }
                                  pivotOccurrences

finishAnalysis ::
  Lit ->
  AnalysisAcc ->
  UM.IOVector Lit ->
  NonLinear.IO ConflictAnalysis
finishAnalysis assertingLit acc scratch = do
  let !scratchLength = analysisScratchLength acc
      !scratchCapacity = UM.length scratch
  if scratchLength < 0 || scratchLength > scratchCapacity
    then
      NonLinear.error
        ( "learned-literal scratch prefix is out of bounds: "
            <> NonLinear.show (scratchLength, scratchCapacity)
        )
    else do
      (!comparisons, !swaps) <- heapSortLitPrefix scratchLength scratch
      let !metrics =
            noteAnalysisSort comparisons swaps (analysisMetrics acc)
          !learnedLength = scratchLength + 1
          !hasLowerLiterals = scratchLength > 0
          !target =
            if hasLowerLiterals
              then analysisTargetLevel acc
              else 0
      output <- UM.new learnedLength
      UM.unsafeWrite output 0 assertingLit
      (!copiedLength, !targetMatches) <-
        if hasLowerLiterals
          then do
            UM.unsafeWrite output 1 (analysisTargetLit acc)
            copyLowerLiterals
              0
              2
              scratchLength
              (analysisTargetLit acc)
              0
              scratch
              output
          else NonLinear.pure (1, 0)
      if copiedLength
        /= learnedLength
        || targetMatches
        /= if hasLowerLiterals then 1 else 0
        then
          NonLinear.error
            ( "learned-clause copy invariant failed: "
                <> NonLinear.show
                  ( copiedLength
                  , learnedLength
                  , targetMatches
                  , hasLowerLiterals
                  )
            )
        else do
          !learnedLits <- U.unsafeFreeze output
          NonLinear.pure
            ( LearnedClause
                target
                Clause
                  { lits = learnedLits
                  , watched1 = 0
                  , watched2 =
                      if learnedLength > 1 then 1 else -1
                  }
                assertingLit
                metrics
            )

copyLowerLiterals ::
  Int ->
  Int ->
  Int ->
  Lit ->
  Int ->
  UM.IOVector Lit ->
  UM.IOVector Lit ->
  NonLinear.IO (Int, Int)
copyLowerLiterals index outputIndex count targetLit targetMatches scratch output
  | index == count =
      NonLinear.pure (outputIndex, targetMatches)
  | otherwise = do
      !literal <- UM.unsafeRead scratch index
      if literal NonLinear.== targetLit
        then
          copyLowerLiterals
            (index + 1)
            outputIndex
            count
            targetLit
            (targetMatches + 1)
            scratch
            output
        else do
          if outputIndex <= count
            then UM.unsafeWrite output outputIndex literal
            else
              NonLinear.error
                "learned-clause output index exceeded its exact allocation"
          copyLowerLiterals
            (index + 1)
            (outputIndex + 1)
            count
            targetLit
            targetMatches
            scratch
            output

heapSortLitPrefix ::
  Int ->
  UM.IOVector Lit ->
  NonLinear.IO (Int, Int)
heapSortLitPrefix count heap
  | count <= 1 = NonLinear.pure (0, 0)
  | otherwise = buildHeap (count `quot` 2 - 1) 0 0
  where
    buildHeap !root !comparisons !swaps
      | root < 0 = drainHeap (count - 1) comparisons swaps
      | otherwise = do
          (!comparisons', !swaps') <-
            siftDownLit root (count - 1) comparisons swaps heap
          buildHeap (root - 1) comparisons' swaps'

    drainHeap !end !comparisons !swaps
      | end <= 0 = NonLinear.pure (comparisons, swaps)
      | otherwise = do
          swapLit 0 end heap
          (!comparisons', !swaps') <-
            siftDownLit 0 (end - 1) comparisons (swaps + 1) heap
          drainHeap (end - 1) comparisons' swaps'

siftDownLit ::
  Int ->
  Int ->
  Int ->
  Int ->
  UM.IOVector Lit ->
  NonLinear.IO (Int, Int)
siftDownLit root end comparisons swaps heap = do
  let !leftChild = 2 * root + 1
  if leftChild > end
    then NonLinear.pure (comparisons, swaps)
    else do
      !leftLit <- UM.unsafeRead heap leftChild
      let !rightChild = leftChild + 1
      (!child, !childLit, !comparisons') <-
        if rightChild > end
          then NonLinear.pure (leftChild, leftLit, comparisons)
          else do
            !rightLit <- UM.unsafeRead heap rightChild
            NonLinear.pure
              ( if leftLit NonLinear.< rightLit
                  then (rightChild, rightLit, comparisons + 1)
                  else (leftChild, leftLit, comparisons + 1)
              )
      !rootLit <- UM.unsafeRead heap root
      let !comparisons'' = comparisons' + 1
      if rootLit NonLinear.< childLit
        then do
          UM.unsafeWrite heap root childLit
          UM.unsafeWrite heap child rootLit
          siftDownLit
            child
            end
            comparisons''
            (swaps + 1)
            heap
        else NonLinear.pure (comparisons'', swaps)

swapLit :: Int -> Int -> UM.IOVector Lit -> NonLinear.IO ()
swapLit left right array
  | left == right = NonLinear.pure ()
  | otherwise = do
      !leftLit <- UM.unsafeRead array left
      !rightLit <- UM.unsafeRead array right
      UM.unsafeWrite array left rightLit
      UM.unsafeWrite array right leftLit

literalValue :: Lit -> Bool -> Bool
literalValue literal variableValue =
  if isPositive literal then variableValue else NonLinear.not variableValue

initialAnalysisAcc :: Int -> Bool -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
initialAnalysisAcc conflictLiteralCount epochCleared =
  AnalysisAcc
    { analysisPathCount = 0
    , analysisScratchLength = 0
    , analysisTargetLevel = -1
    , analysisTargetLit = NegL (VarId maxBound)
    , analysisMetrics =
        AnalysisMetrics
          { metricConflictClauseVisitCount = 1
          , metricReasonClauseVisitCount = 0
          , metricConflictLiteralVisitCount = conflictLiteralCount
          , metricReasonLiteralVisitCount = 0
          , metricTrailReadCount = 0
          , metricPivotCount = 0
          , metricMarkCount = 0
          , metricDuplicateMarkCount = 0
          , metricEpochClearCount = if epochCleared then 1 else 0
          , metricSortComparisonCount = 0
          , metricSortSwapCount = 0
          , metricPivotTraceRev = []
          }
    }
#else
initialAnalysisAcc _ _ =
  AnalysisAcc
    { analysisPathCount = 0
    , analysisScratchLength = 0
    , analysisTargetLevel = -1
    , analysisTargetLit = NegL (VarId maxBound)
    , analysisMetrics = AnalysisMetrics
    }
#endif

noteAnalysisClauseScan ::
  Maybe (Lit, Step) ->
  Int ->
  AnalysisAcc ->
  AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisClauseScan Nothing _ acc = acc
noteAnalysisClauseScan Just {} literalCount acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics
          { metricReasonClauseVisitCount =
              metricReasonClauseVisitCount metrics + 1
          , metricReasonLiteralVisitCount =
              metricReasonLiteralVisitCount metrics + literalCount
          }
    }
#else
{-# INLINE noteAnalysisClauseScan #-}
noteAnalysisClauseScan _ _ acc = acc
#endif

noteAnalysisTrailRead :: AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisTrailRead acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics
          { metricTrailReadCount =
              metricTrailReadCount metrics + 1
          }
    }
#else
{-# INLINE noteAnalysisTrailRead #-}
noteAnalysisTrailRead acc = acc
#endif

noteAnalysisPivot :: Lit -> AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisPivot literal acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics
          { metricPivotCount = metricPivotCount metrics + 1
          , metricPivotTraceRev =
              literal : metricPivotTraceRev metrics
          }
    }
#else
{-# INLINE noteAnalysisPivot #-}
noteAnalysisPivot _ acc = acc
#endif

noteAnalysisMark :: AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisMark acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics {metricMarkCount = metricMarkCount metrics + 1}
    }
#else
{-# INLINE noteAnalysisMark #-}
noteAnalysisMark acc = acc
#endif

noteAnalysisDuplicateMark :: AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisDuplicateMark acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics
          { metricDuplicateMarkCount =
              metricDuplicateMarkCount metrics + 1
          }
    }
#else
{-# INLINE noteAnalysisDuplicateMark #-}
noteAnalysisDuplicateMark acc = acc
#endif

noteAnalysisSort :: Int -> Int -> AnalysisMetrics -> AnalysisMetrics
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisSort comparisons swaps metrics =
  metrics
    { metricSortComparisonCount =
        metricSortComparisonCount metrics + comparisons
    , metricSortSwapCount = metricSortSwapCount metrics + swaps
    }
#else
{-# INLINE noteAnalysisSort #-}
noteAnalysisSort _ _ metrics = metrics
#endif

validateReasonPrecedence ::
  Maybe (Lit, Step) ->
  Lit ->
  Step ->
  NonLinear.IO ()
#ifdef HERBRAND_CDCL_INSTRUMENTED
validateReasonPrecedence Nothing _ _ = NonLinear.pure ()
validateReasonPrecedence (Just (pivot, pivotStep)) literal introducedAt
  | introducedAt NonLinear.< pivotStep = NonLinear.pure ()
  | otherwise =
      NonLinear.error
        ( "reason literal does not precede its pivot: "
            <> NonLinear.show
              (pivot, pivotStep, literal, introducedAt)
        )
#else
{-# INLINE validateReasonPrecedence #-}
validateReasonPrecedence _ _ _ = NonLinear.pure ()
#endif

decayActivities :: CDCLOptions -> VSIDSState s -> VSIDSState s
decayActivities options (VSIDSState unsatisfied satisfied ema exceeds increment) =
  VSIDSState
    unsatisfied
    satisfied
    ema
    exceeds
    case decayFactor options of
      ConstantFactor alpha -> increment / alpha
      Adaptive {lowLBDDecay, highLBDDecay}
        | exceeds -> increment / highLBDDecay
        | otherwise -> increment / lowLBDDecay

incrementActivity :: Lit -> VSIDSState s -> VSIDSState s
incrementActivity literal (VSIDSState unsatisfied satisfied ema exceeds increment) =
  let (!unsatisfiedMaximum, !updatedUnsatisfied) =
        incrementQueue increment literal unsatisfied
      (!satisfiedMaximum, !updatedSatisfied) =
        incrementQueue increment literal satisfied
   in rescaleActivities
        (unsatisfiedMaximum NonLinear.<> satisfiedMaximum)
        ( VSIDSState
            updatedUnsatisfied
            updatedSatisfied
            ema
            exceeds
            increment
        )

incrementQueue ::
  Double ->
  Lit ->
  VarQueue ->
  (Maybe (Max Double), VarQueue)
incrementQueue increment literal =
  PSQ.alter
    ( \case
        Nothing -> (Nothing, Nothing)
        Just (priority, ()) ->
          let !updatedPriority =
                Down (getDown priority NonLinear.+ increment)
           in ( Just (Max (getDown updatedPriority))
              , Just (updatedPriority, ())
              )
    )
    (fromVarId (litVar literal))

rescaleActivities ::
  Maybe (Max Double) ->
  VSIDSState s ->
  VSIDSState s
rescaleActivities maximumActivity state =
  case maximumActivity of
    Just (Max priority)
      | priority >= 1e100 ->
          case state of
            VSIDSState unsatisfied satisfied ema exceeds increment ->
              VSIDSState
                (scaleQueue 1e-100 unsatisfied)
                (scaleQueue 1e-100 satisfied)
                ema
                exceeds
                (increment * 1e-100)
    _ -> state

scaleQueue :: Double -> VarQueue -> VarQueue
scaleQueue factor =
  PSQ.unsafeMapMonotonic \_ (Down priority) value ->
    (Down (priority * factor), value)

applyAnalysisStats :: ConflictAnalysis -> SolverStats -> SolverStats
#ifdef HERBRAND_CDCL_INSTRUMENTED
applyAnalysisStats (RootConflict conflictLiteralCount) stats =
  stats
    { analysisCount = analysisCount stats + 1
    , analysisRootConflictCount =
        analysisRootConflictCount stats + 1
    , analysisConflictClauseVisitCount =
        analysisConflictClauseVisitCount stats + 1
    , analysisConflictLiteralVisitCount =
        analysisConflictLiteralVisitCount stats
          + conflictLiteralCount
    }
applyAnalysisStats
  (LearnedClause target Clause {lits = learnedLits} _ AnalysisMetrics {..})
  stats =
    stats
      { analysisCount = analysisCount stats + 1
      , analysisConflictClauseVisitCount =
          analysisConflictClauseVisitCount stats
            + metricConflictClauseVisitCount
      , analysisReasonClauseVisitCount =
          analysisReasonClauseVisitCount stats
            + metricReasonClauseVisitCount
      , analysisConflictLiteralVisitCount =
          analysisConflictLiteralVisitCount stats
            + metricConflictLiteralVisitCount
      , analysisReasonLiteralVisitCount =
          analysisReasonLiteralVisitCount stats
            + metricReasonLiteralVisitCount
      , analysisTrailReadCount =
          analysisTrailReadCount stats + metricTrailReadCount
      , analysisPivotCount =
          analysisPivotCount stats + metricPivotCount
      , analysisMarkCount =
          analysisMarkCount stats + metricMarkCount
      , analysisDuplicateMarkCount =
          analysisDuplicateMarkCount stats
            + metricDuplicateMarkCount
      , analysisLearnedLiteralCount =
          analysisLearnedLiteralCount stats + U.length learnedLits
      , analysisEpochClearCount =
          analysisEpochClearCount stats + metricEpochClearCount
      , analysisSortComparisonCount =
          analysisSortComparisonCount stats
            + metricSortComparisonCount
      , analysisSortSwapCount =
          analysisSortSwapCount stats + metricSortSwapCount
      , analysisLastTargetLevel = unDecideLevel target
      , analysisLastPivotTrace =
          NonLinear.map decodeMetricLit
            (NonLinear.reverse metricPivotTraceRev)
      , analysisLastLearnedClause =
          NonLinear.map decodeMetricLit (U.toList learnedLits)
      , analysisLearnedTrace =
          ( NonLinear.map decodeMetricLit
              (NonLinear.reverse metricPivotTraceRev)
          , unDecideLevel target
          , NonLinear.map decodeMetricLit (U.toList learnedLits)
          )
            : analysisLearnedTrace stats
      }
  where
    decodeMetricLit :: Lit -> Literal Word
    decodeMetricLit =
      NonLinear.fmap
        (NonLinear.fromIntegral NonLinear.. fromVarId)
        NonLinear.. decodeLit
#else
{-# INLINE applyAnalysisStats #-}
applyAnalysisStats _ stats = stats
#endif
