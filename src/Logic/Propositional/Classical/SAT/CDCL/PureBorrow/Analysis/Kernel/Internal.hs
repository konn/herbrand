{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoImplicitPrelude #-}

{- |
Canonical first-UIP analysis over locally split borrowed stores.
-}
module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Analysis.Kernel.Internal (
  AnalysisPins (..),
  ConflictAnalysis (..),
  analyzeConflict,
  applyAnalysisStats,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.IntPSQ qualified as PSQ
import Data.Ord (Down (..))
import Data.Semigroup (Max (..))
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Unboxed qualified as U
import Data.Word (Word64)
import Logic.Propositional.Classical.SAT.CDCL.Types
#ifdef HERBRAND_CDCL_INSTRUMENTED
import Logic.Propositional.Syntax.General (Literal)
#endif
import Prelude.Linear
import Prelude qualified as NonLinear

data AnalysisPins α where
  AnalysisPins ::
    Boxed.PinnedBuffer α (Ur (U.Vector Lit)) %1 ->
    Fixed.Pinned α Variable %1 ->
    Fixed.Pinned α Lit %1 ->
    Fixed.Pinned α Word64 %1 ->
    Fixed.Pinned α Word64 %1 ->
    Fixed.Pinned α Lit %1 ->
    AnalysisPins α

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
  AnalysisPins α %1 ->
  BO
    α
    ( Ur ConflictAnalysis
    , VSIDSState s
    , AnalysisPins α
    )
{-# NOINLINE analyzeConflict #-}
analyzeConflict options currentLevel trailLength conflictClause vsids pins =
  case move vsids of
    Ur unrestrictedVSIDS ->
      analyzeConflictMoved
        options
        currentLevel
        trailLength
        conflictClause
        unrestrictedVSIDS
        pins

analyzeConflictMoved ::
  CDCLOptions ->
  DecideLevel ->
  Int ->
  ClauseId ->
  VSIDSState s ->
  AnalysisPins α %1 ->
  BO
    α
    ( Ur ConflictAnalysis
    , VSIDSState s
    , AnalysisPins α
    )
{-# INLINE analyzeConflictMoved #-}
analyzeConflictMoved options currentLevel trailLength conflictClause vsids (AnalysisPins literals valuation trail epochStore stamps scratch) = Control.do
  (Ur oldEpoch, epochStore) <-
    Fixed.pinnedUnsafeCopyAt 0 epochStore
  (Ur (Ur conflictLits), literals) <-
    Boxed.pinnedBufferUnsafeCopyAt
      (unClauseId conflictClause)
      literals
  let !decayedVSIDS = decayActivities options vsids
  if currentLevel NonLinear.== 0
    then
      Control.pure
        ( Ur (RootConflict (U.length conflictLits))
        , decayedVSIDS
        , AnalysisPins literals valuation trail epochStore stamps scratch
        )
    else Control.do
      (Ur (epoch, epochCleared), stamps) <-
        advanceAnalysisEpoch oldEpoch stamps
      (Ur initialAcc, stamps, scratch, valuation) <-
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
          error
            ( "positive-level conflict has no current-level path: "
                <> NonLinear.show (conflictClause, currentLevel)
            )
            decayedVSIDS
            literals
            valuation
            trail
            epochStore
            stamps
            scratch
        else Control.do
          ( Ur result
            , updatedVSIDS
            , literals
            , valuation
            , trail
            , stamps
            , scratch
            ) <-
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
          epochStore <-
            Fixed.pinnedUnsafeWrite 0 epoch epochStore
          Control.pure
            ( Ur result
            , updatedVSIDS
            , AnalysisPins
                literals
                valuation
                trail
                epochStore
                stamps
                scratch
            )

advanceAnalysisEpoch ::
  Word64 ->
  Fixed.Pinned α Word64 %1 ->
  BO α (Ur (Word64, Bool), Fixed.Pinned α Word64)
{-# INLINE advanceAnalysisEpoch #-}
advanceAnalysisEpoch oldEpoch stamps =
  if oldEpoch NonLinear.== maxBound
    then Control.do
      stamps <- clearStamps 0 stamps
      Control.pure (Ur (1, True), stamps)
    else Control.pure (Ur (oldEpoch + 1, False), stamps)

clearStamps ::
  Int ->
  Fixed.Pinned α Word64 %1 ->
  BO α (Fixed.Pinned α Word64)
{-# INLINE clearStamps #-}
clearStamps !index stamps =
  case Fixed.pinnedSize stamps of
    (Ur length_, stamps)
      | index NonLinear.>= length_ -> Control.pure stamps
      | otherwise -> Control.do
          stamps <- Fixed.pinnedUnsafeWrite index 0 stamps
          clearStamps (index + 1) stamps

seek ::
  CDCLOptions ->
  DecideLevel ->
  Int ->
  AnalysisAcc ->
  Word64 ->
  VSIDSState s ->
  Boxed.PinnedBuffer α (Ur (U.Vector Lit)) %1 ->
  Fixed.Pinned α Variable %1 ->
  Fixed.Pinned α Lit %1 ->
  Fixed.Pinned α Word64 %1 ->
  Fixed.Pinned α Lit %1 ->
  BO
    α
    ( Ur ConflictAnalysis
    , VSIDSState s
    , Boxed.PinnedBuffer α (Ur (U.Vector Lit))
    , Fixed.Pinned α Variable
    , Fixed.Pinned α Lit
    , Fixed.Pinned α Word64
    , Fixed.Pinned α Lit
    )
seek options currentLevel cursor acc epoch vsids literals valuation trail stamps scratch
  | cursor < 0 =
      error
        "first-UIP analysis exhausted the trail before finding a marked pivot"
        vsids
        literals
        valuation
        trail
        stamps
        scratch
  | otherwise = Control.do
      (Ur assignedLit, trail) <-
        Fixed.pinnedUnsafeCopyAt cursor trail
      let !accRead = noteAnalysisTrailRead acc
          !variableIndex = fromVarId (litVar assignedLit)
      (Ur stamp, stamps) <-
        Fixed.pinnedUnsafeCopyAt variableIndex stamps
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
        else Control.do
          let !remainingPaths = analysisPathCount accRead - 1
              !nextAcc =
                noteAnalysisPivot
                  assignedLit
                  accRead {analysisPathCount = remainingPaths}
          stamps <- Fixed.pinnedUnsafeWrite variableIndex 0 stamps
          if remainingPaths == 0
            then Control.do
              (Ur result, scratch) <-
                finishAnalysis
                  (negL assignedLit)
                  nextAcc
                  scratch
              Control.pure
                ( Ur result
                , vsids
                , literals
                , valuation
                , trail
                , stamps
                , scratch
                )
            else
              if remainingPaths < 0
                then
                  error
                    "first-UIP path counter became negative"
                    vsids
                    literals
                    valuation
                    trail
                    stamps
                    scratch
                else Control.do
                  (Ur variable, valuation) <-
                    Fixed.pinnedUnsafeCopyAt variableIndex valuation
                  case variable of
                    Indefinite ->
                      error
                        ( "marked trail pivot is unassigned: "
                            <> NonLinear.show assignedLit
                        )
                        vsids
                        literals
                        valuation
                        trail
                        stamps
                        scratch
                    Definite {antecedent = Nothing} ->
                      error
                        ( "reasonless decision selected before the final UIP: "
                            <> NonLinear.show assignedLit
                        )
                        vsids
                        literals
                        valuation
                        trail
                        stamps
                        scratch
                    Definite
                      { antecedent = Just reason
                      , decisionStep = pivotStep
                      } -> Control.do
                        (Ur (Ur reasonLits), literals) <-
                          Boxed.pinnedBufferUnsafeCopyAt
                            (unClauseId reason)
                            literals
                        let !updatedVSIDS =
                              if activateResolved options
                                then incrementActivity assignedLit vsids
                                else vsids
                        (Ur scannedAcc, stamps, scratch, valuation) <-
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
  Fixed.Pinned α Word64 %1 ->
  Fixed.Pinned α Lit %1 ->
  Fixed.Pinned α Variable %1 ->
  BO
    α
    ( Ur AnalysisAcc
    , Fixed.Pinned α Word64
    , Fixed.Pinned α Lit
    , Fixed.Pinned α Variable
    )
scanAnalysisClause currentLevel epoch pivot clause initialAcc stamps scratch valuation =
  go
    0
    (noteAnalysisClauseScan pivot literalCount initialAcc)
    0
    stamps
    scratch
    valuation
  where
    !literalCount = U.length clause

    go ::
      Int ->
      AnalysisAcc ->
      Int ->
      Fixed.Pinned α Word64 %1 ->
      Fixed.Pinned α Lit %1 ->
      Fixed.Pinned α Variable %1 ->
      BO
        α
        ( Ur AnalysisAcc
        , Fixed.Pinned α Word64
        , Fixed.Pinned α Lit
        , Fixed.Pinned α Variable
        )
    go !index !acc !pivotOccurrences stamps scratch valuation
      | index == literalCount =
          case pivot of
            Nothing -> Control.pure (Ur acc, stamps, scratch, valuation)
            Just {}
              | pivotOccurrences == 1 ->
                  Control.pure (Ur acc, stamps, scratch, valuation)
              | otherwise ->
                  error
                    ( "analysis reason contains its pivot "
                        <> NonLinear.show pivotOccurrences
                        <> " times"
                    )
                    stamps
                    scratch
                    valuation
      | otherwise =
          let !literal = U.unsafeIndex clause index
           in case pivot of
                Just (pivotLit, _)
                  | litVar literal NonLinear.== litVar pivotLit ->
                      if literal NonLinear.== pivotLit
                        then
                          go
                            (index + 1)
                            acc
                            (pivotOccurrences + 1)
                            stamps
                            scratch
                            valuation
                        else
                          error
                            ( "analysis reason contains the pivot with opposite polarity: "
                                <> NonLinear.show (pivotLit, literal)
                            )
                            stamps
                            scratch
                            valuation
                _ -> Control.do
                  let !variableIndex = fromVarId (litVar literal)
                  (Ur variable, valuation) <-
                    Fixed.pinnedUnsafeCopyAt variableIndex valuation
                  case variable of
                    Indefinite ->
                      error
                        ( "analysis clause contains an unassigned literal: "
                            <> NonLinear.show literal
                        )
                        stamps
                        scratch
                        valuation
                    Definite
                      { decideLevel
                      , decisionStep
                      , value
                      }
                        | literalValue literal value ->
                            error
                              ( "analysis clause contains a true literal: "
                                  <> NonLinear.show literal
                              )
                              stamps
                              scratch
                              valuation
                        | decideLevel NonLinear.> currentLevel ->
                            error
                              ( "analysis clause literal exceeds the conflict level: "
                                  <> NonLinear.show
                                    (literal, decideLevel, currentLevel)
                              )
                              stamps
                              scratch
                              valuation
                        | otherwise ->
                            case validateReasonPrecedence pivot literal decisionStep of
                              () -> Control.do
                                (Ur stamp, stamps) <-
                                  Fixed.pinnedUnsafeCopyAt variableIndex stamps
                                if stamp == epoch
                                  then
                                    go
                                      (index + 1)
                                      (noteAnalysisDuplicateMark acc)
                                      pivotOccurrences
                                      stamps
                                      scratch
                                      valuation
                                  else Control.do
                                    stamps <-
                                      Fixed.pinnedUnsafeWrite
                                        variableIndex
                                        epoch
                                        stamps
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
                                          stamps
                                          scratch
                                          valuation
                                      else Control.do
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
                                        scratch <-
                                          Fixed.pinnedUnsafeWrite
                                            scratchIndex
                                            literal
                                            scratch
                                        go
                                          (index + 1)
                                          markedAcc
                                            { analysisScratchLength =
                                                scratchIndex + 1
                                            , analysisTargetLevel = targetLevel
                                            , analysisTargetLit = targetLit
                                            }
                                          pivotOccurrences
                                          stamps
                                          scratch
                                          valuation

finishAnalysis ::
  Lit ->
  AnalysisAcc ->
  Fixed.Pinned α Lit %1 ->
  BO α (Ur ConflictAnalysis, Fixed.Pinned α Lit)
finishAnalysis assertingLit acc scratch =
  case Fixed.pinnedSize scratch of
    (Ur scratchCapacity, scratch) ->
      let !scratchLength = analysisScratchLength acc
       in if scratchLength < 0 || scratchLength > scratchCapacity
            then
              error
                ( "learned-literal scratch prefix is out of bounds: "
                    <> NonLinear.show (scratchLength, scratchCapacity)
                )
                scratch
            else Control.do
              (Ur (comparisons, swaps), scratch) <-
                heapSortLitPrefix scratchLength scratch
              let !metrics =
                    noteAnalysisSort comparisons swaps (analysisMetrics acc)
                  !learnedLength = scratchLength + 1
                  !hasLowerLiterals = scratchLength > 0
                  !target =
                    if hasLowerLiterals
                      then analysisTargetLevel acc
                      else 0
              (Ur (lowerLiterals, targetMatches), scratch) <-
                if hasLowerLiterals
                  then
                    collectLowerLiterals
                      (scratchLength - 1)
                      scratchLength
                      (analysisTargetLit acc)
                      []
                      0
                      scratch
                  else Control.pure (Ur ([], 0), scratch)
              let !copiedLength =
                    1
                      + if hasLowerLiterals
                        then 1 + scratchLength - targetMatches
                        else 0
              if copiedLength
                /= learnedLength
                || targetMatches
                /= if hasLowerLiterals then 1 else 0
                then
                  error
                    ( "learned-clause copy invariant failed: "
                        <> NonLinear.show
                          ( copiedLength
                          , learnedLength
                          , targetMatches
                          , hasLowerLiterals
                          )
                    )
                    scratch
                else
                  let !learnedLits =
                        U.fromListN
                          learnedLength
                          if hasLowerLiterals
                            then
                              assertingLit
                                : analysisTargetLit acc
                                : lowerLiterals
                            else [assertingLit]
                   in Control.pure
                        ( Ur
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
                        , scratch
                        )

collectLowerLiterals ::
  Int ->
  Int ->
  Lit ->
  [Lit] ->
  Int ->
  Fixed.Pinned α Lit %1 ->
  BO α (Ur ([Lit], Int), Fixed.Pinned α Lit)
collectLowerLiterals !index count targetLit lowerLiterals targetMatches scratch
  | index < 0 =
      Control.pure (Ur (lowerLiterals, targetMatches), scratch)
  | index >= count =
      error
        "learned-clause scratch index exceeded its prefix"
        scratch
  | otherwise = Control.do
      (Ur literal, scratch) <- Fixed.pinnedUnsafeCopyAt index scratch
      if literal NonLinear.== targetLit
        then
          collectLowerLiterals
            (index - 1)
            count
            targetLit
            lowerLiterals
            (targetMatches + 1)
            scratch
        else
          collectLowerLiterals
            (index - 1)
            count
            targetLit
            (literal : lowerLiterals)
            targetMatches
            scratch

heapSortLitPrefix ::
  Int ->
  Fixed.Pinned α Lit %1 ->
  BO α (Ur (Int, Int), Fixed.Pinned α Lit)
heapSortLitPrefix count heap
  | count <= 1 = Control.pure (Ur (0, 0), heap)
  | otherwise = buildHeap (count `quot` 2 - 1) 0 0 heap
  where
    buildHeap !root !comparisons !swaps heap
      | root < 0 = drainHeap (count - 1) comparisons swaps heap
      | otherwise = Control.do
          (Ur (comparisons', swaps'), heap) <-
            siftDownLit root (count - 1) comparisons swaps heap
          buildHeap (root - 1) comparisons' swaps' heap

    drainHeap !end !comparisons !swaps heap
      | end <= 0 = Control.pure (Ur (comparisons, swaps), heap)
      | otherwise = Control.do
          heap <- swapLit 0 end heap
          (Ur (comparisons', swaps'), heap) <-
            siftDownLit 0 (end - 1) comparisons (swaps + 1) heap
          drainHeap (end - 1) comparisons' swaps' heap

siftDownLit ::
  Int ->
  Int ->
  Int ->
  Int ->
  Fixed.Pinned α Lit %1 ->
  BO α (Ur (Int, Int), Fixed.Pinned α Lit)
siftDownLit root end comparisons swaps heap = Control.do
  let !leftChild = 2 * root + 1
  if leftChild > end
    then Control.pure (Ur (comparisons, swaps), heap)
    else Control.do
      (Ur leftLit, heap) <- Fixed.pinnedUnsafeCopyAt leftChild heap
      let !rightChild = leftChild + 1
      (Ur (child, childLit, comparisons'), heap) <-
        if rightChild > end
          then Control.pure (Ur (leftChild, leftLit, comparisons), heap)
          else Control.do
            (Ur rightLit, heap) <-
              Fixed.pinnedUnsafeCopyAt rightChild heap
            Control.pure
              ( Ur
                  ( if leftLit NonLinear.< rightLit
                      then (rightChild, rightLit, comparisons + 1)
                      else (leftChild, leftLit, comparisons + 1)
                  )
              , heap
              )
      (Ur rootLit, heap) <- Fixed.pinnedUnsafeCopyAt root heap
      let !comparisons'' = comparisons' + 1
      if rootLit NonLinear.< childLit
        then Control.do
          heap <- Fixed.pinnedUnsafeWrite root childLit heap
          heap <- Fixed.pinnedUnsafeWrite child rootLit heap
          siftDownLit
            child
            end
            comparisons''
            (swaps + 1)
            heap
        else Control.pure (Ur (comparisons'', swaps), heap)

swapLit ::
  Int ->
  Int ->
  Fixed.Pinned α Lit %1 ->
  BO α (Fixed.Pinned α Lit)
swapLit left right array
  | left == right = Control.pure array
  | otherwise = Control.do
      (Ur leftLit, array) <- Fixed.pinnedUnsafeCopyAt left array
      (Ur rightLit, array) <- Fixed.pinnedUnsafeCopyAt right array
      array <- Fixed.pinnedUnsafeWrite left rightLit array
      Fixed.pinnedUnsafeWrite right leftLit array

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
  ()
#ifdef HERBRAND_CDCL_INSTRUMENTED
validateReasonPrecedence Nothing _ _ = ()
validateReasonPrecedence (Just (pivot, pivotStep)) literal introducedAt
  | introducedAt NonLinear.< pivotStep = ()
  | otherwise =
      NonLinear.error
        ( "reason literal does not precede its pivot: "
            <> NonLinear.show
              (pivot, pivotStep, literal, introducedAt)
        )
#else
{-# INLINE validateReasonPrecedence #-}
validateReasonPrecedence _ _ _ = ()
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
