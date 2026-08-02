{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}

{- |
The public-operation bulk kernel for the CDCL watch loop.

Every fixed alias is split by the caller from one locally reborrowed
`CDCLStore`. The recurrence threads and returns each alias linearly.
-}
module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Propagation.Kernel.Internal (
  KernelPins (..),
  KernelDelta (..),
  KernelOutcome (..),
  scanOccurrenceChain,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal qualified as Grow
import Data.Vector.Unboxed qualified as U
import Logic.Propositional.Classical.SAT.CDCL.Types
import Prelude.Linear
import Prelude qualified as NonLinear

data KernelPins α where
  KernelPins ::
    Fixed.Pinned α Int %1 ->
    Fixed.Pinned α Int %1 ->
    Fixed.Pinned α Variable %1 ->
    Boxed.PinnedBuffer α (Ur (U.Vector Lit)) %1 ->
    Grow.PinnedBuffer α ClauseBody %1 ->
    Grow.PinnedBuffer α Int %1 ->
    KernelPins α

data KernelDelta = KernelDelta
  { visitedOccurrences :: {-# UNPACK #-} !Int
  , movedWatches :: {-# UNPACK #-} !Int
  , inspectedLiterals :: {-# UNPACK #-} !Int
  }
  deriving (NonLinear.Show, NonLinear.Eq)

data KernelOutcome
  = ChainDrained !KernelDelta
  | UnitRequired
      !ClauseId
      !Lit
      {-# UNPACK #-} !Int
      !KernelDelta
  | ConflictDetected !ClauseId !Lit !KernelDelta
  deriving (NonLinear.Show, NonLinear.Eq)

scanOccurrenceChain ::
  Int ->
  Lit ->
  Int ->
  KernelPins α %1 ->
  BO
    α
    ( Ur KernelOutcome
    , KernelPins α
    )
{-# NOINLINE scanOccurrenceChain #-}
scanOccurrenceChain numInitialClauses falseLiteral =
  go 0 0 0
  where
    go !visited !moved !inspected !occurrence pins
      | occurrence < 0 =
          Control.pure
            ( Ur (ChainDrained (KernelDelta visited moved inspected))
            , pins
            )
      | otherwise =
          case pins of
            KernelPins heads tails valuation literals bodies nexts -> Control.do
              (Ur nextOccurrence, nexts) <-
                Grow.pinnedBufferUnsafeCopyAt occurrence nexts
              let !clauseId = watchOccurrenceClause occurrence
                  !watchSlot = watchOccurrenceSlot occurrence
                  !clauseIndex = unClauseId clauseId
              (Ur body@ClauseBody {wat1, wat2}, bodies) <-
                Grow.pinnedBufferUnsafeCopyAt clauseIndex bodies
              (Ur (Ur clause), literals) <-
                Boxed.pinnedBufferUnsafeCopyAt clauseIndex literals
              let !watchedIndex =
                    case watchSlot of
                      W1 -> wat1
                      W2 -> wat2
                  !otherIndex =
                    case watchSlot of
                      W1 -> wat2
                      W2 -> wat1
                  !watchedLiteral =
                    U.unsafeIndex clause watchedIndex
                  !visited' = visited + 1
              if watchedLiteral NonLinear./= falseLiteral
                then
                  error
                    ( "watch occurrence is in the wrong literal bucket: "
                        <> NonLinear.show
                          (clauseId, watchSlot, falseLiteral, watchedLiteral)
                    )
                    heads
                    tails
                    valuation
                    literals
                    bodies
                    nexts
                else Control.do
                  (Ur other, valuation) <-
                    if otherIndex < 0
                      then Control.pure (Ur Nothing, valuation)
                      else Control.do
                        let !otherLiteral = U.unsafeIndex clause otherIndex
                        (Ur otherValue, valuation) <-
                          evalLiteral otherLiteral valuation
                        Control.pure
                          (Ur (Just (otherLiteral, otherValue)), valuation)
                  case other of
                    Just (_, Just True) -> Control.do
                      (heads, tails, nexts) <-
                        appendOccurrence
                          falseLiteral
                          occurrence
                          heads
                          tails
                          nexts
                      go
                        visited'
                        moved
                        inspected
                        nextOccurrence
                        (KernelPins heads tails valuation literals bodies nexts)
                    _ -> Control.do
                      (Ur (replacement, newInspections), valuation) <-
                        findReplacement
                          numInitialClauses
                          clauseId
                          watchSlot
                          clause
                          body
                          valuation
                      let !inspected' = inspected + newInspections
                      case replacement of
                        Just (replacementIndex, replacementLiteral) -> Control.do
                          let !updatedBody =
                                case watchSlot of
                                  W1 -> body {wat1 = replacementIndex}
                                  W2 -> body {wat2 = replacementIndex}
                          bodies <-
                            Grow.pinnedBufferUnsafeWrite
                              clauseIndex
                              updatedBody
                              bodies
                          (heads, tails, nexts) <-
                            linkOccurrence
                              replacementLiteral
                              occurrence
                              heads
                              tails
                              nexts
                          go
                            visited'
                            (moved + 1)
                            inspected'
                            nextOccurrence
                            ( KernelPins
                                heads
                                tails
                                valuation
                                literals
                                bodies
                                nexts
                            )
                        Nothing ->
                          case other of
                            Nothing -> Control.do
                              (heads, tails, nexts) <-
                                appendOccurrence
                                  falseLiteral
                                  occurrence
                                  heads
                                  tails
                                  nexts
                              (heads, tails, nexts) <-
                                restoreOccurrenceChain
                                  falseLiteral
                                  nextOccurrence
                                  heads
                                  tails
                                  nexts
                              Control.pure
                                ( Ur
                                    ( ConflictDetected
                                        clauseId
                                        watchedLiteral
                                        ( KernelDelta
                                            visited'
                                            moved
                                            inspected'
                                        )
                                    )
                                , KernelPins
                                    heads
                                    tails
                                    valuation
                                    literals
                                    bodies
                                    nexts
                                )
                            Just (otherLiteral, Nothing) -> Control.do
                              (heads, tails, nexts) <-
                                appendOccurrence
                                  falseLiteral
                                  occurrence
                                  heads
                                  tails
                                  nexts
                              Control.pure
                                ( Ur
                                    ( UnitRequired
                                        clauseId
                                        otherLiteral
                                        nextOccurrence
                                        ( KernelDelta
                                            visited'
                                            moved
                                            inspected'
                                        )
                                    )
                                , KernelPins
                                    heads
                                    tails
                                    valuation
                                    literals
                                    bodies
                                    nexts
                                )
                            Just (otherLiteral, Just False) -> Control.do
                              (Ur conflictLiteral, valuation) <-
                                selectConflictLiteral
                                  watchedLiteral
                                  otherLiteral
                                  valuation
                              (heads, tails, nexts) <-
                                appendOccurrence
                                  falseLiteral
                                  occurrence
                                  heads
                                  tails
                                  nexts
                              (heads, tails, nexts) <-
                                restoreOccurrenceChain
                                  falseLiteral
                                  nextOccurrence
                                  heads
                                  tails
                                  nexts
                              Control.pure
                                ( Ur
                                    ( ConflictDetected
                                        clauseId
                                        conflictLiteral
                                        ( KernelDelta
                                            visited'
                                            moved
                                            inspected'
                                        )
                                    )
                                , KernelPins
                                    heads
                                    tails
                                    valuation
                                    literals
                                    bodies
                                    nexts
                                )

evalLiteral ::
  Lit ->
  Fixed.Pinned α Variable %1 ->
  BO α (Ur (Maybe Bool), Fixed.Pinned α Variable)
{-# INLINE evalLiteral #-}
evalLiteral literal valuation = Control.do
  (Ur variable, valuation) <-
    Fixed.pinnedUnsafeCopyAt (fromVarId (litVar literal)) valuation
  Control.pure
    ( Ur
        case variable of
          Indefinite -> Nothing
          Definite {value} ->
            Just (isPositive literal == value)
    , valuation
    )

findReplacement ::
  Int ->
  ClauseId ->
  WatchVar ->
  U.Vector Lit ->
  ClauseBody ->
  Fixed.Pinned α Variable %1 ->
  BO
    α
    ( Ur (Maybe (Index, Lit), Int)
    , Fixed.Pinned α Variable
    )
{-# INLINE findReplacement #-}
findReplacement numInitialClauses clauseId watchSlot clause ClauseBody {wat1, wat2} =
  search 0 Nothing 0
  where
    !watchedIndex =
      case watchSlot of
        W1 -> wat1
        W2 -> wat2
    !clauseLength = U.length clause
    !isLearnt = unClauseId clauseId >= numInitialClauses
    !cursor
      | isLearnt || clauseLength <= 8 = 0
      | watchedIndex + 1 == clauseLength = 0
      | otherwise = watchedIndex + 1
    !preferSatisfied = clauseLength <= 8 || isLearnt

    search !offset undetermined !inspected valuation
      | offset == clauseLength =
          Control.pure (Ur (undetermined, inspected), valuation)
      | otherwise =
          let !rawIndex = cursor + offset
              !index =
                if rawIndex < clauseLength
                  then rawIndex
                  else rawIndex - clauseLength
           in if index == wat1 || index == wat2
                then search (offset + 1) undetermined inspected valuation
                else Control.do
                  let !candidate = U.unsafeIndex clause index
                  (Ur candidateValue, valuation) <-
                    evalLiteral candidate valuation
                  let !inspected' = inspected + 1
                  case candidateValue of
                    Just False ->
                      search
                        (offset + 1)
                        undetermined
                        inspected'
                        valuation
                    Just True ->
                      Control.pure
                        (Ur (Just (index, candidate), inspected'), valuation)
                    Nothing
                      | preferSatisfied ->
                          search
                            (offset + 1)
                            case undetermined of
                              Nothing -> Just (index, candidate)
                              Just {} -> undetermined
                            inspected'
                            valuation
                      | otherwise ->
                          Control.pure
                            (Ur (Just (index, candidate), inspected'), valuation)

selectConflictLiteral ::
  Lit ->
  Lit ->
  Fixed.Pinned α Variable %1 ->
  BO α (Ur Lit, Fixed.Pinned α Variable)
{-# INLINE selectConflictLiteral #-}
selectConflictLiteral first second valuation = Control.do
  (Ur firstVariable, valuation) <-
    Fixed.pinnedUnsafeCopyAt
      (fromVarId (litVar first))
      valuation
  (Ur secondVariable, valuation) <-
    Fixed.pinnedUnsafeCopyAt
      (fromVarId (litVar second))
      valuation
  Control.pure
    ( Ur
        ( if introduced firstVariable NonLinear.> introduced secondVariable
            then first
            else second
        )
    , valuation
    )

introduced :: Variable -> (DecideLevel, Step)
{-# INLINE introduced #-}
introduced Indefinite = (-1, -1)
introduced Definite {decideLevel, decisionStep} =
  (decideLevel, decisionStep)

appendOccurrence ::
  Lit ->
  Int ->
  Fixed.Pinned α Int %1 ->
  Fixed.Pinned α Int %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Fixed.Pinned α Int
    , Fixed.Pinned α Int
    , Grow.PinnedBuffer α Int
    )
{-# INLINE appendOccurrence #-}
appendOccurrence literal occurrence heads tails nexts = Control.do
  let !bucket = litBucketIndex literal
  (Ur oldTail, tails) <- Fixed.pinnedUnsafeCopyAt bucket tails
  nexts <- Grow.pinnedBufferUnsafeWrite occurrence (-1) nexts
  if oldTail < 0
    then Control.do
      heads <- Fixed.pinnedUnsafeWrite bucket occurrence heads
      tails <- Fixed.pinnedUnsafeWrite bucket occurrence tails
      Control.pure (heads, tails, nexts)
    else Control.do
      nexts <- Grow.pinnedBufferUnsafeWrite oldTail occurrence nexts
      tails <- Fixed.pinnedUnsafeWrite bucket occurrence tails
      Control.pure (heads, tails, nexts)

linkOccurrence ::
  Lit ->
  Int ->
  Fixed.Pinned α Int %1 ->
  Fixed.Pinned α Int %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Fixed.Pinned α Int
    , Fixed.Pinned α Int
    , Grow.PinnedBuffer α Int
    )
{-# INLINE linkOccurrence #-}
linkOccurrence literal occurrence heads tails nexts = Control.do
  let !bucket = litBucketIndex literal
  (Ur oldHead, heads) <- Fixed.pinnedUnsafeCopyAt bucket heads
  (Ur oldTail, tails) <- Fixed.pinnedUnsafeCopyAt bucket tails
  if oldTail < 0
    then Control.do
      heads <- Fixed.pinnedUnsafeWrite bucket occurrence heads
      tails <- Fixed.pinnedUnsafeWrite bucket occurrence tails
      nexts <- Grow.pinnedBufferUnsafeWrite occurrence (-1) nexts
      Control.pure (heads, tails, nexts)
    else
      if occurrence < oldHead
        then Control.do
          heads <- Fixed.pinnedUnsafeWrite bucket occurrence heads
          nexts <- Grow.pinnedBufferUnsafeWrite occurrence oldHead nexts
          Control.pure (heads, tails, nexts)
        else Control.do
          tails <- Fixed.pinnedUnsafeWrite bucket occurrence tails
          nexts <- Grow.pinnedBufferUnsafeWrite occurrence (-1) nexts
          nexts <- Grow.pinnedBufferUnsafeWrite oldTail occurrence nexts
          Control.pure (heads, tails, nexts)

restoreOccurrenceChain ::
  Lit ->
  Int ->
  Fixed.Pinned α Int %1 ->
  Fixed.Pinned α Int %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Fixed.Pinned α Int
    , Fixed.Pinned α Int
    , Grow.PinnedBuffer α Int
    )
{-# INLINE restoreOccurrenceChain #-}
restoreOccurrenceChain literal =
  go
  where
    go !occurrence heads tails nexts
      | occurrence < 0 =
          Control.pure (heads, tails, nexts)
      | otherwise = Control.do
          (Ur nextOccurrence, nexts) <-
            Grow.pinnedBufferUnsafeCopyAt occurrence nexts
          (heads, tails, nexts) <-
            appendOccurrence literal occurrence heads tails nexts
          go nextOccurrence heads tails nexts
