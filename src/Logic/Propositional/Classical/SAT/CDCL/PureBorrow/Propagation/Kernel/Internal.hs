{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}

{- |
Low-level bulk primitive for the CDCL watch loop.

The caller has already split the independently owned stores and opened
rank-2 pins. This module is the sole unsafe boundary that temporarily exposes
those pins to one 'IO' loop. The pin tokens are returned unchanged, so no
backing buffer can escape its local borrow scope.
-}
module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Propagation.Kernel.Internal (
  KernelPins (..),
  KernelDelta (..),
  KernelOutcome (..),
  scanOccurrenceChain,
) where

import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.BO.Unsafe (unsafeSystemIOToBO)
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.Vector.Mutable qualified as MV
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal qualified as Grow
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import Logic.Propositional.Classical.SAT.CDCL.Types
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as NonLinear

data KernelPins headsPin tailsPin valuationPin literalsPin bodiesPin nextsPin where
  KernelPins ::
    Fixed.Pinned headsPin Int %1 ->
    Fixed.Pinned tailsPin Int %1 ->
    Fixed.Pinned valuationPin Variable %1 ->
    Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit)) %1 ->
    Grow.PinnedBuffer bodiesPin ClauseBody %1 ->
    Grow.PinnedBuffer nextsPin Int %1 ->
    KernelPins headsPin tailsPin valuationPin literalsPin bodiesPin nextsPin

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
  KernelPins headsPin tailsPin valuationPin literalsPin bodiesPin nextsPin %1 ->
  BO
    scope
    ( Ur KernelOutcome
    , KernelPins headsPin tailsPin valuationPin literalsPin bodiesPin nextsPin
    )
{-# NOINLINE scanOccurrenceChain #-}
scanOccurrenceChain =
  \numInitialClauses falseLiteral firstOccurrence ->
    Unsafe.toLinear
      \pins@(KernelPins (Fixed.Pinned heads) (Fixed.Pinned tails) (Fixed.Pinned valuation) (Boxed.PinnedBuffer literals) (Grow.PinnedBuffer bodies) (Grow.PinnedBuffer nexts)) ->
        unsafeSystemIOToBO do
          !outcome <-
            scan
              numInitialClauses
              falseLiteral
              firstOccurrence
              heads
              tails
              valuation
              literals
              bodies
              nexts
          NonLinear.pure (Ur outcome, pins)

scan ::
  Int ->
  Lit ->
  Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  UM.IOVector Variable ->
  MV.IOVector (Ur (U.Vector Lit)) ->
  UM.IOVector ClauseBody ->
  UM.IOVector Int ->
  NonLinear.IO KernelOutcome
{-# NOINLINE scan #-}
scan numInitialClauses falseLiteral =
  go 0 0 0
  where
    go !visited !moved !inspected !occurrence heads tails valuation literals bodies nexts
      | occurrence < 0 =
          NonLinear.pure
            (ChainDrained (KernelDelta visited moved inspected))
      | otherwise = do
          !nextOccurrence <- UM.unsafeRead nexts occurrence
          let !clauseId = watchOccurrenceClause occurrence
              !watchSlot = watchOccurrenceSlot occurrence
              !clauseIndex = unClauseId clauseId
          !body@ClauseBody {wat1, wat2} <-
            UM.unsafeRead bodies clauseIndex
          Ur clause <- MV.unsafeRead literals clauseIndex
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
              NonLinear.error
                ( "watch occurrence is in the wrong literal bucket: "
                    <> NonLinear.show
                      (clauseId, watchSlot, falseLiteral, watchedLiteral)
                )
            else do
              !other <-
                if otherIndex < 0
                  then NonLinear.pure Nothing
                  else do
                    let !otherLiteral = U.unsafeIndex clause otherIndex
                    !otherValue <- evalLiteralIO otherLiteral valuation
                    NonLinear.pure (Just (otherLiteral, otherValue))
              case other of
                Just (_, Just True) -> do
                  appendOccurrenceIO
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
                    heads
                    tails
                    valuation
                    literals
                    bodies
                    nexts
                _ -> do
                  (!replacement, !newInspections) <-
                    findReplacementIO
                      numInitialClauses
                      clauseId
                      watchSlot
                      clause
                      body
                      valuation
                  let !inspected' = inspected + newInspections
                  case replacement of
                    Just (replacementIndex, replacementLiteral) -> do
                      let !updatedBody =
                            case watchSlot of
                              W1 -> body {wat1 = replacementIndex}
                              W2 -> body {wat2 = replacementIndex}
                      UM.unsafeWrite bodies clauseIndex updatedBody
                      linkOccurrenceIO
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
                        heads
                        tails
                        valuation
                        literals
                        bodies
                        nexts
                    Nothing ->
                      case other of
                        Nothing -> do
                          appendOccurrenceIO
                            falseLiteral
                            occurrence
                            heads
                            tails
                            nexts
                          restoreOccurrenceChainIO
                            falseLiteral
                            nextOccurrence
                            heads
                            tails
                            nexts
                          NonLinear.pure
                            ( ConflictDetected
                                clauseId
                                watchedLiteral
                                (KernelDelta visited' moved inspected')
                            )
                        Just (otherLiteral, Nothing) -> do
                          appendOccurrenceIO
                            falseLiteral
                            occurrence
                            heads
                            tails
                            nexts
                          NonLinear.pure
                            ( UnitRequired
                                clauseId
                                otherLiteral
                                nextOccurrence
                                (KernelDelta visited' moved inspected')
                            )
                        Just (otherLiteral, Just False) -> do
                          !conflictLiteral <-
                            selectConflictLiteralIO
                              watchedLiteral
                              otherLiteral
                              valuation
                          appendOccurrenceIO
                            falseLiteral
                            occurrence
                            heads
                            tails
                            nexts
                          restoreOccurrenceChainIO
                            falseLiteral
                            nextOccurrence
                            heads
                            tails
                            nexts
                          NonLinear.pure
                            ( ConflictDetected
                                clauseId
                                conflictLiteral
                                (KernelDelta visited' moved inspected')
                            )

evalLiteralIO ::
  Lit ->
  UM.IOVector Variable ->
  NonLinear.IO (Maybe Bool)
{-# INLINE evalLiteralIO #-}
evalLiteralIO literal valuation = do
  !variable <-
    UM.unsafeRead valuation (fromVarId (litVar literal))
  NonLinear.pure
    case variable of
      Indefinite -> Nothing
      Definite {value} ->
        Just (isPositive literal == value)

findReplacementIO ::
  Int ->
  ClauseId ->
  WatchVar ->
  U.Vector Lit ->
  ClauseBody ->
  UM.IOVector Variable ->
  NonLinear.IO (Maybe (Index, Lit), Int)
{-# INLINE findReplacementIO #-}
findReplacementIO numInitialClauses clauseId watchSlot clause ClauseBody {wat1, wat2} valuation =
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

    search !offset undetermined !inspected
      | offset == clauseLength =
          NonLinear.pure (undetermined, inspected)
      | otherwise =
          let !rawIndex = cursor + offset
              !index =
                if rawIndex < clauseLength
                  then rawIndex
                  else rawIndex - clauseLength
           in if index == wat1 || index == wat2
                then search (offset + 1) undetermined inspected
                else do
                  let !candidate = U.unsafeIndex clause index
                  !candidateValue <- evalLiteralIO candidate valuation
                  let !inspected' = inspected + 1
                  case candidateValue of
                    Just False ->
                      search (offset + 1) undetermined inspected'
                    Just True ->
                      NonLinear.pure
                        (Just (index, candidate), inspected')
                    Nothing
                      | preferSatisfied ->
                          search
                            (offset + 1)
                            case undetermined of
                              Nothing -> Just (index, candidate)
                              Just {} -> undetermined
                            inspected'
                      | otherwise ->
                          NonLinear.pure
                            (Just (index, candidate), inspected')

selectConflictLiteralIO ::
  Lit ->
  Lit ->
  UM.IOVector Variable ->
  NonLinear.IO Lit
{-# INLINE selectConflictLiteralIO #-}
selectConflictLiteralIO first second valuation = do
  !firstVariable <-
    UM.unsafeRead valuation (fromVarId (litVar first))
  !secondVariable <-
    UM.unsafeRead valuation (fromVarId (litVar second))
  NonLinear.pure
    ( if introduced firstVariable NonLinear.> introduced secondVariable
        then first
        else second
    )

introduced :: Variable -> (DecideLevel, Step)
{-# INLINE introduced #-}
introduced Indefinite = (-1, -1)
introduced Definite {decideLevel, decisionStep} =
  (decideLevel, decisionStep)

appendOccurrenceIO ::
  Lit ->
  Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  NonLinear.IO ()
{-# INLINE appendOccurrenceIO #-}
appendOccurrenceIO literal occurrence heads tails nexts = do
  let !bucket = litBucketIndex literal
  !oldTail <- UM.unsafeRead tails bucket
  UM.unsafeWrite nexts occurrence (-1)
  if oldTail < 0
    then do
      UM.unsafeWrite heads bucket occurrence
      UM.unsafeWrite tails bucket occurrence
    else do
      UM.unsafeWrite nexts oldTail occurrence
      UM.unsafeWrite tails bucket occurrence

linkOccurrenceIO ::
  Lit ->
  Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  NonLinear.IO ()
{-# INLINE linkOccurrenceIO #-}
linkOccurrenceIO literal occurrence heads tails nexts = do
  let !bucket = litBucketIndex literal
  !oldHead <- UM.unsafeRead heads bucket
  !oldTail <- UM.unsafeRead tails bucket
  if oldTail < 0
    then do
      UM.unsafeWrite heads bucket occurrence
      UM.unsafeWrite tails bucket occurrence
      UM.unsafeWrite nexts occurrence (-1)
    else
      if occurrence < oldHead
        then do
          UM.unsafeWrite heads bucket occurrence
          UM.unsafeWrite nexts occurrence oldHead
        else do
          UM.unsafeWrite tails bucket occurrence
          UM.unsafeWrite nexts occurrence (-1)
          UM.unsafeWrite nexts oldTail occurrence

restoreOccurrenceChainIO ::
  Lit ->
  Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  NonLinear.IO ()
{-# INLINE restoreOccurrenceChainIO #-}
restoreOccurrenceChainIO literal =
  go
  where
    go !occurrence heads tails nexts
      | occurrence < 0 = NonLinear.pure ()
      | otherwise = do
          !nextOccurrence <- UM.unsafeRead nexts occurrence
          appendOccurrenceIO literal occurrence heads tails nexts
          go nextOccurrence heads tails nexts
