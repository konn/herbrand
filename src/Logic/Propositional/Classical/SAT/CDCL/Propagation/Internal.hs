{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{- |
The Phase 1 architecture spike for a complete propagation transaction.

The algorithm has no access to owner constructors and imports no unsafe Pure
Borrow module. It reborrows the aggregate, performs the mandatory five-field
split, splits the nested clause/watch records, opens all three growable roots
and the VSIDS root once, and passes only active stores to the inner loop.
-}
module Logic.Propositional.Classical.SAT.CDCL.Propagation.Internal (
  PropagationControl (..),
  PropagationEvidence (..),
  PropagationStart (..),
  PropagationExit (..),
  ConflictExit (..),
  KernelEvidence (..),
  propagateArchitectureSpike,
  propagateWatchSpike,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.Bits (xor)
import Data.Record.Linear.Borrow.Experimental.PatternMatch ((.@))
import Data.Ref.Linear.Borrow qualified as RefBorrow
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal qualified as Grow
import Data.Vector.Unboxed qualified as U
import Logic.Propositional.Classical.SAT.CDCL.Store.Internal qualified as Store
import Prelude.Linear
import Prelude qualified as NonLinear

-- | Scalar state is threaded linearly and owns no mutable store.
data PropagationControl where
  PropagationControl ::
    {-# UNPACK #-} !Int %1 ->
    {-# UNPACK #-} !Int %1 ->
    PropagationControl
  deriving (NonLinear.Show, NonLinear.Eq)

instance Consumable PropagationControl where
  consume (PropagationControl cursor limit) =
    consume cursor `lseq` consume limit

instance Dupable PropagationControl where
  dup2 (PropagationControl cursor limit) =
    dup2 cursor & \(firstCursor, secondCursor) ->
      dup2 limit & \(firstLimit, secondLimit) ->
        ( PropagationControl firstCursor firstLimit
        , PropagationControl secondCursor secondLimit
        )

instance Movable PropagationControl where
  move (PropagationControl cursor limit) =
    case move cursor of
      Ur unrestrictedCursor ->
        case move limit of
          Ur unrestrictedLimit ->
            Ur
              ( PropagationControl
                  unrestrictedCursor
                  unrestrictedLimit
              )

-- | Runtime evidence collected without retaining a borrow.
data PropagationEvidence = PropagationEvidence
  { visitedOccurrences :: {-# UNPACK #-} !Int
  , observationChecksum :: {-# UNPACK #-} !Int
  }
  deriving (NonLinear.Show, NonLinear.Eq)

-- | Entry mode for the bounded watch-kernel spike.
data PropagationStart
  = ResumePropagation
  | SeedRootUnit {-# UNPACK #-} !Int {-# UNPACK #-} !Int
  deriving (NonLinear.Show, NonLinear.Eq)

-- | The two distinct conflict exits covered by the spike.
data ConflictExit
  = ClauseConflict
  | AssertionConflict
  deriving (NonLinear.Show, NonLinear.Eq)

data PropagationExit
  = PropagationComplete
  | PropagationConflict
      !ConflictExit
      {-# UNPACK #-} !Int
      {-# UNPACK #-} !Int
  deriving (NonLinear.Show, NonLinear.Eq)

data KernelEvidence = KernelEvidence
  { kernelExit :: !PropagationExit
  , kernelVisited :: {-# UNPACK #-} !Int
  , kernelMoves :: {-# UNPACK #-} !Int
  , kernelEnqueues :: {-# UNPACK #-} !Int
  }
  deriving (NonLinear.Show, NonLinear.Eq)

-- | Exercise the complete topology under one aggregate reborrow.
propagateArchitectureSpike ::
  PropagationControl %1 ->
  Mut lifetime (Store.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur PropagationEvidence
    , PropagationControl
    , Mut lifetime (Store.CDCLStore s)
    )
{-# INLINE propagateArchitectureSpike #-}
propagateArchitectureSpike =
  withPropagationTransaction (propagationLoop 0 0)

{- | Run a small but real watched-literal chain under the same transaction.

Integer literals use MiniSat-style buckets: @2*v@ is positive and
@2*v+1@ is negative. Valuation cells are @-1/0/1@ for false/unassigned/true.
-}
propagateWatchSpike ::
  PropagationStart ->
  PropagationControl %1 ->
  Mut lifetime (Store.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur KernelEvidence
    , PropagationControl
    , Mut lifetime (Store.CDCLStore s)
    )
{-# INLINE propagateWatchSpike #-}
propagateWatchSpike start =
  withPropagationTransaction (watchKernel start)

withPropagationTransaction ::
  ( forall local.
    control %1 ->
    Store.VSIDSState s %1 ->
    Mut local (Fixed.UArray Int) %1 ->
    Mut local (Fixed.UArray Int) %1 ->
    Mut local (Fixed.UArray Int) %1 ->
    Mut local (Fixed.UArray Int) %1 ->
    Boxed.PinnedBuffer local (Ur (U.Vector Int)) %1 ->
    Grow.PinnedBuffer local Int %1 ->
    Grow.PinnedBuffer local Int %1 ->
    BO
      local
      ( result
      , control
      , Store.VSIDSState s
      , Mut local (Fixed.UArray Int)
      , Mut local (Fixed.UArray Int)
      , Mut local (Fixed.UArray Int)
      , Mut local (Fixed.UArray Int)
      , Boxed.PinnedBuffer local (Ur (U.Vector Int))
      , Grow.PinnedBuffer local Int
      , Grow.PinnedBuffer local Int
      )
  ) %1 ->
  control %1 ->
  Mut α (Store.CDCLStore s) %1 ->
  BO
    α
    ( result
    , control
    , Mut α (Store.CDCLStore s)
    )
{-# INLINE withPropagationTransaction #-}
withPropagationTransaction worker control store = Control.do
  ((result, finalControl), store) <-
    reborrowing store \local -> Control.do
      let %1 !(watches, clauses, valuation, trail, vsids) =
            local
              .@ ( Store.watchesField
                 , Store.clausesField
                 , Store.valuationField
                 , Store.trailField
                 , Store.vsidsField
                 )
      let %1 !(watchHeads, watchTails, watchNexts) =
            watches
              .@ ( Store.watchHeadsField
                 , Store.watchTailsField
                 , Store.watchNextsField
                 )
      let %1 !(clauseLiterals, clauseBodies) =
            clauses
              .@ ( Store.clauseLiteralsField
                 , Store.clauseBodiesField
                 )
      Boxed.getContents clauseLiterals & \literalContents ->
        Grow.getContents clauseBodies & \bodyContents ->
          Grow.getContents watchNexts & \nextContents -> Control.do
            ( ( result
                , finalControl
                , watchHeads
                , watchTails
                , valuation
                , trail
                , Boxed.PinnedBuffer literalContents
                , Grow.PinnedBuffer bodyContents
                , Grow.PinnedBuffer nextContents
                )
              , vsids
              ) <-
              RefBorrow.update
                ( \vsidsState -> Control.do
                    ( result
                      , finalControl
                      , vsidsState
                      , watchHeads
                      , watchTails
                      , valuation
                      , trail
                      , literals
                      , bodies
                      , nexts
                      ) <-
                      worker
                        control
                        vsidsState
                        watchHeads
                        watchTails
                        valuation
                        trail
                        (Boxed.PinnedBuffer literalContents)
                        (Grow.PinnedBuffer bodyContents)
                        (Grow.PinnedBuffer nextContents)
                    Control.pure
                      (
                        ( result
                        , finalControl
                        , watchHeads
                        , watchTails
                        , valuation
                        , trail
                        , literals
                        , bodies
                        , nexts
                        )
                      , vsidsState
                      )
                )
                vsids
            let !(Ur _) = share watchHeads
            let !(Ur _) = share watchTails
            let !(Ur _) = share valuation
            let !(Ur _) = share trail
            let !(Ur _) = share literalContents
            let !(Ur _) = share bodyContents
            let !(Ur _) = share nextContents
            let !(Ur _) = share vsids
            Control.pure (result, finalControl)
  Control.pure (result, finalControl, store)

data SpikeAssertion
  = NewlyAsserted
  | AlreadyAsserted
  | ContradictingAssertion

watchKernel ::
  PropagationStart ->
  PropagationControl %1 ->
  Store.VSIDSState s %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Boxed.PinnedBuffer α (Ur (U.Vector Int)) %1 ->
  Grow.PinnedBuffer α Int %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Ur KernelEvidence
    , PropagationControl
    , Store.VSIDSState s
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Boxed.PinnedBuffer α (Ur (U.Vector Int))
    , Grow.PinnedBuffer α Int
    , Grow.PinnedBuffer α Int
    )
{-# INLINE watchKernel #-}
watchKernel start control vsids watchHeads watchTails valuation trail literals bodies nexts =
  case start of
    ResumePropagation ->
      drainTrail
        0
        0
        0
        control
        vsids
        watchHeads
        watchTails
        valuation
        trail
        literals
        bodies
        nexts
    SeedRootUnit clauseId literal -> Control.do
      (Ur assertion, control, vsids, valuation, trail) <-
        enqueueLiteral literal control vsids valuation trail
      case assertion of
        ContradictingAssertion ->
          Control.pure
            ( Ur
                KernelEvidence
                  { kernelExit =
                      PropagationConflict
                        AssertionConflict
                        clauseId
                        literal
                  , kernelVisited = 0
                  , kernelMoves = 0
                  , kernelEnqueues = 0
                  }
            , control
            , vsids
            , watchHeads
            , watchTails
            , valuation
            , trail
            , literals
            , bodies
            , nexts
            )
        AlreadyAsserted ->
          drainTrail
            0
            0
            0
            control
            vsids
            watchHeads
            watchTails
            valuation
            trail
            literals
            bodies
            nexts
        NewlyAsserted ->
          drainTrail
            0
            0
            1
            control
            vsids
            watchHeads
            watchTails
            valuation
            trail
            literals
            bodies
            nexts

drainTrail ::
  Int ->
  Int ->
  Int ->
  PropagationControl %1 ->
  Store.VSIDSState s %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Boxed.PinnedBuffer α (Ur (U.Vector Int)) %1 ->
  Grow.PinnedBuffer α Int %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Ur KernelEvidence
    , PropagationControl
    , Store.VSIDSState s
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Boxed.PinnedBuffer α (Ur (U.Vector Int))
    , Grow.PinnedBuffer α Int
    , Grow.PinnedBuffer α Int
    )
{-# INLINE drainTrail #-}
drainTrail !visited !moves !enqueues control vsids watchHeads watchTails valuation trail literals bodies nexts =
  case move control of
    Ur (PropagationControl qhead trailLength)
      | qhead >= trailLength ->
          Control.pure
            ( Ur
                KernelEvidence
                  { kernelExit = PropagationComplete
                  , kernelVisited = visited
                  , kernelMoves = moves
                  , kernelEnqueues = enqueues
                  }
            , PropagationControl qhead trailLength
            , vsids
            , watchHeads
            , watchTails
            , valuation
            , trail
            , literals
            , bodies
            , nexts
            )
      | otherwise -> Control.do
          (Ur assertedLiteral, trail) <-
            Fixed.unsafeCopyAtMut qhead trail
          let !falseLiteral = assertedLiteral `xor` 1
          (Ur firstOccurrence, watchHeads) <-
            Fixed.unsafeCopyAtMut falseLiteral watchHeads
          watchHeads <-
            Fixed.unsafeWrite falseLiteral (-1) watchHeads
          watchTails <-
            Fixed.unsafeWrite falseLiteral (-1) watchTails
          ( Ur (conflict, visited, moves, enqueues)
            , control
            , vsids
            , watchHeads
            , watchTails
            , valuation
            , trail
            , literals
            , bodies
            , nexts
            ) <-
            processOccurrences
              falseLiteral
              firstOccurrence
              visited
              moves
              enqueues
              (PropagationControl (qhead + 1) trailLength)
              vsids
              watchHeads
              watchTails
              valuation
              trail
              literals
              bodies
              nexts
          case conflict of
            Just (kind, clauseId, conflictLiteral) ->
              Control.pure
                ( Ur
                    KernelEvidence
                      { kernelExit =
                          PropagationConflict
                            kind
                            clauseId
                            conflictLiteral
                      , kernelVisited = visited
                      , kernelMoves = moves
                      , kernelEnqueues = enqueues
                      }
                , control
                , vsids
                , watchHeads
                , watchTails
                , valuation
                , trail
                , literals
                , bodies
                , nexts
                )
            Nothing ->
              drainTrail
                visited
                moves
                enqueues
                control
                vsids
                watchHeads
                watchTails
                valuation
                trail
                literals
                bodies
                nexts

processOccurrences ::
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  PropagationControl %1 ->
  Store.VSIDSState s %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Boxed.PinnedBuffer α (Ur (U.Vector Int)) %1 ->
  Grow.PinnedBuffer α Int %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Ur (Maybe (ConflictExit, Int, Int), Int, Int, Int)
    , PropagationControl
    , Store.VSIDSState s
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Boxed.PinnedBuffer α (Ur (U.Vector Int))
    , Grow.PinnedBuffer α Int
    , Grow.PinnedBuffer α Int
    )
{-# INLINE processOccurrences #-}
processOccurrences !falseLiteral !occurrence !visited !moves !enqueues control vsids watchHeads watchTails valuation trail literals bodies nexts
  | occurrence < 0 =
      Control.pure
        ( Ur (Nothing, visited, moves, enqueues)
        , control
        , vsids
        , watchHeads
        , watchTails
        , valuation
        , trail
        , literals
        , bodies
        , nexts
        )
  | otherwise = Control.do
      (Ur nextOccurrence, nexts) <-
        Grow.pinnedBufferUnsafeCopyAt occurrence nexts
      let !clauseId = occurrence `div` 2
          !watchSlot = occurrence `mod` 2
      (Ur encodedBody, bodies) <-
        Grow.pinnedBufferUnsafeCopyAt clauseId bodies
      (Ur (Ur clause), literals) <-
        Boxed.pinnedBufferUnsafeCopyAt clauseId literals
      let (!watched1, !watched2) = decodeBody encodedBody
          !watchedIndex =
            if watchSlot == 0 then watched1 else watched2
          !otherIndex =
            if watchSlot == 0 then watched2 else watched1
          !watchedLiteral = U.unsafeIndex clause watchedIndex
      if watchedLiteral /= falseLiteral
        then
          error
            ( "watch occurrence in wrong bucket: "
                <> show (occurrence, falseLiteral, watchedLiteral)
            )
            control
            vsids
            watchHeads
            watchTails
            valuation
            trail
            literals
            bodies
            nexts
        else Control.do
          (Ur otherValue, valuation) <-
            if otherIndex < 0
              then Control.pure (Ur (-1), valuation)
              else
                evalLiteral
                  (U.unsafeIndex clause otherIndex)
                  valuation
          if otherIndex >= 0 && otherValue > 0
            then Control.do
              (watchHeads, watchTails, nexts) <-
                appendOccurrence
                  falseLiteral
                  occurrence
                  watchHeads
                  watchTails
                  nexts
              processOccurrences
                falseLiteral
                nextOccurrence
                (visited + 1)
                moves
                enqueues
                control
                (Store.bumpVSIDS vsids)
                watchHeads
                watchTails
                valuation
                trail
                literals
                bodies
                nexts
            else Control.do
              (Ur replacement, valuation) <-
                findReplacement
                  clause
                  watched1
                  watched2
                  0
                  valuation
              case replacement of
                Just (replacementIndex, replacementLiteral) -> Control.do
                  let !updatedBody =
                        if watchSlot == 0
                          then encodeBody replacementIndex watched2
                          else encodeBody watched1 replacementIndex
                  bodies <-
                    Grow.pinnedBufferUnsafeWrite
                      clauseId
                      updatedBody
                      bodies
                  (watchHeads, watchTails, nexts) <-
                    appendOccurrence
                      replacementLiteral
                      occurrence
                      watchHeads
                      watchTails
                      nexts
                  processOccurrences
                    falseLiteral
                    nextOccurrence
                    (visited + 1)
                    (moves + 1)
                    enqueues
                    control
                    (Store.bumpVSIDS vsids)
                    watchHeads
                    watchTails
                    valuation
                    trail
                    literals
                    bodies
                    nexts
                Nothing
                  | otherIndex < 0 || otherValue < 0 -> Control.do
                      (watchHeads, watchTails, nexts) <-
                        appendOccurrence
                          falseLiteral
                          occurrence
                          watchHeads
                          watchTails
                          nexts
                      (watchHeads, watchTails, nexts) <-
                        restoreOccurrenceChain
                          falseLiteral
                          nextOccurrence
                          watchHeads
                          watchTails
                          nexts
                      let !conflictLiteral =
                            if otherIndex < 0
                              then watchedLiteral
                              else U.unsafeIndex clause otherIndex
                      Control.pure
                        ( Ur
                            ( Just
                                ( ClauseConflict
                                , clauseId
                                , conflictLiteral
                                )
                            , visited + 1
                            , moves
                            , enqueues
                            )
                        , control
                        , Store.bumpVSIDS vsids
                        , watchHeads
                        , watchTails
                        , valuation
                        , trail
                        , literals
                        , bodies
                        , nexts
                        )
                  | otherwise -> Control.do
                      (watchHeads, watchTails, nexts) <-
                        appendOccurrence
                          falseLiteral
                          occurrence
                          watchHeads
                          watchTails
                          nexts
                      let !unitLiteral = U.unsafeIndex clause otherIndex
                      (Ur assertion, control, vsids, valuation, trail) <-
                        enqueueLiteral
                          unitLiteral
                          control
                          (Store.bumpVSIDS vsids)
                          valuation
                          trail
                      case assertion of
                        ContradictingAssertion -> Control.do
                          (watchHeads, watchTails, nexts) <-
                            restoreOccurrenceChain
                              falseLiteral
                              nextOccurrence
                              watchHeads
                              watchTails
                              nexts
                          Control.pure
                            ( Ur
                                ( Just
                                    ( AssertionConflict
                                    , clauseId
                                    , unitLiteral
                                    )
                                , visited + 1
                                , moves
                                , enqueues
                                )
                            , control
                            , vsids
                            , watchHeads
                            , watchTails
                            , valuation
                            , trail
                            , literals
                            , bodies
                            , nexts
                            )
                        AlreadyAsserted ->
                          processOccurrences
                            falseLiteral
                            nextOccurrence
                            (visited + 1)
                            moves
                            enqueues
                            control
                            vsids
                            watchHeads
                            watchTails
                            valuation
                            trail
                            literals
                            bodies
                            nexts
                        NewlyAsserted ->
                          processOccurrences
                            falseLiteral
                            nextOccurrence
                            (visited + 1)
                            moves
                            (enqueues + 1)
                            control
                            vsids
                            watchHeads
                            watchTails
                            valuation
                            trail
                            literals
                            bodies
                            nexts

evalLiteral ::
  Int ->
  Mut α (Fixed.UArray Int) %1 ->
  BO α (Ur Int, Mut α (Fixed.UArray Int))
{-# INLINE evalLiteral #-}
evalLiteral literal valuation = Control.do
  (Ur variableValue, valuation) <-
    Fixed.unsafeCopyAtMut (literal `div` 2) valuation
  let !literalValue =
        if literal `mod` 2 == 0
          then variableValue
          else negate variableValue
  Control.pure (Ur literalValue, valuation)

findReplacement ::
  U.Vector Int ->
  Int ->
  Int ->
  Int ->
  Mut α (Fixed.UArray Int) %1 ->
  BO
    α
    (Ur (Maybe (Int, Int)), Mut α (Fixed.UArray Int))
{-# INLINE findReplacement #-}
findReplacement clause watched1 watched2 !index valuation
  | index >= U.length clause =
      Control.pure (Ur Nothing, valuation)
  | index == watched1 || index == watched2 =
      findReplacement
        clause
        watched1
        watched2
        (index + 1)
        valuation
  | otherwise = Control.do
      let !candidate = U.unsafeIndex clause index
      (Ur candidateValue, valuation) <-
        evalLiteral candidate valuation
      if candidateValue >= 0
        then Control.pure (Ur (Just (index, candidate)), valuation)
        else
          findReplacement
            clause
            watched1
            watched2
            (index + 1)
            valuation

enqueueLiteral ::
  Int ->
  PropagationControl %1 ->
  Store.VSIDSState s %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  BO
    α
    ( Ur SpikeAssertion
    , PropagationControl
    , Store.VSIDSState s
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    )
{-# INLINE enqueueLiteral #-}
enqueueLiteral literal control vsids valuation trail =
  case move control of
    Ur (PropagationControl qhead trailLength) -> Control.do
      let !variableIndex = literal `div` 2
          !assertedValue =
            if literal `mod` 2 == 0 then 1 else -1
      (Ur oldValue, valuation) <-
        Fixed.unsafeCopyAtMut variableIndex valuation
      if oldValue == 0
        then Control.do
          valuation <-
            Fixed.unsafeWrite
              variableIndex
              assertedValue
              valuation
          trail <-
            Fixed.unsafeWrite trailLength literal trail
          Control.pure
            ( Ur NewlyAsserted
            , PropagationControl qhead (trailLength + 1)
            , vsids
            , valuation
            , trail
            )
        else
          Control.pure
            ( Ur
                ( if oldValue == assertedValue
                    then AlreadyAsserted
                    else ContradictingAssertion
                )
            , PropagationControl qhead trailLength
            , vsids
            , valuation
            , trail
            )

appendOccurrence ::
  Int ->
  Int ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Grow.PinnedBuffer α Int
    )
{-# INLINE appendOccurrence #-}
appendOccurrence literal occurrence watchHeads watchTails nexts = Control.do
  (Ur oldTail, watchTails) <-
    Fixed.unsafeCopyAtMut literal watchTails
  nexts <-
    Grow.pinnedBufferUnsafeWrite occurrence (-1) nexts
  if oldTail < 0
    then Control.do
      watchHeads <-
        Fixed.unsafeWrite literal occurrence watchHeads
      watchTails <-
        Fixed.unsafeWrite literal occurrence watchTails
      Control.pure (watchHeads, watchTails, nexts)
    else Control.do
      nexts <-
        Grow.pinnedBufferUnsafeWrite oldTail occurrence nexts
      watchTails <-
        Fixed.unsafeWrite literal occurrence watchTails
      Control.pure (watchHeads, watchTails, nexts)

restoreOccurrenceChain ::
  Int ->
  Int ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Grow.PinnedBuffer α Int
    )
{-# INLINE restoreOccurrenceChain #-}
restoreOccurrenceChain literal occurrence watchHeads watchTails nexts
  | occurrence < 0 =
      Control.pure (watchHeads, watchTails, nexts)
  | otherwise = Control.do
      (Ur nextOccurrence, nexts) <-
        Grow.pinnedBufferUnsafeCopyAt occurrence nexts
      (watchHeads, watchTails, nexts) <-
        appendOccurrence
          literal
          occurrence
          watchHeads
          watchTails
          nexts
      restoreOccurrenceChain
        literal
        nextOccurrence
        watchHeads
        watchTails
        nexts

bodyBase :: Int
bodyBase = 65536

encodeBody :: Int -> Int -> Int
encodeBody watched1 watched2 =
  (watched1 + 1) * bodyBase + watched2 + 1

decodeBody :: Int -> (Int, Int)
decodeBody encoded =
  (encoded `div` bodyBase - 1, encoded `mod` bodyBase - 1)

propagationLoop ::
  Int ->
  Int ->
  PropagationControl %1 ->
  Store.VSIDSState s %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Mut α (Fixed.UArray Int) %1 ->
  Boxed.PinnedBuffer α (Ur (U.Vector Int)) %1 ->
  Grow.PinnedBuffer α Int %1 ->
  Grow.PinnedBuffer α Int %1 ->
  BO
    α
    ( Ur PropagationEvidence
    , PropagationControl
    , Store.VSIDSState s
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Mut α (Fixed.UArray Int)
    , Boxed.PinnedBuffer α (Ur (U.Vector Int))
    , Grow.PinnedBuffer α Int
    , Grow.PinnedBuffer α Int
    )
{-# INLINE propagationLoop #-}
propagationLoop !visited !checksum control vsids watchHeads watchTails valuation trail literals bodies nexts =
  case move control of
    Ur (PropagationControl cursor limit)
      | cursor >= limit ->
          Control.pure
            ( Ur
                PropagationEvidence
                  { visitedOccurrences = visited
                  , observationChecksum = checksum
                  }
            , PropagationControl cursor limit
            , vsids
            , watchHeads
            , watchTails
            , valuation
            , trail
            , literals
            , bodies
            , nexts
            )
      | otherwise -> Control.do
          (Ur trailLiteral, trail) <-
            Fixed.unsafeCopyAtMut cursor trail
          (Ur variableValue, valuation) <-
            Fixed.unsafeCopyAtMut cursor valuation
          (Ur bucketHead, watchHeads) <-
            Fixed.unsafeCopyAtMut trailLiteral watchHeads
          (Ur bucketTail, watchTails) <-
            Fixed.unsafeCopyAtMut trailLiteral watchTails
          (Ur (Ur clause), literals) <-
            Boxed.pinnedBufferUnsafeCopyAt cursor literals
          (Ur body, bodies) <-
            Grow.pinnedBufferUnsafeCopyAt cursor bodies
          (Ur nextOccurrence, nexts) <-
            Grow.pinnedBufferUnsafeCopyAt cursor nexts
          bodies <-
            Grow.pinnedBufferUnsafeWrite
              cursor
              (body + 1)
              bodies
          nexts <-
            Grow.pinnedBufferUnsafeWrite cursor nextOccurrence nexts
          watchHeads <-
            Fixed.unsafeWrite trailLiteral bucketHead watchHeads
          watchTails <-
            Fixed.unsafeWrite trailLiteral bucketTail watchTails
          valuation <-
            Fixed.unsafeWrite cursor variableValue valuation
          let !nextChecksum =
                checksum
                  + trailLiteral
                  + variableValue
                  + bucketHead
                  + bucketTail
                  + U.length clause
                  + body
                  + nextOccurrence
          propagationLoop
            (visited + 1)
            nextChecksum
            (PropagationControl (cursor + 1) limit)
            (Store.bumpVSIDS vsids)
            watchHeads
            watchTails
            valuation
            trail
            literals
            bodies
            nexts
