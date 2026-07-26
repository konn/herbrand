{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Propagation.Production.Internal (
  PropagationStart (..),
  propagateFrom,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.Record.Linear.Borrow.Experimental.PatternMatch ((.@))
import Data.Ref.Linear.Borrow qualified as RefBorrow
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal qualified as Grow
import Data.Vector.Unboxed qualified as U
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Control.Internal qualified as SolverControl
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Propagation.Kernel.Internal qualified as Kernel
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Runtime.Internal qualified as Runtime
import Logic.Propositional.Classical.SAT.CDCL.Types
import Prelude.Linear
import Prelude qualified as NonLinear

data PropagationStart
  = SeedRootUnits
  | EnqueueLit {-# UNPACK #-} !Lit {-# UNPACK #-} !ClauseId
  | ResumePropagation

propagateFrom ::
  Runtime.SolverMeta ->
  PropagationStart ->
  SolverControl.SolverControl %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur PropResult
    , SolverControl.SolverControl
    , Mut lifetime (Runtime.CDCLStore s)
    )
{-# INLINE propagateFrom #-}
propagateFrom meta start =
  withPropagationTransaction (propagationWorker meta start)

-- All hot stores stay pinned for one propagation transaction.
data KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s where
  KernelStores ::
    VSIDSState s %1 ->
    Fixed.Pinned headsPin Int %1 ->
    Fixed.Pinned tailsPin Int %1 ->
    Fixed.Pinned valuationPin Variable %1 ->
    Fixed.Pinned trailPin Lit %1 ->
    Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit)) %1 ->
    Grow.PinnedBuffer bodiesPin ClauseBody %1 ->
    Grow.PinnedBuffer nextsPin Int %1 ->
    KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s

withPropagationTransaction ::
  ( forall local headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin.
    control %1 ->
    KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s %1 ->
    BO
      local
      ( result
      , control
      , KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s
      )
  ) %1 ->
  control %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( result
    , control
    , Mut lifetime (Runtime.CDCLStore s)
    )
{-# INLINE withPropagationTransaction #-}
withPropagationTransaction worker control store = Control.do
  ((result, finalControl), store) <-
    reborrowing store \local -> Control.do
      let %1 !(watches, clauses, valuation, trail, vsids) =
            local
              .@ ( Runtime.watchesField
                 , Runtime.clausesField
                 , Runtime.valuationField
                 , Runtime.trailField
                 , Runtime.vsidsField
                 )
      let %1 !(watchHeads, watchTails, watchNexts) =
            watches
              .@ ( Runtime.watchHeadsField
                 , Runtime.watchTailsField
                 , Runtime.watchNextsField
                 )
      let %1 !(clauseLiterals, clauseBodies) =
            clauses
              .@ ( Runtime.clauseLiteralsField
                 , Runtime.clauseBodiesField
                 )
      ( ( result
          , finalControl
          , watchHeads
          , watchTails
          , valuation
          , trail
          , clauseLiterals
          , clauseBodies
          , watchNexts
          )
        , vsids
        ) <-
        RefBorrow.update
          ( \vsidsState -> Control.do
              ( ( result
                  , finalControl
                  , vsidsState
                  , watchHeads
                  , watchTails
                  , valuation
                  , trail
                  )
                , (clauseLiterals, clauseBodies, watchNexts)
                ) <-
                withPinnedStores
                  ( \literalsPinned bodiesPinned nextsPinned -> Control.do
                      ( ( result
                          , finalControl
                          , vsidsState
                          , literalsPinned
                          , bodiesPinned
                          , nextsPinned
                          )
                        , (watchHeads, watchTails, valuation, trail)
                        ) <-
                        withPinnedFixedStores
                          ( \headsPinned tailsPinned valuationPinned trailPinned -> Control.do
                              ( result
                                , finalControl
                                , KernelStores
                                    vsidsState
                                    headsPinned
                                    tailsPinned
                                    valuationPinned
                                    trailPinned
                                    literalsPinned
                                    bodiesPinned
                                    nextsPinned
                                ) <-
                                worker
                                  control
                                  ( KernelStores
                                      vsidsState
                                      headsPinned
                                      tailsPinned
                                      valuationPinned
                                      trailPinned
                                      literalsPinned
                                      bodiesPinned
                                      nextsPinned
                                  )
                              Control.pure
                                (
                                  ( result
                                  , finalControl
                                  , vsidsState
                                  , literalsPinned
                                  , bodiesPinned
                                  , nextsPinned
                                  )
                                ,
                                  ( headsPinned
                                  , tailsPinned
                                  , valuationPinned
                                  , trailPinned
                                  )
                                )
                          )
                          watchHeads
                          watchTails
                          valuation
                          trail
                      Control.pure
                        (
                          ( result
                          , finalControl
                          , vsidsState
                          , watchHeads
                          , watchTails
                          , valuation
                          , trail
                          )
                        , (literalsPinned, bodiesPinned, nextsPinned)
                        )
                  )
                  clauseLiterals
                  clauseBodies
                  watchNexts
              Control.pure
                (
                  ( result
                  , finalControl
                  , watchHeads
                  , watchTails
                  , valuation
                  , trail
                  , clauseLiterals
                  , clauseBodies
                  , watchNexts
                  )
                , vsidsState
                )
          )
          vsids
      let !(Ur _) = share watchHeads
      let !(Ur _) = share watchTails
      let !(Ur _) = share valuation
      let !(Ur _) = share trail
      let !(Ur _) = share clauseLiterals
      let !(Ur _) = share clauseBodies
      let !(Ur _) = share watchNexts
      let !(Ur _) = share vsids
      Control.pure (result, finalControl)
  Control.pure (result, finalControl, store)

withPinnedFixedStores ::
  (lifetime >= scope) =>
  ( forall headsPin tailsPin valuationPin trailPin.
    Fixed.Pinned headsPin Int %1 ->
    Fixed.Pinned tailsPin Int %1 ->
    Fixed.Pinned valuationPin Variable %1 ->
    Fixed.Pinned trailPin Lit %1 ->
    BO
      scope
      ( result
      , ( Fixed.Pinned headsPin Int
        , Fixed.Pinned tailsPin Int
        , Fixed.Pinned valuationPin Variable
        , Fixed.Pinned trailPin Lit
        )
      )
  ) %1 ->
  Mut lifetime (Fixed.UArray Int) %1 ->
  Mut lifetime (Fixed.UArray Int) %1 ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  BO
    scope
    ( result
    , ( Mut lifetime (Fixed.UArray Int)
      , Mut lifetime (Fixed.UArray Int)
      , Mut lifetime (Fixed.UArray Variable)
      , Mut lifetime (Fixed.UArray Lit)
      )
    )
{-# INLINE withPinnedFixedStores #-}
withPinnedFixedStores action heads tails valuation trail = Control.do
  ((result, tails, valuation, trail), heads) <-
    Fixed.withPinned
      ( \headsPinned -> Control.do
          ((result, headsPinned, valuation, trail), tails) <-
            Fixed.withPinned
              ( \tailsPinned -> Control.do
                  ((result, headsPinned, tailsPinned, trail), valuation) <-
                    Fixed.withPinned
                      ( \valuationPinned -> Control.do
                          ((result, headsPinned, tailsPinned, valuationPinned), trail) <-
                            Fixed.withPinned
                              ( \trailPinned -> Control.do
                                  ( result
                                    , ( headsPinned
                                        , tailsPinned
                                        , valuationPinned
                                        , trailPinned
                                        )
                                    ) <-
                                    action
                                      headsPinned
                                      tailsPinned
                                      valuationPinned
                                      trailPinned
                                  Control.pure
                                    (
                                      ( result
                                      , headsPinned
                                      , tailsPinned
                                      , valuationPinned
                                      )
                                    , trailPinned
                                    )
                              )
                              trail
                          Control.pure
                            (
                              ( result
                              , headsPinned
                              , tailsPinned
                              , trail
                              )
                            , valuationPinned
                            )
                      )
                      valuation
                  Control.pure
                    ( (result, headsPinned, valuation, trail)
                    , tailsPinned
                    )
              )
              tails
          Control.pure
            ( (result, tails, valuation, trail)
            , headsPinned
            )
      )
      heads
  Control.pure (result, (heads, tails, valuation, trail))

withPinnedStores ::
  (lifetime >= scope) =>
  ( forall literalsPin bodiesPin nextsPin.
    Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit)) %1 ->
    Grow.PinnedBuffer bodiesPin ClauseBody %1 ->
    Grow.PinnedBuffer nextsPin Int %1 ->
    BO
      scope
      ( result
      , ( Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit))
        , Grow.PinnedBuffer bodiesPin ClauseBody
        , Grow.PinnedBuffer nextsPin Int
        )
      )
  ) %1 ->
  Mut lifetime (Boxed.Vector (Ur (U.Vector Lit))) %1 ->
  Mut lifetime (Grow.Vector ClauseBody) %1 ->
  Mut lifetime (Grow.Vector Int) %1 ->
  BO
    scope
    ( result
    , ( Mut lifetime (Boxed.Vector (Ur (U.Vector Lit)))
      , Mut lifetime (Grow.Vector ClauseBody)
      , Mut lifetime (Grow.Vector Int)
      )
    )
{-# INLINE withPinnedStores #-}
withPinnedStores action literals bodies nexts = Control.do
  ((result, bodies, nexts), literals) <-
    Boxed.withPinnedBuffer
      ( \_ literalsPinned -> Control.do
          ((result, literalsPinned, nexts), bodies) <-
            Grow.withPinnedBuffer
              ( \_ bodiesPinned -> Control.do
                  ((result, literalsPinned, bodiesPinned), nexts) <-
                    Grow.withPinnedBuffer
                      ( \_ nextsPinned -> Control.do
                          ( result
                            , ( literalsPinned
                                , bodiesPinned
                                , nextsPinned
                                )
                            ) <-
                            action
                              literalsPinned
                              bodiesPinned
                              nextsPinned
                          Control.pure
                            ( (result, literalsPinned, bodiesPinned)
                            , nextsPinned
                            )
                      )
                      nexts
                  Control.pure
                    ( (result, literalsPinned, nexts)
                    , bodiesPinned
                    )
              )
              bodies
          Control.pure
            ( (result, bodies, nexts)
            , literalsPinned
            )
      )
      literals
  Control.pure (result, (literals, bodies, nexts))

propagationWorker ::
  Runtime.SolverMeta ->
  PropagationStart ->
  SolverControl.SolverControl %1 ->
  KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s %1 ->
  BO
    scope
    ( Ur PropResult
    , SolverControl.SolverControl
    , KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s
    )
{-# INLINE propagationWorker #-}
propagationWorker meta start control stores =
  case start of
    ResumePropagation ->
      drainTrail meta control stores
    EnqueueLit literal reason -> Control.do
      (Ur assertion, control, stores) <-
        enqueueLiteral reason literal control stores
      case assertion of
        ContradictingAssertion ->
          Control.pure
            (Ur (ConflictFound reason literal), control, stores)
        AlreadyAsserted ->
          drainTrail
            meta
            (SolverControl.bumpDuplicateEnqueue control)
            stores
        NewlyAsserted ->
          drainTrail meta control stores
    SeedRootUnits ->
      seedRootUnits
        meta
        0
        (SolverControl.bumpSeedScan control)
        stores

seedRootUnits ::
  Runtime.SolverMeta ->
  Int ->
  SolverControl.SolverControl %1 ->
  KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s %1 ->
  BO
    scope
    ( Ur PropResult
    , SolverControl.SolverControl
    , KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s
    )
{-# INLINE seedRootUnits #-}
seedRootUnits meta !clauseIndex control stores =
  if clauseIndex == Runtime.numInitialClauses meta
    then drainTrail meta control stores
    else case stores of
      KernelStores vsids heads tails valuation trail literals bodies nexts -> Control.do
        (Ur body@ClauseBody {wat1, wat2}, bodies) <-
          Grow.pinnedBufferUnsafeCopyAt clauseIndex bodies
        if wat2 >= 0
          then
            seedRootUnits
              meta
              (clauseIndex + 1)
              control
              ( KernelStores
                  vsids
                  heads
                  tails
                  valuation
                  trail
                  literals
                  bodies
                  nexts
              )
          else Control.do
            (Ur (Ur clause), literals) <-
              Boxed.pinnedBufferUnsafeCopyAt clauseIndex literals
            let !unitLiteral =
                  if wat1 >= 0
                    then U.unsafeIndex clause wat1
                    else
                      error
                        "seedRootUnits: empty clause escaped preparation"
                        body
            ( Ur assertion
              , control
              , KernelStores
                  vsids
                  heads
                  tails
                  valuation
                  trail
                  literals
                  bodies
                  nexts
              ) <-
              enqueueLiteral
                (ClauseId clauseIndex)
                unitLiteral
                control
                ( KernelStores
                    vsids
                    heads
                    tails
                    valuation
                    trail
                    literals
                    bodies
                    nexts
                )
            case assertion of
              ContradictingAssertion ->
                Control.pure
                  ( Ur
                      ( ConflictFound
                          (ClauseId clauseIndex)
                          unitLiteral
                      )
                  , control
                  , KernelStores
                      vsids
                      heads
                      tails
                      valuation
                      trail
                      literals
                      bodies
                      nexts
                  )
              AlreadyAsserted ->
                seedRootUnits
                  meta
                  (clauseIndex + 1)
                  (SolverControl.bumpDuplicateEnqueue control)
                  ( KernelStores
                      vsids
                      heads
                      tails
                      valuation
                      trail
                      literals
                      bodies
                      nexts
                  )
              NewlyAsserted ->
                seedRootUnits
                  meta
                  (clauseIndex + 1)
                  control
                  ( KernelStores
                      vsids
                      heads
                      tails
                      valuation
                      trail
                      literals
                      bodies
                      nexts
                  )

enqueueLiteral ::
  ClauseId ->
  Lit ->
  SolverControl.SolverControl %1 ->
  KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s %1 ->
  BO
    scope
    ( Ur AssertionResult
    , SolverControl.SolverControl
    , KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s
    )
{-# INLINE enqueueLiteral #-}
enqueueLiteral
  reason
  literal
  control
  (KernelStores vsids heads tails valuation trail literals bodies nexts) = Control.do
    (Ur variable, valuation) <-
      Fixed.pinnedUnsafeCopyAt
        (fromVarId (litVar literal))
        valuation
    case variable of
      Indefinite ->
        case SolverControl.assignmentContext control of
          (Ur (decideLevel, decisionStep), control) -> Control.do
            let !antecedent =
                  if unClauseId reason NonLinear.< 0
                    then Nothing
                    else Just reason
            valuation <-
              Fixed.pinnedUnsafeWrite
                (fromVarId (litVar literal))
                Definite
                  { value = isPositive literal
                  , decideLevel
                  , decisionStep
                  , antecedent
                  }
                valuation
            trail <-
              Fixed.pinnedUnsafeWrite
                (NonLinear.fromIntegral (unStep decisionStep))
                literal
                trail
            Control.pure
              ( Ur NewlyAsserted
              , SolverControl.appendAssignment control
              , KernelStores
                  (moveToSatQueue (litVar literal) vsids)
                  heads
                  tails
                  valuation
                  trail
                  literals
                  bodies
                  nexts
              )
      Definite {value}
        | value == isPositive literal ->
            Control.pure
              ( Ur AlreadyAsserted
              , control
              , KernelStores
                  vsids
                  heads
                  tails
                  valuation
                  trail
                  literals
                  bodies
                  nexts
              )
        | otherwise ->
            Control.pure
              ( Ur ContradictingAssertion
              , control
              , KernelStores
                  vsids
                  heads
                  tails
                  valuation
                  trail
                  literals
                  bodies
                  nexts
              )

type KernelResult result headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s =
  ( Ur result
  , SolverControl.SolverControl
  , VSIDSState s
  , Fixed.Pinned headsPin Int
  , Fixed.Pinned tailsPin Int
  , Fixed.Pinned valuationPin Variable
  , Fixed.Pinned trailPin Lit
  , Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit))
  , Grow.PinnedBuffer bodiesPin ClauseBody
  , Grow.PinnedBuffer nextsPin Int
  )

drainTrail ::
  Runtime.SolverMeta ->
  SolverControl.SolverControl %1 ->
  KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s %1 ->
  BO
    scope
    ( Ur PropResult
    , SolverControl.SolverControl
    , KernelStores headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s
    )
{-# INLINE drainTrail #-}
drainTrail
  meta
  control
  (KernelStores vsids heads tails valuation trail literals bodies nexts) = Control.do
    ( result
      , control
      , vsids
      , heads
      , tails
      , valuation
      , trail
      , literals
      , bodies
      , nexts
      ) <-
      drainTrailRaw
        meta
        control
        vsids
        heads
        tails
        valuation
        trail
        literals
        bodies
        nexts
    Control.pure
      ( result
      , control
      , KernelStores
          vsids
          heads
          tails
          valuation
          trail
          literals
          bodies
          nexts
      )

drainTrailRaw ::
  Runtime.SolverMeta ->
  SolverControl.SolverControl %1 ->
  VSIDSState s %1 ->
  Fixed.Pinned headsPin Int %1 ->
  Fixed.Pinned tailsPin Int %1 ->
  Fixed.Pinned valuationPin Variable %1 ->
  Fixed.Pinned trailPin Lit %1 ->
  Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit)) %1 ->
  Grow.PinnedBuffer bodiesPin ClauseBody %1 ->
  Grow.PinnedBuffer nextsPin Int %1 ->
  BO
    scope
    (KernelResult PropResult headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s)
{-# INLINE drainTrailRaw #-}
drainTrailRaw meta control vsids heads tails valuation trail literals bodies nexts =
  case SolverControl.propagationCursor control of
    (Ur (qhead, trailLength), control)
      | qhead == trailLength ->
          Control.pure
            ( Ur NoMorePropagation
            , control
            , vsids
            , heads
            , tails
            , valuation
            , trail
            , literals
            , bodies
            , nexts
            )
      | qhead > trailLength ->
          error
            ("propagation cursor exceeds trail: " <> show (qhead, trailLength))
            control
            vsids
            heads
            tails
            valuation
            trail
            literals
            bodies
            nexts
      | otherwise -> Control.do
          (Ur assertedLiteral, trail) <-
            Fixed.pinnedUnsafeCopyAt qhead trail
          let !falseLiteral = negL assertedLiteral
              !bucket = litBucketIndex falseLiteral
          (Ur firstOccurrence, heads) <-
            Fixed.pinnedUnsafeCopyAt bucket heads
          heads <- Fixed.pinnedUnsafeWrite bucket (-1) heads
          tails <- Fixed.pinnedUnsafeWrite bucket (-1) tails
          processOccurrencesRaw
            meta
            falseLiteral
            firstOccurrence
            (SolverControl.advancePropagation control)
            vsids
            heads
            tails
            valuation
            trail
            literals
            bodies
            nexts

processOccurrencesRaw ::
  Runtime.SolverMeta ->
  Lit ->
  Int ->
  SolverControl.SolverControl %1 ->
  VSIDSState s %1 ->
  Fixed.Pinned headsPin Int %1 ->
  Fixed.Pinned tailsPin Int %1 ->
  Fixed.Pinned valuationPin Variable %1 ->
  Fixed.Pinned trailPin Lit %1 ->
  Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit)) %1 ->
  Grow.PinnedBuffer bodiesPin ClauseBody %1 ->
  Grow.PinnedBuffer nextsPin Int %1 ->
  BO
    scope
    (KernelResult PropResult headsPin tailsPin valuationPin trailPin literalsPin bodiesPin nextsPin s)
{-# INLINE processOccurrencesRaw #-}
processOccurrencesRaw meta falseLiteral !occurrence control vsids heads tails valuation trail literals bodies nexts =
  Control.do
    ( Ur outcome
      , Kernel.KernelPins
          heads
          tails
          valuation
          literals
          bodies
          nexts
      ) <-
      Kernel.scanOccurrenceChain
        (Runtime.numInitialClauses meta)
        falseLiteral
        occurrence
        (Kernel.KernelPins heads tails valuation literals bodies nexts)
    case outcome of
      Kernel.ChainDrained delta ->
        drainTrailRaw
          meta
          (applyKernelDelta delta control)
          vsids
          heads
          tails
          valuation
          trail
          literals
          bodies
          nexts
      Kernel.ConflictDetected clauseId conflictLiteral delta ->
        Control.pure
          ( Ur (ConflictFound clauseId conflictLiteral)
          , applyKernelDelta delta control
          , vsids
          , heads
          , tails
          , valuation
          , trail
          , literals
          , bodies
          , nexts
          )
      Kernel.UnitRequired clauseId otherLiteral nextOccurrence delta -> Control.do
        ( Ur assertion
          , control
          , KernelStores
              vsids
              heads
              tails
              valuation
              trail
              literals
              bodies
              nexts
          ) <-
          enqueueLiteral
            clauseId
            otherLiteral
            (applyKernelDelta delta control)
            ( KernelStores
                vsids
                heads
                tails
                valuation
                trail
                literals
                bodies
                nexts
            )
        case assertion of
          ContradictingAssertion -> Control.do
            (heads, tails, nexts) <-
              restoreOccurrenceChain
                falseLiteral
                nextOccurrence
                heads
                tails
                nexts
            Control.pure
              ( Ur (ConflictFound clauseId otherLiteral)
              , control
              , vsids
              , heads
              , tails
              , valuation
              , trail
              , literals
              , bodies
              , nexts
              )
          AlreadyAsserted ->
            processOccurrencesRaw
              meta
              falseLiteral
              nextOccurrence
              (SolverControl.bumpDuplicateEnqueue control)
              vsids
              heads
              tails
              valuation
              trail
              literals
              bodies
              nexts
          NewlyAsserted ->
            processOccurrencesRaw
              meta
              falseLiteral
              nextOccurrence
              control
              vsids
              heads
              tails
              valuation
              trail
              literals
              bodies
              nexts

applyKernelDelta ::
  Kernel.KernelDelta ->
  SolverControl.SolverControl %1 ->
  SolverControl.SolverControl
{-# INLINE applyKernelDelta #-}
applyKernelDelta (Kernel.KernelDelta visitedOccurrences movedWatches inspectedLiterals) =
  SolverControl.bumpLiteralInspections inspectedLiterals
    . SolverControl.bumpWatchMoves movedWatches
    . SolverControl.bumpWatchVisits visitedOccurrences

appendOccurrence ::
  Lit ->
  Int ->
  Fixed.Pinned headsPin Int %1 ->
  Fixed.Pinned tailsPin Int %1 ->
  Grow.PinnedBuffer nextsPin Int %1 ->
  BO
    scope
    ( Fixed.Pinned headsPin Int
    , Fixed.Pinned tailsPin Int
    , Grow.PinnedBuffer nextsPin Int
    )
{-# INLINE appendOccurrence #-}
appendOccurrence literal occurrence heads tails nexts = Control.do
  let !bucket = litBucketIndex literal
  (Ur oldTail, tails) <-
    Fixed.pinnedUnsafeCopyAt bucket tails
  nexts <-
    Grow.pinnedBufferUnsafeWrite occurrence (-1) nexts
  if oldTail < 0
    then Control.do
      heads <- Fixed.pinnedUnsafeWrite bucket occurrence heads
      tails <- Fixed.pinnedUnsafeWrite bucket occurrence tails
      Control.pure (heads, tails, nexts)
    else Control.do
      nexts <-
        Grow.pinnedBufferUnsafeWrite oldTail occurrence nexts
      tails <- Fixed.pinnedUnsafeWrite bucket occurrence tails
      Control.pure (heads, tails, nexts)

restoreOccurrenceChain ::
  Lit ->
  Int ->
  Fixed.Pinned headsPin Int %1 ->
  Fixed.Pinned tailsPin Int %1 ->
  Grow.PinnedBuffer nextsPin Int %1 ->
  BO
    scope
    ( Fixed.Pinned headsPin Int
    , Fixed.Pinned tailsPin Int
    , Grow.PinnedBuffer nextsPin Int
    )
{-# INLINE restoreOccurrenceChain #-}
restoreOccurrenceChain literal !occurrence heads tails nexts =
  if occurrence < 0
    then Control.pure (heads, tails, nexts)
    else Control.do
      (Ur nextOccurrence, nexts) <-
        Grow.pinnedBufferUnsafeCopyAt occurrence nexts
      (heads, tails, nexts) <-
        appendOccurrence
          literal
          occurrence
          heads
          tails
          nexts
      restoreOccurrenceChain
        literal
        nextOccurrence
        heads
        tails
        nexts
