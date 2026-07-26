{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Solver.Internal (
  solveVarIdWithStats,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.HashSet qualified as HashSet
import Data.IntPSQ qualified as PSQ
#ifdef HERBRAND_CDCL_INSTRUMENTED
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List qualified as List
import Data.Record.Linear.Borrow.Experimental.PatternMatch ((.#), (.@))
#else
import Data.Record.Linear.Borrow.Experimental.PatternMatch ((.@))
#endif
import Data.Ord (Down (..))
import Data.Ref.Linear.Borrow qualified as RefBorrow
import Data.Semigroup (Max (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal qualified as Grow
import Data.Vector.Unboxed qualified as U
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Analysis.Internal qualified as Analysis
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Control.Internal qualified as SolverControl
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Propagation.Production.Internal qualified as Propagation
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Runtime.Internal qualified as Runtime
import Logic.Propositional.Classical.SAT.CDCL.Types
import Logic.Propositional.Classical.SAT.Types (
  Model (..),
  SatResult (..),
 )
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive (CNF)
import Prelude.Linear
import Prelude qualified as NonLinear

data ClauseClassification
  = ClauseSatisfied
  | ClauseOpen
  | ClauseUnit {-# UNPACK #-} !Lit
  | ClauseConflict
#ifdef HERBRAND_CDCL_INSTRUMENTED
  deriving (Show)
#endif

data ClauseScan = ClauseScan
  { scanSatisfied :: !Bool
  , scanUnassignedCount :: {-# UNPACK #-} !Int
  , scanUnassignedLit :: !(Maybe Lit)
  }

#ifdef HERBRAND_CDCL_INSTRUMENTED
data LearnedValidation = LearnedValidation
  { validationCurrentLevelCount :: {-# UNPACK #-} !Int
  , validationMaximumLowerLevel :: {-# UNPACK #-} !DecideLevel
  , validationSeenVariables :: !IntSet
  , validationLeastTargetLit :: !(Maybe Lit)
  }
#endif

solveVarIdWithStats ::
  CDCLOptions ->
  CNF VarId ->
  (SatResult (Model VarId), SolverStats)
solveVarIdWithStats options cnf =
  case Runtime.prepareCDCL cnf of
    Left (Ur result) ->
      (NonLinear.mempty NonLinear.<$ result, zeroSolverStats)
    Right prepared ->
      unur $
        linearly \linear -> DataFlow.do
          (allocationLinear, borrowLinear) <- dup linear
          store <- Runtime.newCDCLStore prepared allocationLinear
          runBO borrowLinear Control.do
            (storeBorrow, lender) <- borrowM store
            (Ur satisfiable, control, storeBorrow) <-
              solverLoop
                options
                (Runtime.preparedMeta prepared)
                Propagation.SeedRootUnits
                (SolverControl.initialControl options)
                storeBorrow
            let !(Ur _) = share storeBorrow
            pureAfter
              ( finishResult
                  satisfiable
                  control
                  (reclaim lender)
              )

finishResult ::
  Bool ->
  SolverControl.SolverControl %1 ->
  Runtime.CDCLStore s %1 ->
  Ur (SatResult (Model VarId), SolverStats)
finishResult satisfiable control store =
  case SolverControl.finishControl control of
    Ur stats ->
      if satisfiable
        then case Runtime.finishValuation store of
          Ur valuation ->
            Ur (Satisfiable (valuationModel valuation), stats)
        else
          Runtime.disposeCDCLStore store `lseq`
            Ur (Unsat, stats)

valuationModel :: U.Vector Variable -> Model VarId
valuationModel =
  U.ifoldl'
    ( \model index variable ->
        case variable of
          Indefinite -> model
          Definite {value}
            | value ->
                model
                  { positive =
                      HashSet.insert
                        (VarId (fromIntegral index))
                        (positive model)
                  }
            | otherwise ->
                model
                  { negative =
                      HashSet.insert
                        (VarId (fromIntegral index))
                        (negative model)
                  }
    )
    NonLinear.mempty

solverLoop ::
  CDCLOptions ->
  Runtime.SolverMeta ->
  Propagation.PropagationStart ->
  SolverControl.SolverControl %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur Bool
    , SolverControl.SolverControl
    , Mut lifetime (Runtime.CDCLStore s)
    )
solverLoop options meta start control store = Control.do
  (Ur propagation, control, store) <-
    Propagation.propagateFrom meta start control store
  case propagation of
    ConflictFound clauseId literal ->
      backjump options meta clauseId literal control store
    NoMorePropagation -> Control.do
      (Ur nextDecision, control, store) <-
        decideNext control store
      case nextDecision of
        Nothing -> Control.pure (Ur True, control, store)
        Just literal ->
          solverLoop
            options
            meta
            (Propagation.EnqueueLit literal (-1))
            control
            store

decideNext ::
  SolverControl.SolverControl %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur (Maybe Lit)
    , SolverControl.SolverControl
    , Mut lifetime (Runtime.CDCLStore s)
    )
decideNext control store = Control.do
  ((result, control), store) <-
    reborrowing store (decideTransaction control)
  Control.pure (result, control, store)

decideTransaction ::
  SolverControl.SolverControl %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur (Maybe Lit)
    , SolverControl.SolverControl
    )
decideTransaction control local = Control.do
  let %1 !(levels, trail, valuation, vsids) =
        local
          .@ ( Runtime.levelStartsField
             , Runtime.trailField
             , Runtime.valuationField
             , Runtime.vsidsField
             )
  ((result, control, levels, trail, valuation), vsids) <-
    RefBorrow.update
      (decideWithVSIDS control levels trail valuation)
      vsids
  let !(Ur _) = share levels
  let !(Ur _) = share trail
  let !(Ur _) = share valuation
  let !(Ur _) = share vsids
  Control.pure (result, control)

decideWithVSIDS ::
  (lifetime >= scope) =>
  SolverControl.SolverControl %1 ->
  Mut lifetime (Fixed.UArray Step) %1 ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  VSIDSState s %1 ->
  BO
    scope
    ( ( Ur (Maybe Lit)
      , SolverControl.SolverControl
      , Mut lifetime (Fixed.UArray Step)
      , Mut lifetime (Fixed.UArray Lit)
      , Mut lifetime (Fixed.UArray Variable)
      )
    , VSIDSState s
    )
decideWithVSIDS
  control
  levels
  trail
  valuation
  (VSIDSState unsatisfied satisfied ema exceeds increment) =
    case PSQ.minView unsatisfied of
      Nothing ->
        Control.pure
          ( (Ur Nothing, control, levels, trail, valuation)
          , VSIDSState
              unsatisfied
              satisfied
              ema
              exceeds
              increment
          )
      Just (key, priority, (), remaining) ->
        decideSelected
          (VarId (fromIntegral key))
          control
          levels
          trail
          valuation
          ( VSIDSState
              remaining
              (PSQ.unsafeInsertNew key priority () satisfied)
              ema
              exceeds
              increment
          )

decideSelected ::
  (lifetime >= scope) =>
  VarId ->
  SolverControl.SolverControl %1 ->
  Mut lifetime (Fixed.UArray Step) %1 ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  VSIDSState s %1 ->
  BO
    scope
    ( ( Ur (Maybe Lit)
      , SolverControl.SolverControl
      , Mut lifetime (Fixed.UArray Step)
      , Mut lifetime (Fixed.UArray Lit)
      , Mut lifetime (Fixed.UArray Variable)
      )
    , VSIDSState s
    )
decideSelected variable control levels trail valuation vsidsState =
  case SolverControl.assignmentContext control of
    (Ur (_, Step rawTrailLength), control) ->
      case SolverControl.pushDecisionLevel control of
        control ->
          case SolverControl.assignmentContext control of
            (Ur (decisionLevel, decisionStep), control) -> Control.do
              levels <-
                Fixed.unsafeWrite
                  (unDecideLevel decisionLevel)
                  decisionStep
                  levels
              valuation <-
                Fixed.unsafeWrite
                  (fromVarId variable)
                  Definite
                    { decideLevel = decisionLevel
                    , decisionStep = decisionStep
                    , antecedent = Nothing
                    , value = False
                    }
                  valuation
              trail <-
                Fixed.unsafeWrite
                  (fromIntegral rawTrailLength)
                  (NegL variable)
                  trail
              case SolverControl.appendAssignment control of
                control ->
                  Control.pure
                    (
                      ( Ur (Just (NegL variable))
                      , control
                      , levels
                      , trail
                      , valuation
                      )
                    , vsidsState
                    )

backjump ::
  CDCLOptions ->
  Runtime.SolverMeta ->
  ClauseId ->
  Lit ->
  SolverControl.SolverControl %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur Bool
    , SolverControl.SolverControl
    , Mut lifetime (Runtime.CDCLStore s)
    )
backjump options meta conflictClause _ control store =
  case SolverControl.assignmentContext
    (SolverControl.bumpConflict control) of
    (Ur (currentLevel, trailStep), control) -> Control.do
      (Ur analysis, control, store) <-
        Analysis.analyzeConflict
          options
          currentLevel
          (NonLinear.fromIntegral (unStep trailStep))
          conflictClause
          control
          store
      case analysis of
        Analysis.RootConflict {} -> Control.do
          store <- validateConflictClause conflictClause store
          Control.pure (Ur False, control, store)
        Analysis.LearnedClause analysisLevel learned analysisLiteral _ -> Control.do
          store <-
            validateLearnedAnalysis
              currentLevel
              analysisLevel
              learned
              analysisLiteral
              store
          (Ur reason, store) <-
            insertLearned options learned store
          (control, store) <-
            backtrack False analysisLevel control store
          case SolverControl.tryRestart options control of
            (Ur Continued, control) -> Control.do
              store <-
                validateAssertingReason
                  reason
                  analysisLiteral
                  store
              solverLoop
                options
                meta
                (Propagation.EnqueueLit analysisLiteral reason)
                control
                store
            (Ur Restarted, control) -> Control.do
              (control, store) <-
                backtrack True 0 control store
              (Ur classification, store) <-
                classifyClause reason store
              case validateRestartedLearnedClause
                analysisLiteral
                classification of
                () -> case classification of
                  ClauseConflict ->
                    Control.pure (Ur False, control, store)
                  ClauseUnit unitLiteral ->
                    solverLoop
                      options
                      meta
                      (Propagation.EnqueueLit unitLiteral reason)
                      control
                      store
                  ClauseSatisfied ->
                    solverLoop
                      options
                      meta
                      Propagation.ResumePropagation
                      control
                      store
                  ClauseOpen ->
                    solverLoop
                      options
                      meta
                      Propagation.ResumePropagation
                      control
                      store

insertLearned ::
  forall lifetime s.
  CDCLOptions ->
  Clause ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur ClauseId
    , Mut lifetime (Runtime.CDCLStore s)
    )
insertLearned options Clause {lits, watched1, watched2} store = Control.do
  (reason, store) <-
    reborrowing store \local -> Control.do
      let %1 !(clauses, watches, valuation, vsids) =
            local
              .@ ( Runtime.clausesField
                 , Runtime.watchesField
                 , Runtime.valuationField
                 , Runtime.vsidsField
                 )
      let %1 !(clauseLiterals, clauseBodies) =
            clauses
              .@ ( Runtime.clauseLiteralsField
                 , Runtime.clauseBodiesField
                 )
      let %1 !(watchHeads, watchTails, watchNexts) =
            watches
              .@ ( Runtime.watchHeadsField
                 , Runtime.watchTailsField
                 , Runtime.watchNextsField
                 )
      (Ur clauseCount, clauseLiterals) <-
        boxedMutableSize clauseLiterals
      (Ur lbd, valuation) <-
        calculateLBD (U.toList lits) Set.empty valuation
      clauseLiterals <- Boxed.push (Ur lits) clauseLiterals
      clauseBodies <-
        Grow.push
          ClauseBody {wat1 = watched1, wat2 = watched2}
          clauseBodies
      watchNexts <- Grow.push (-1) watchNexts
      watchNexts <- Grow.push (-1) watchNexts
      let !reason = ClauseId clauseCount
      (watchHeads, watchTails, watchNexts) <-
        if watched1 < 0
          then
            Control.pure (watchHeads, watchTails, watchNexts)
          else
            linkNewOccurrence
              (U.unsafeIndex lits watched1)
              (watchOccurrence reason W1)
              watchHeads
              watchTails
              watchNexts
      (watchHeads, watchTails, watchNexts) <-
        if watched2 < 0
          then
            Control.pure (watchHeads, watchTails, watchNexts)
          else
            linkNewOccurrence
              (U.unsafeIndex lits watched2)
              (watchOccurrence reason W2)
              watchHeads
              watchTails
              watchNexts
      ((), vsids) <-
        RefBorrow.update
          ( \vsidsState ->
              Control.pure
                ( ()
                , bumpLearnedActivities
                    options
                    lbd
                    lits
                    vsidsState
                )
          )
          vsids
      let !(Ur _) = share clauseLiterals
      let !(Ur _) = share clauseBodies
      let !(Ur _) = share watchHeads
      let !(Ur _) = share watchTails
      let !(Ur _) = share watchNexts
      let !(Ur _) = share valuation
      let !(Ur _) = share vsids
      Control.pure (Ur reason)
  Control.pure (reason, store)

boxedMutableSize ::
  Mut lifetime (Boxed.Vector a) %1 ->
  BO lifetime (Ur Int, Mut lifetime (Boxed.Vector a))
boxedMutableSize =
  Boxed.withPinned \pinned ->
    case Boxed.pinnedSize pinned of
      (Ur logicalSize, pinned) ->
        Control.pure (Ur logicalSize, pinned)

calculateLBD ::
  (lifetime >= scope) =>
  [Lit] ->
  Set DecideLevel ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  BO
    scope
    ( Ur Int
    , Mut lifetime (Fixed.UArray Variable)
    )
calculateLBD [] levels valuation =
  Control.pure (Ur (Set.size levels), valuation)
calculateLBD (literal : rest) levels valuation = Control.do
  (Ur variable, valuation) <-
    Fixed.unsafeCopyAtMut
      (fromVarId (litVar literal))
      valuation
  let !updated =
        case variable of
          Indefinite -> levels
          Definite {decideLevel} -> Set.insert decideLevel levels
  calculateLBD rest updated valuation

linkNewOccurrence ::
  (lifetime >= scope) =>
  Lit ->
  Int ->
  Mut lifetime (Fixed.UArray Int) %1 ->
  Mut lifetime (Fixed.UArray Int) %1 ->
  Mut lifetime (Grow.Vector Int) %1 ->
  BO
    scope
    ( Mut lifetime (Fixed.UArray Int)
    , Mut lifetime (Fixed.UArray Int)
    , Mut lifetime (Grow.Vector Int)
    )
linkNewOccurrence literal occurrence heads tails nexts = Control.do
  let !bucket = litBucketIndex literal
  (Ur oldTail, tails) <- Fixed.unsafeCopyAtMut bucket tails
  if oldTail < 0
    then Control.do
      heads <- Fixed.unsafeWrite bucket occurrence heads
      tails <- Fixed.unsafeWrite bucket occurrence tails
      Control.pure (heads, tails, nexts)
    else Control.do
      nexts <- Grow.unsafeWrite oldTail occurrence nexts
      tails <- Fixed.unsafeWrite bucket occurrence tails
      Control.pure (heads, tails, nexts)

bumpLearnedActivities ::
  CDCLOptions ->
  Int ->
  U.Vector Lit ->
  VSIDSState s %1 ->
  VSIDSState s
bumpLearnedActivities options lbd literals state =
  case state of
    VSIDSState unsatisfied satisfied ema exceeds increment ->
      let (!maximumActivity, !updatedUnsatisfied, !updatedSatisfied) =
            incrementQueues
              increment
              0
              literals
              Nothing
              unsatisfied
              satisfied
          (!updatedEma, !updatedExceeds) =
            case decayFactor options of
              ConstantFactor {} -> (ema, exceeds)
              Adaptive {lbdEmaDecayFactor} ->
                let !nextEma =
                      ema
                        * lbdEmaDecayFactor
                        + fromIntegral lbd
                        * (1 - lbdEmaDecayFactor)
                 in (nextEma, fromIntegral lbd >= nextEma)
       in rescaleActivities
            maximumActivity
            ( VSIDSState
                updatedUnsatisfied
                updatedSatisfied
                updatedEma
                updatedExceeds
                increment
            )

incrementQueues ::
  Double ->
  Int ->
  U.Vector Lit ->
  Maybe (Max Double) ->
  VarQueue ->
  VarQueue ->
  (Maybe (Max Double), VarQueue, VarQueue)
incrementQueues increment index literals maximumActivity unsatisfied satisfied
  | index == U.length literals =
      (maximumActivity, unsatisfied, satisfied)
  | otherwise =
      let !literal = U.unsafeIndex literals index
          (!unsatisfiedMaximum, !updatedUnsatisfied) =
            incrementQueue increment literal unsatisfied
          (!satisfiedMaximum, !updatedSatisfied) =
            incrementQueue increment literal satisfied
       in incrementQueues
            increment
            (index + 1)
            literals
            ( maximumActivity
                NonLinear.<> unsatisfiedMaximum
                NonLinear.<> satisfiedMaximum
            )
            updatedUnsatisfied
            updatedSatisfied

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
  VSIDSState s %1 ->
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

backtrack ::
  Bool ->
  DecideLevel ->
  SolverControl.SolverControl %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( SolverControl.SolverControl
    , Mut lifetime (Runtime.CDCLStore s)
    )
backtrack isRestart target control store =
  case SolverControl.currentDecideLevel control of
    (Ur currentLevel, control) ->
      case SolverControl.assignmentContext control of
        (Ur (_, Step rawTrailLength), control) ->
          case unDecideLevel target
            NonLinear.> unDecideLevel currentLevel of
            True ->
              error
                ( "backtrack target exceeds current level: "
                    <> show (target, currentLevel)
                )
                control
                store
            False -> Control.do
              (control, store) <-
                reborrowing
                  store
                  ( backtrackTransaction
                      isRestart
                      target
                      currentLevel
                      (fromIntegral rawTrailLength)
                      control
                  )
              Control.pure (control, store)

backtrackTransaction ::
  Bool ->
  DecideLevel ->
  DecideLevel ->
  Int ->
  SolverControl.SolverControl %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO lifetime SolverControl.SolverControl
backtrackTransaction isRestart target currentLevel trailLength control local =
  Control.do
    let %1 !(levels, trail, valuation, vsids) =
          local
            .@ ( Runtime.levelStartsField
               , Runtime.trailField
               , Runtime.valuationField
               , Runtime.vsidsField
               )
    (Ur cutoff, levels) <-
      case unDecideLevel target
        NonLinear.< unDecideLevel currentLevel of
        True -> Control.do
          (Ur (Step rawCutoff), levels) <-
            Fixed.unsafeCopyAtMut
              (unDecideLevel target + 1)
              levels
          Control.pure (Ur (fromIntegral rawCutoff), levels)
        False -> Control.pure (Ur trailLength, levels)
    ((Ur cleared, trail, valuation), vsids) <-
      RefBorrow.update
        (clearWithVSIDS trailLength cutoff trail valuation)
        vsids
    case SolverControl.recordBacktrack
      isRestart
      ( if unDecideLevel target
          NonLinear.< unDecideLevel currentLevel
          then 1
          else 0
      )
      cleared
      cleared
      0
      0
      ( SolverControl.setBacktrackState
          target
          cutoff
          control
      ) of
      control -> Control.do
        let !(Ur _) = share levels
        let !(Ur _) = share trail
        let !(Ur _) = share valuation
        let !(Ur _) = share vsids
        Control.pure control

clearWithVSIDS ::
  (lifetime >= scope) =>
  Int ->
  Int ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  VSIDSState s %1 ->
  BO
    scope
    ( ( Ur Int
      , Mut lifetime (Fixed.UArray Lit)
      , Mut lifetime (Fixed.UArray Variable)
      )
    , VSIDSState s
    )
clearWithVSIDS trailLength cutoff trail valuation vsidsState = Control.do
  (Ur cleared, trail, valuation, vsidsState) <-
    clearTrail
      (trailLength - 1)
      cutoff
      0
      trail
      valuation
      vsidsState
  Control.pure
    ( (Ur cleared, trail, valuation)
    , vsidsState
    )

clearTrail ::
  (lifetime >= scope) =>
  Int ->
  Int ->
  Int ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  VSIDSState s %1 ->
  BO
    scope
    ( Ur Int
    , Mut lifetime (Fixed.UArray Lit)
    , Mut lifetime (Fixed.UArray Variable)
    , VSIDSState s
    )
clearTrail index cutoff cleared trail valuation vsids
  | index < cutoff =
      Control.pure (Ur cleared, trail, valuation, vsids)
  | otherwise = Control.do
      (Ur literal, trail) <- Fixed.unsafeCopyAtMut index trail
      valuation <-
        Fixed.unsafeWrite
          (fromVarId (litVar literal))
          Indefinite
          valuation
      clearTrail
        (index - 1)
        cutoff
        (cleared + 1)
        trail
        valuation
        (moveToUnsatQueue (litVar literal) vsids)

classifyClause ::
  ClauseId ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur ClauseClassification
    , Mut lifetime (Runtime.CDCLStore s)
    )
classifyClause clauseId store = Control.do
  (classification, store) <-
    reborrowing store \local -> Control.do
      let %1 !(clauses, valuation) =
            local
              .@ ( Runtime.clausesField
                 , Runtime.valuationField
                 )
      let %1 !(literals, bodies) =
            clauses
              .@ ( Runtime.clauseLiteralsField
                 , Runtime.clauseBodiesField
                 )
      (Ur (Ur clause), literals) <-
        Boxed.unsafeCopyAtMut
          (unClauseId clauseId)
          literals
      (Ur scan, valuation) <-
        scanClause
          (U.toList clause)
          (ClauseScan False 0 Nothing)
          valuation
      let !classification =
            if scanSatisfied scan
              then ClauseSatisfied
              else case scanUnassignedCount scan of
                0 -> ClauseConflict
                1 -> case scanUnassignedLit scan of
                  Just unitLiteral -> ClauseUnit unitLiteral
                  Nothing ->
                    error
                      ( "classifyClause: missing unit literal "
                          <> show clauseId
                      )
                _ -> ClauseOpen
      let !(Ur _) = share literals
      let !(Ur _) = share bodies
      let !(Ur _) = share valuation
      Control.pure (Ur classification)
  Control.pure (classification, store)

#ifdef HERBRAND_CDCL_INSTRUMENTED
validateConflictClause ::
  ClauseId ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO lifetime (Mut lifetime (Runtime.CDCLStore s))
validateConflictClause clauseId store = Control.do
  (Ur classification, store) <- classifyClause clauseId store
  case classification of
    ClauseConflict -> Control.pure store
    _ ->
      validationFailure
        ( "reported conflict clause is not fully false: "
            <> show (clauseId, classification)
        )
        store

validateLearnedAnalysis ::
  DecideLevel ->
  DecideLevel ->
  Clause ->
  Lit ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO lifetime (Mut lifetime (Runtime.CDCLStore s))
validateLearnedAnalysis currentLevel target Clause {lits, watched1, watched2} assertingLit store
  | unDecideLevel currentLevel NonLinear.<= 0 =
      validationFailure
        ( "learned analysis has a nonpositive conflict level: "
            <> show currentLevel
        )
        store
  | unDecideLevel target NonLinear.< 0
      NonLinear.|| unDecideLevel target NonLinear.>= unDecideLevel currentLevel =
      validationFailure
        ( "learned analysis has an invalid target level: "
            <> show (target, currentLevel)
        )
        store
  | U.null lits =
      validationFailure
        "learned analysis returned an empty clause"
        store
  | U.unsafeIndex lits 0 NonLinear./= assertingLit =
      validationFailure
        ( "learned clause does not start with its asserting literal: "
            <> show (assertingLit, U.toList lits)
        )
        store
  | watched1 /= 0 =
      validationFailure
        ( "learned clause does not watch its asserting literal first: "
            <> show (watched1, U.toList lits)
        )
        store
  | watched2 /= if U.length lits > 1 then 1 else -1 =
      validationFailure
        ( "learned clause has an invalid second watch: "
            <> show (watched2, U.toList lits)
        )
        store
  | otherwise = Control.do
      (Ur summary, store) <-
        reborrowing store \local -> Control.do
          let valuation = local .# Runtime.valuationField
          (Ur summary, valuation) <-
            validateLearnedLiterals
              currentLevel
              target
              (U.toList lits)
              (LearnedValidation 0 0 IntSet.empty Nothing)
              valuation
          let !(Ur _) = share valuation
          Control.pure (Ur summary)
      let !secondLit =
            if U.length lits > 1
              then Just (U.unsafeIndex lits 1)
              else Nothing
          !orderedRemainder = NonLinear.drop 2 (U.toList lits)
      if
        | validationCurrentLevelCount summary /= 1 ->
            validationFailure
              ( "learned clause is not first-UIP asserting: "
                  <> show
                    ( validationCurrentLevelCount summary
                    , U.toList lits
                    )
              )
              store
        | validationMaximumLowerLevel summary NonLinear./= target ->
            validationFailure
              ( "learned clause target is not the maximum lower level: "
                  <> show
                    ( target
                    , validationMaximumLowerLevel summary
                    , U.toList lits
                    )
              )
              store
        | IntSet.size (validationSeenVariables summary) /= U.length lits ->
            validationFailure
              "learned-clause variable accounting mismatch"
              store
        | secondLit NonLinear./= validationLeastTargetLit summary ->
            validationFailure
              ( "learned clause second watch is not the least target-level literal: "
                  <> show
                    ( secondLit
                    , validationLeastTargetLit summary
                    , U.toList lits
                    )
              )
              store
        | orderedRemainder NonLinear./= List.sort orderedRemainder ->
            validationFailure
              ( "learned clause lower-literal remainder is not ordered: "
                  <> show (U.toList lits)
              )
              store
        | otherwise -> Control.pure store

validateLearnedLiterals ::
  (lifetime >= scope) =>
  DecideLevel ->
  DecideLevel ->
  [Lit] ->
  LearnedValidation ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  BO
    scope
    ( Ur LearnedValidation
    , Mut lifetime (Fixed.UArray Variable)
    )
validateLearnedLiterals _ _ [] summary valuation =
  Control.pure (Ur summary, valuation)
validateLearnedLiterals currentLevel target (literal : rest) summary valuation =
  let !variableIndex = fromVarId (litVar literal)
   in if IntSet.member variableIndex (validationSeenVariables summary)
        then
          validationReadFailure
            ( "learned clause contains a duplicate variable: "
                <> show literal
            )
            valuation
        else Control.do
          (Ur variable, valuation) <-
            Fixed.unsafeCopyAtMut variableIndex valuation
          let !seen =
                IntSet.insert
                  variableIndex
                  (validationSeenVariables summary)
          case variable of
            Indefinite ->
              validationReadFailure
                ( "learned clause contains an unassigned literal "
                    <> "before backtracking: "
                    <> show literal
                )
                valuation
            Definite {decideLevel, value}
              | value NonLinear.== isPositive literal ->
                  validationReadFailure
                    ( "learned clause contains a true literal "
                        <> "before backtracking: "
                        <> show literal
                    )
                    valuation
              | decideLevel NonLinear.== currentLevel ->
                  validateLearnedLiterals
                    currentLevel
                    target
                    rest
                    summary
                      { validationCurrentLevelCount =
                          validationCurrentLevelCount summary + 1
                      , validationSeenVariables = seen
                      }
                    valuation
              | decideLevel NonLinear.< currentLevel ->
                  let !leastTarget =
                        if decideLevel NonLinear./= target
                          then validationLeastTargetLit summary
                          else
                            Just
                              ( NonLinear.maybe
                                  literal
                                  (NonLinear.min literal)
                                  (validationLeastTargetLit summary)
                              )
                   in validateLearnedLiterals
                        currentLevel
                        target
                        rest
                        summary
                          { validationMaximumLowerLevel =
                              NonLinear.max
                                (validationMaximumLowerLevel summary)
                                decideLevel
                          , validationSeenVariables = seen
                          , validationLeastTargetLit = leastTarget
                          }
                        valuation
              | otherwise ->
                  validationReadFailure
                    ( "learned clause literal exceeds the conflict level: "
                        <> show (literal, decideLevel, currentLevel)
                    )
                    valuation

validateAssertingReason ::
  ClauseId ->
  Lit ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO lifetime (Mut lifetime (Runtime.CDCLStore s))
validateAssertingReason reason expected store = Control.do
  (Ur classification, store) <- classifyClause reason store
  case classification of
    ClauseUnit actual
      | actual NonLinear.== expected -> Control.pure store
    _ ->
      validationFailure
        ( "non-asserting reason after backtrack: "
            <> show (reason, expected, classification)
        )
        store

validateRestartedLearnedClause ::
  Lit ->
  ClauseClassification ->
  ()
validateRestartedLearnedClause assertingLit = \case
  ClauseUnit unitLiteral
    | unitLiteral NonLinear.== assertingLit -> ()
    | otherwise ->
        error
          ( "restarted learned clause is unit on the wrong literal: "
              <> show (assertingLit, unitLiteral)
          )
  ClauseOpen -> ()
  ClauseSatisfied ->
    error "restarted learned clause is unexpectedly satisfied"
  ClauseConflict ->
    error "restarted learned clause is unexpectedly conflicting"

validationFailure ::
  String ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  result
validationFailure message store =
  store `lseq` error message

validationReadFailure ::
  String ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  result
validationReadFailure message valuation =
  valuation `lseq` error message
#else
validateConflictClause ::
  ClauseId ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO lifetime (Mut lifetime (Runtime.CDCLStore s))
{-# INLINE validateConflictClause #-}
validateConflictClause clauseId store =
  clauseId `lseq` Control.pure store

validateLearnedAnalysis ::
  DecideLevel ->
  DecideLevel ->
  Clause ->
  Lit ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO lifetime (Mut lifetime (Runtime.CDCLStore s))
{-# INLINE validateLearnedAnalysis #-}
validateLearnedAnalysis _ _ _ _ store =
  Control.pure store

validateAssertingReason ::
  ClauseId ->
  Lit ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO lifetime (Mut lifetime (Runtime.CDCLStore s))
{-# INLINE validateAssertingReason #-}
validateAssertingReason reason literal store =
  reason `lseq` literal `lseq` Control.pure store

validateRestartedLearnedClause ::
  Lit ->
  ClauseClassification ->
  ()
{-# INLINE validateRestartedLearnedClause #-}
validateRestartedLearnedClause _ _ = ()
#endif

scanClause ::
  (lifetime >= scope) =>
  [Lit] ->
  ClauseScan ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  BO
    scope
    ( Ur ClauseScan
    , Mut lifetime (Fixed.UArray Variable)
    )
scanClause [] scan valuation =
  Control.pure (Ur scan, valuation)
scanClause (literal : rest) scan valuation = Control.do
  (Ur variable, valuation) <-
    Fixed.unsafeCopyAtMut
      (fromVarId (litVar literal))
      valuation
  let !updated =
        case variable of
          Indefinite ->
            scan
              { scanUnassignedCount =
                  scanUnassignedCount scan + 1
              , scanUnassignedLit = Just literal
              }
          Definite {value}
            | value == isPositive literal ->
                scan {scanSatisfied = True}
            | otherwise -> scan
  scanClause rest updated valuation
