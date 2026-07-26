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
Fine-grained Pure Borrow transaction for first-UIP conflict analysis.

Each store is split locally and pinned once for the bulk kernel. VSIDS is the
only replaced scalar root; no aggregate solver state is placed behind a
reference.
-}
module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Analysis.Internal (
  analyzeConflict,
  Kernel.ConflictAnalysis (..),
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.Record.Linear.Borrow.Experimental.PatternMatch ((.@))
import Data.Ref.Linear.Borrow qualified as RefBorrow
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Unboxed qualified as U
import Data.Word (Word64)
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Analysis.Kernel.Internal qualified as Kernel
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Control.Internal qualified as SolverControl
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Runtime.Internal qualified as Runtime
import Logic.Propositional.Classical.SAT.CDCL.Types
import Prelude.Linear

analyzeConflict ::
  CDCLOptions ->
  DecideLevel ->
  Int ->
  ClauseId ->
  SolverControl.SolverControl %1 ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO
    lifetime
    ( Ur Kernel.ConflictAnalysis
    , SolverControl.SolverControl
    , Mut lifetime (Runtime.CDCLStore s)
    )
{-# INLINE analyzeConflict #-}
analyzeConflict options currentLevel trailLength conflictClause control store =
  Control.do
    (Ur result, store) <-
      reborrowing store \local ->
        analyzeTransaction
          options
          currentLevel
          trailLength
          conflictClause
          local
    let !updatedControl =
          SolverControl.modifyStats
            (Kernel.applyAnalysisStats result)
            control
    Control.pure (Ur result, updatedControl, store)

analyzeTransaction ::
  CDCLOptions ->
  DecideLevel ->
  Int ->
  ClauseId ->
  Mut lifetime (Runtime.CDCLStore s) %1 ->
  BO lifetime (Ur Kernel.ConflictAnalysis)
analyzeTransaction options currentLevel trailLength conflictClause local =
  Control.do
    let %1 !(clauses, valuation, trail, workspace, vsids) =
          local
            .@ ( Runtime.clausesField
               , Runtime.valuationField
               , Runtime.trailField
               , Runtime.analysisField
               , Runtime.vsidsField
               )
    let %1 !(literals, bodies) =
          clauses
            .@ ( Runtime.clauseLiteralsField
               , Runtime.clauseBodiesField
               )
    let %1 !(epoch, stamps, scratch) =
          workspace
            .@ ( Runtime.analysisEpochField
               , Runtime.analysisStampsField
               , Runtime.analysisLiteralsField
               )
    ( ( Ur result
        , literals
        , valuation
        , trail
        , epoch
        , stamps
        , scratch
        )
      , vsids
      ) <-
      RefBorrow.update
        ( \vsidsState -> Control.do
            ( (Ur result, updatedVSIDS)
              , (literals, valuation, trail, epoch, stamps, scratch)
              ) <-
              withPinnedAnalysisStores
                ( \literalsPinned valuationPinned trailPinned epochPinned stampsPinned scratchPinned -> Control.do
                    ( Ur result
                      , updatedVSIDS
                      , Kernel.AnalysisPins
                          literalsPinned
                          valuationPinned
                          trailPinned
                          epochPinned
                          stampsPinned
                          scratchPinned
                      ) <-
                      Kernel.analyzeConflict
                        options
                        currentLevel
                        trailLength
                        conflictClause
                        vsidsState
                        ( Kernel.AnalysisPins
                            literalsPinned
                            valuationPinned
                            trailPinned
                            epochPinned
                            stampsPinned
                            scratchPinned
                        )
                    Control.pure
                      ( (Ur result, updatedVSIDS)
                      ,
                        ( literalsPinned
                        , valuationPinned
                        , trailPinned
                        , epochPinned
                        , stampsPinned
                        , scratchPinned
                        )
                      )
                )
                literals
                valuation
                trail
                epoch
                stamps
                scratch
            Control.pure
              (
                ( Ur result
                , literals
                , valuation
                , trail
                , epoch
                , stamps
                , scratch
                )
              , updatedVSIDS
              )
        )
        vsids
    let !(Ur _) = share literals
    let !(Ur _) = share bodies
    let !(Ur _) = share valuation
    let !(Ur _) = share trail
    let !(Ur _) = share epoch
    let !(Ur _) = share stamps
    let !(Ur _) = share scratch
    let !(Ur _) = share vsids
    Control.pure (Ur result)

withPinnedAnalysisStores ::
  (lifetime >= scope) =>
  ( forall literalsPin valuationPin trailPin epochPin stampsPin scratchPin.
    Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit)) %1 ->
    Fixed.Pinned valuationPin Variable %1 ->
    Fixed.Pinned trailPin Lit %1 ->
    Fixed.Pinned epochPin Word64 %1 ->
    Fixed.Pinned stampsPin Word64 %1 ->
    Fixed.Pinned scratchPin Lit %1 ->
    BO
      scope
      ( result
      , ( Boxed.PinnedBuffer literalsPin (Ur (U.Vector Lit))
        , Fixed.Pinned valuationPin Variable
        , Fixed.Pinned trailPin Lit
        , Fixed.Pinned epochPin Word64
        , Fixed.Pinned stampsPin Word64
        , Fixed.Pinned scratchPin Lit
        )
      )
  ) %1 ->
  Mut lifetime (Boxed.Vector (Ur (U.Vector Lit))) %1 ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  Mut lifetime (Fixed.UArray Word64) %1 ->
  Mut lifetime (Fixed.UArray Word64) %1 ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  BO
    scope
    ( result
    , ( Mut lifetime (Boxed.Vector (Ur (U.Vector Lit)))
      , Mut lifetime (Fixed.UArray Variable)
      , Mut lifetime (Fixed.UArray Lit)
      , Mut lifetime (Fixed.UArray Word64)
      , Mut lifetime (Fixed.UArray Word64)
      , Mut lifetime (Fixed.UArray Lit)
      )
    )
{-# INLINE withPinnedAnalysisStores #-}
withPinnedAnalysisStores action literals valuation trail epoch stamps scratch =
  Control.do
    ((result, valuation, trail, epoch, stamps, scratch), literals) <-
      Boxed.withPinnedBuffer
        ( \_ literalsPinned -> Control.do
            ( ( result
                , literalsPinned
                )
              , (valuation, trail, epoch, stamps, scratch)
              ) <-
              withPinnedFixedStores
                ( \valuationPinned trailPinned epochPinned stampsPinned scratchPinned -> Control.do
                    ( result
                      , ( literalsPinned
                          , valuationPinned
                          , trailPinned
                          , epochPinned
                          , stampsPinned
                          , scratchPinned
                          )
                      ) <-
                      action
                        literalsPinned
                        valuationPinned
                        trailPinned
                        epochPinned
                        stampsPinned
                        scratchPinned
                    Control.pure
                      ( (result, literalsPinned)
                      ,
                        ( valuationPinned
                        , trailPinned
                        , epochPinned
                        , stampsPinned
                        , scratchPinned
                        )
                      )
                )
                valuation
                trail
                epoch
                stamps
                scratch
            Control.pure
              ( (result, valuation, trail, epoch, stamps, scratch)
              , literalsPinned
              )
        )
        literals
    Control.pure
      (result, (literals, valuation, trail, epoch, stamps, scratch))

withPinnedFixedStores ::
  (lifetime >= scope) =>
  ( forall valuationPin trailPin epochPin stampsPin scratchPin.
    Fixed.Pinned valuationPin Variable %1 ->
    Fixed.Pinned trailPin Lit %1 ->
    Fixed.Pinned epochPin Word64 %1 ->
    Fixed.Pinned stampsPin Word64 %1 ->
    Fixed.Pinned scratchPin Lit %1 ->
    BO
      scope
      ( result
      , ( Fixed.Pinned valuationPin Variable
        , Fixed.Pinned trailPin Lit
        , Fixed.Pinned epochPin Word64
        , Fixed.Pinned stampsPin Word64
        , Fixed.Pinned scratchPin Lit
        )
      )
  ) %1 ->
  Mut lifetime (Fixed.UArray Variable) %1 ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  Mut lifetime (Fixed.UArray Word64) %1 ->
  Mut lifetime (Fixed.UArray Word64) %1 ->
  Mut lifetime (Fixed.UArray Lit) %1 ->
  BO
    scope
    ( result
    , ( Mut lifetime (Fixed.UArray Variable)
      , Mut lifetime (Fixed.UArray Lit)
      , Mut lifetime (Fixed.UArray Word64)
      , Mut lifetime (Fixed.UArray Word64)
      , Mut lifetime (Fixed.UArray Lit)
      )
    )
{-# INLINE withPinnedFixedStores #-}
withPinnedFixedStores action valuation trail epoch stamps scratch = Control.do
  ((result, trail, epoch, stamps, scratch), valuation) <-
    Fixed.withPinned
      ( \valuationPinned -> Control.do
          ((result, valuationPinned, epoch, stamps, scratch), trail) <-
            Fixed.withPinned
              ( \trailPinned -> Control.do
                  ((result, valuationPinned, trailPinned, stamps, scratch), epoch) <-
                    Fixed.withPinned
                      ( \epochPinned -> Control.do
                          ((result, valuationPinned, trailPinned, epochPinned, scratch), stamps) <-
                            Fixed.withPinned
                              ( \stampsPinned -> Control.do
                                  ((result, valuationPinned, trailPinned, epochPinned, stampsPinned), scratch) <-
                                    Fixed.withPinned
                                      ( \scratchPinned -> Control.do
                                          ( result
                                            , ( valuationPinned
                                                , trailPinned
                                                , epochPinned
                                                , stampsPinned
                                                , scratchPinned
                                                )
                                            ) <-
                                            action
                                              valuationPinned
                                              trailPinned
                                              epochPinned
                                              stampsPinned
                                              scratchPinned
                                          Control.pure
                                            (
                                              ( result
                                              , valuationPinned
                                              , trailPinned
                                              , epochPinned
                                              , stampsPinned
                                              )
                                            , scratchPinned
                                            )
                                      )
                                      scratch
                                  Control.pure
                                    (
                                      ( result
                                      , valuationPinned
                                      , trailPinned
                                      , epochPinned
                                      , scratch
                                      )
                                    , stampsPinned
                                    )
                              )
                              stamps
                          Control.pure
                            (
                              ( result
                              , valuationPinned
                              , trailPinned
                              , stamps
                              , scratch
                              )
                            , epochPinned
                            )
                      )
                      epoch
                  Control.pure
                    (
                      ( result
                      , valuationPinned
                      , epoch
                      , stamps
                      , scratch
                      )
                    , trailPinned
                    )
              )
              trail
          Control.pure
            (
              ( result
              , trail
              , epoch
              , stamps
              , scratch
              )
            , valuationPinned
            )
      )
      valuation
  Control.pure (result, (valuation, trail, epoch, stamps, scratch))
