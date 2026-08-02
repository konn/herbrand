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
module Logic.Propositional.Classical.SAT.CDCL.Analysis.Internal (
  analyzeConflict,
  Kernel.ConflictAnalysis (..),
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.Record.Linear.Borrow.Experimental.PatternMatch ((.@))
import Data.Ref.Linear.Borrow qualified as RefBorrow
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Logic.Propositional.Classical.SAT.CDCL.Analysis.Kernel.Internal qualified as Kernel
import Logic.Propositional.Classical.SAT.CDCL.Control.Internal qualified as SolverControl
import Logic.Propositional.Classical.SAT.CDCL.Runtime.Internal qualified as Runtime
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
    Boxed.getContents literals & \literalContents -> Control.do
      ( ( Ur result
          , Boxed.PinnedBuffer literalContents
          , Fixed.Pinned valuation
          , Fixed.Pinned trail
          , Fixed.Pinned epoch
          , Fixed.Pinned stamps
          , Fixed.Pinned scratch
          )
        , vsids
        ) <-
        RefBorrow.update
          ( \vsidsState -> Control.do
              ( Ur result
                , updatedVSIDS
                , Kernel.AnalysisPins
                    literalContents
                    valuation
                    trail
                    epoch
                    stamps
                    scratch
                ) <-
                Kernel.analyzeConflict
                  options
                  currentLevel
                  trailLength
                  conflictClause
                  vsidsState
                  ( Kernel.AnalysisPins
                      (Boxed.PinnedBuffer literalContents)
                      (Fixed.Pinned valuation)
                      (Fixed.Pinned trail)
                      (Fixed.Pinned epoch)
                      (Fixed.Pinned stamps)
                      (Fixed.Pinned scratch)
                  )
              Control.pure
                (
                  ( Ur result
                  , literalContents
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
      let !(Ur _) = share literalContents
      let !(Ur _) = share bodies
      let !(Ur _) = share valuation
      let !(Ur _) = share trail
      let !(Ur _) = share epoch
      let !(Ur _) = share stamps
      let !(Ur _) = share scratch
      let !(Ur _) = share vsids
      Control.pure (Ur result)
