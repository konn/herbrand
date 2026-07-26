{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}

-- | Conflict-driven clause learning backed by fine-grained Pure Borrow stores.
module Logic.Propositional.Classical.SAT.CDCL (
  solve,
  solveVarId,
  CDCLOptions (..),
  defaultOptions,
  VariableSelection (..),
  defaultAdaptiveFactor,
  RestartStrategy (..),
  defaultRestartStrategy,
  defaultExponentialRestart,
  defaultLubyRestart,
  luby,
  SolverStats (..),
  solveWith,
  solveVarIdWith,
  solveVarIdWithStats,

  -- * Re-exports
  CNF (..),
  CNFClause (..),
  Literal (..),
  VarId (..),
) where

import Control.Functor.Linear qualified as Control
import Control.Functor.Linear.State.Extra qualified as State
import Control.Optics.Linear qualified as LinearOptics
import Data.Bifunctor.Linear qualified as Bifunctor
import Data.Foldable qualified as Foldable
import Data.Functor.Identity (Identity)
import Data.Functor.Linear qualified as Linear
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Hashable (Hashable)
import Data.Unrestricted.Linear (UrT (..), liftUrT, runUrT)
import Data.Unrestricted.Linear qualified as Ur
import Linear.Token.Linearly (besides)
import Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Solver.Internal qualified as PureBorrow
import Logic.Propositional.Classical.SAT.CDCL.Types
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Prelude.Linear
import Prelude qualified as NonLinear

solve :: (HashMap.Keyed variable) => CNF variable -> SatResult (Model variable)
{-# INLINE solve #-}
solve = solveWith defaultOptions

solveWith ::
  (HashMap.Keyed variable) =>
  CDCLOptions ->
  CNF variable ->
  SatResult (Model variable)
{-# INLINE [1] solveWith #-}
{-# ANN solveWith "HLint: ignore Avoid lambda" #-}
solveWith options cnf =
  case solveSparseByPureLiterals cnf of
    Just model -> Satisfiable model
    Nothing ->
      unur $
        HashMap.empty 128 \forward ->
          besides forward (HashMap.emptyL 128)
            & \(reverseMap, forward) ->
              State.runState
                ( runUrT
                    ( NonLinear.traverse
                        (\variable -> liftUrT (renameCNF variable))
                        cnf
                    )
                )
                ((reverseMap, Ur 0), forward)
                & \(Ur renamed, ((forward, Ur _), reverseMap)) ->
                  forward `lseq`
                    case NonLinear.fst
                      ( PureBorrow.solveVarIdWithStats
                          options
                          renamed
                      ) of
                      Unsat ->
                        reverseMap `lseq` Ur Unsat
                      Satisfiable model ->
                        Satisfiable
                          Linear.<$> State.evalState
                            (unrenameModel model)
                            reverseMap

solveSparseByPureLiterals ::
  (Hashable variable) =>
  CNF variable ->
  Maybe (Model variable)
{-# INLINE solveSparseByPureLiterals #-}
solveSparseByPureLiterals (CNF clauses)
  | NonLinear.not (hasWideFirstClause clauses) = Nothing
  | NonLinear.not (hasAtMost 64 clauses) = Nothing
  | otherwise =
      let !clauseCount = NonLinear.length clauses
          !literalCount =
            Foldable.foldl'
              ( \count (CNFClause clause) ->
                  count + NonLinear.length clause
              )
              0
              clauses
       in if literalCount < 8 * clauseCount
            then Nothing
            else eliminate clauses NonLinear.mempty
  where
    hasAtMost :: Int -> [element] -> Bool
    hasAtMost _ [] = True
    hasAtMost 0 _ = False
    hasAtMost count (_ : rest) =
      hasAtMost (count - 1) rest

    hasWideFirstClause [] = True
    hasWideFirstClause (CNFClause clause : _) =
      hasAtLeast 8 clause

    hasAtLeast :: Int -> [element] -> Bool
    hasAtLeast 0 _ = True
    hasAtLeast _ [] = False
    hasAtLeast count (_ : rest) =
      hasAtLeast (count - 1) rest

    eliminate [] model = Just model
    eliminate active model =
      let (!positiveVariables, !negativeVariables) =
            Foldable.foldl'
              collectClause
              (HashSet.empty, HashSet.empty)
              active
          !purePositive =
            positiveVariables
              `HashSet.difference` negativeVariables
          !pureNegative =
            negativeVariables
              `HashSet.difference` positiveVariables
          !pureModel =
            Model
              { positive = purePositive
              , negative = pureNegative
              }
       in if HashSet.null purePositive
            NonLinear.&& HashSet.null pureNegative
            then Nothing
            else
              eliminate
                ( NonLinear.filter
                    ( NonLinear.not
                        NonLinear.. isCovered
                          purePositive
                          pureNegative
                    )
                    active
                )
                (model NonLinear.<> pureModel)

    collectClause
      (!positiveVariables, !negativeVariables)
      (CNFClause clause) =
        Foldable.foldl'
          collectLiteral
          (positiveVariables, negativeVariables)
          clause

    collectLiteral
      (!positiveVariables, !negativeVariables) = \case
        Positive variable ->
          ( HashSet.insert variable positiveVariables
          , negativeVariables
          )
        Negative variable ->
          ( positiveVariables
          , HashSet.insert variable negativeVariables
          )

    isCovered purePositive pureNegative (CNFClause clause) =
      NonLinear.any
        ( \case
            Positive variable ->
              HashSet.member variable purePositive
            Negative variable ->
              HashSet.member variable pureNegative
        )
        clause

unrenameModel ::
  (Hashable variable) =>
  Model VarId ->
  State.State
    (HashMap.HashMap VarId variable)
    (Ur (Model variable))
unrenameModel (Model positiveIds negativeIds) = State.do
  Ur !positive <- unrenameSet positiveIds
  Ur !negative <- unrenameSet negativeIds
  State.pure (Ur Model {..})

unrenameSet ::
  (Hashable variable) =>
  HashSet.HashSet VarId ->
  State.StateT
    (HashMap.HashMap VarId variable)
    Identity
    (Ur (HashSet.HashSet variable))
{-# INLINE unrenameSet #-}
unrenameSet variables =
  Control.fmap (Ur.lift HashSet.fromList) $
    runUrT $
      NonLinear.traverse
        ( \variable ->
            UrT $
              State.state \dictionary ->
                Bifunctor.first
                  ( Linear.fmap
                      ( fromMaybe
                          ( error
                              ( "unrenameModel: variable out of bound: "
                                  <> show variable
                              )
                          )
                      )
                  )
                  (HashMap.lookup variable dictionary)
        )
        (HashSet.toList variables)

renameCNF ::
  (HashMap.Keyed variable) =>
  variable ->
  State.State
    ( (HashMap.HashMap variable VarId, Ur VarId)
    , HashMap.HashMap VarId variable
    )
    VarId
renameCNF variable = State.do
  Ur existing <-
    State.uses
      (LinearOptics._1 LinearOptics..> LinearOptics._1)
      (HashMap.lookup variable)
  case existing of
    Just identifier -> State.pure identifier
    Nothing -> State.do
      Ur identifier <-
        State.uses
          (LinearOptics._1 LinearOptics..> LinearOptics._2)
          ( \(Ur identifier) ->
              (Ur identifier, Ur (identifier NonLinear.+ 1))
          )
      (LinearOptics._1 LinearOptics..> LinearOptics._1)
        State.%= HashMap.insert variable identifier
      LinearOptics._2
        State.%= HashMap.insert identifier variable
      State.pure identifier

{-# RULES "solveWith/VarId" solveWith = solveVarIdWith #-}

solveVarId :: CNF VarId -> SatResult (Model VarId)
{-# INLINE solveVarId #-}
solveVarId = solveVarIdWith defaultOptions

solveVarIdWith ::
  CDCLOptions ->
  CNF VarId ->
  SatResult (Model VarId)
{-# INLINE solveVarIdWith #-}
solveVarIdWith options cnf =
  case solveSparseByPureLiterals cnf of
    Just model -> Satisfiable model
    Nothing ->
      NonLinear.fst
        (PureBorrow.solveVarIdWithStats options cnf)

solveVarIdWithStats ::
  CDCLOptions ->
  CNF VarId ->
  (SatResult (Model VarId), SolverStats)
solveVarIdWithStats options cnf =
  case solveSparseByPureLiterals cnf of
    Just model ->
      (Satisfiable model, zeroSolverStats)
    Nothing ->
      PureBorrow.solveVarIdWithStats options cnf
