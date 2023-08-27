{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Logic.Propositional.Classical.SAT.CDCL.Old.Types (
  isAssignedAfter,
  toCDCLState,
  CDCLState (..),
  Valuation,
  Clauses,
  WatchMap,
  stepsL,
  clausesL,
  watchesL,
  valuationL,
  numInitialClausesL,
  Index,

  -- * Compact literal
  Lit (PosL, NegL),
  litVar,
  _PosL,
  _NegL,
  isPositive,
  isNegative,

  -- * Clause
  Clause (..),

  -- * Variable
  Variable (..),
  litVarL,
  encodeLit,
  decodeLit,
  VarId (..),
  DecideLevel (..),
  Step (..),
  ClauseId (..),
  U.Vector (V_VarId, V_ClauseId, V_Step, V_DecideLevel),
  U.MVector (MV_VarId, MV_ClauseId, MV_Step, MV_DecideLevel),
  UnitResult (..),
  AssignmentState (..),
  PropResult (..),
  WatchVar (..),
  watchVarL,
  numTotalClauses,
) where

import Control.Foldl qualified as Foldl
import Control.Foldl qualified as L
import Control.Optics.Linear qualified as LinLens
import Data.Alloc.Linearly.Token
import Data.Alloc.Linearly.Token.Unsafe (HasLinearWitness)
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as LHM
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.List (mapAccumL)
import Data.Map.Strict qualified as Map
import Data.Strict.Tuple (Pair (..))
import Data.Unrestricted.Linear (Ur (..))
import Data.Unrestricted.Linear.Orphans ()
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Generics.Linear qualified as L
import Generics.Linear.TH (deriveGeneric)
import Logic.Propositional.Classical.SAT.CDCL.Types hiding (
  CDCLState (..),
  clausesL,
  numInitialClausesL,
  numTotalClauses,
  stepsL,
  toCDCLState,
  valuationL,
  watchesL,
 )
import Logic.Propositional.Classical.SAT.Types (SatResult (..))
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Prelude.Linear (lseq, (&))
import Prelude.Linear qualified as PL

data CDCLState where
  CDCLState ::
    -- | Number of original clauses
    {-# UNPACK #-} !Int %1 ->
    -- | Level-wise maximum steps
    {-# UNPACK #-} !(LUV.Vector Step) %1 ->
    -- | Clauses
    {-# UNPACK #-} !Clauses %1 ->
    -- | Watches
    {-# UNPACK #-} !WatchMap %1 ->
    -- | Valuations
    {-# UNPACK #-} !Valuation %1 ->
    CDCLState
  deriving anyclass (HasLinearWitness)

stepsL :: LinLens.Lens' CDCLState (LUV.Vector Step)
{-# INLINE stepsL #-}
stepsL = LinLens.lens \(CDCLState numOrig ss cs ws vs) ->
  (ss, \ss -> CDCLState numOrig ss cs ws vs)

numInitialClausesL :: LinLens.Lens' CDCLState Int
numInitialClausesL = LinLens.lens \(CDCLState numOrig ss cs ws vs) ->
  (numOrig, \numOrig -> CDCLState numOrig ss cs ws vs)

clausesL :: LinLens.Lens' CDCLState (LV.Vector Clause)
{-# INLINE clausesL #-}
clausesL = LinLens.lens \(CDCLState numOrig ss cs ws vs) ->
  (cs, \cs -> CDCLState numOrig ss cs ws vs)

watchesL :: LinLens.Lens' CDCLState WatchMap
{-# INLINE watchesL #-}
watchesL = LinLens.lens \(CDCLState numOrig ss cs ws vs) ->
  (ws, \ws -> CDCLState numOrig ss cs ws vs)

valuationL :: LinLens.Lens CDCLState CDCLState Valuation Valuation
{-# INLINE valuationL #-}
valuationL = LinLens.lens \(CDCLState norig ss cs ws vs) -> (vs, CDCLState norig ss cs ws)

toCDCLState :: CNF VarId -> Linearly %1 -> Either (Ur (SatResult ())) CDCLState
toCDCLState (CNF cls) lin =
  let (cls', truth, contradicting, maxVar) =
        L.fold
          ( (,,,)
              <$> L.handles
                #_CNFClause
                (L.premap (L.fold L.nub . map encodeLit) L.nub)
              <*> Foldl.null
              <*> Foldl.any null
              <*> Foldl.handles Foldl.folded Foldl.maximum
          )
          cls
      (numOrigCls :!: upds, cls'') = mapAccumL buildClause (0 :!: Map.empty) cls'
   in case () of
        _
          | truth -> lin `lseq` Left (Ur $ Satisfiable ())
          | contradicting -> lin `lseq` Left (Ur Unsat)
        _ ->
          besides lin (`LUV.fromListL` [0]) PL.& \(steps, lin) ->
            besides lin (`LV.fromListL` cls'') PL.& \(clauses, lin) ->
              besides lin (`LHM.fromListL` Map.toList upds)
                PL.& \(watcheds, lin) ->
                  Right
                    PL.$ CDCLState numOrigCls steps clauses watcheds
                    PL.$ LUA.allocL lin (maybe 0 ((+ 1) . fromEnum) maxVar) Indefinite

buildClause ::
  Pair Int (Map.Map VarId IntSet) ->
  [Lit] ->
  (Pair Int (Map.Map VarId IntSet), Clause)
buildClause (i :!: watches) [] =
  (i :!: watches, Clause {lits = mempty, satisfiedAt = -1, watched1 = -1, watched2 = -1})
buildClause (i :!: watches) [x] =
  ( (i + 1) :!: Map.insertWith IS.union (litVar x) (IS.singleton i) watches
  , Clause {lits = U.singleton x, satisfiedAt = -1, watched1 = 0, watched2 = -1}
  )
buildClause (i :!: watches) xs =
  ( i
      + 1
      :!: Map.insertWith
        IS.union
        (litVar $ head xs)
        (IS.singleton i)
        ( Map.insertWith
            IS.union
            (litVar $ xs !! 1)
            (IS.singleton i)
            watches
        )
  , Clause {lits = U.fromList xs, satisfiedAt = -1, watched1 = 0, watched2 = 1}
  )

deriveGeneric ''CDCLState

deriving via L.Generically CDCLState instance PL.Consumable CDCLState

deriving via L.Generically CDCLState instance PL.Dupable CDCLState

numTotalClauses :: CDCLState %1 -> (Ur Int, CDCLState)
numTotalClauses (CDCLState numOrig steps clauses watches vals) =
  LV.size clauses & \(sz, clauses) ->
    (sz, CDCLState numOrig steps clauses watches vals)
