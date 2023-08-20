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
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Logic.Propositional.Classical.SAT.CDCL.Types (
  withCDCLState,
  toCDCLState,
  CDCLState (..),
  Valuation,
  Clauses,
  WatchMap,
  stepsL,
  clausesL,
  watchMapL,
  variablesL,
  Index,
  backtrack,

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
  numClauses,
) where

import Control.DeepSeq (NFData)
import Control.Foldl qualified as Foldl
import Control.Foldl qualified as L
import Control.Lens (Lens', Prism', imapAccumL, lens, prism')
import Control.Monad (guard)
import Control.Optics.Linear qualified as LinLens
import Data.Alloc.Linearly.Token
import Data.Alloc.Linearly.Token.Unsafe (HasLinearWitness)
import Data.Bit (Bit (..))
import Data.Bits ((.&.), (.|.))
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as LHM
import Data.Hashable (Hashable)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.Map.Strict qualified as Map
import Data.Strict.Tuple (Pair)
import Data.Strict.Tuple qualified as S
import Data.Unrestricted.Linear (Ur)
import Data.Unrestricted.Linear qualified as L
import Data.Unrestricted.Linear.Orphans ()
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import GHC.Generics (Generic)
import Generics.Linear qualified as L
import Generics.Linear.TH (deriveGeneric)
import Logic.Propositional.Classical.SAT.Types (SatResult (..))
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Prelude.Linear (lseq, (&))
import Prelude.Linear qualified as L
import Prelude.Linear qualified as PL

newtype VarId = VarId {unVarId :: Word}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, PL.Consumable, PL.Dupable, PL.Movable)

derivingUnbox "VarId" [t|VarId -> Word|] [|unVarId|] [|VarId|]

newtype ClauseId = ClauseId {unClauseId :: Word}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, PL.Consumable, PL.Dupable, PL.Movable)

derivingUnbox "ClauseId" [t|ClauseId -> Word|] [|unClauseId|] [|ClauseId|]

newtype DecideLevel = DecideLevel {unDecideLevel :: Word}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, Integral, Real, PL.Consumable, PL.Dupable, PL.Movable)

derivingUnbox "DecideLevel" [t|DecideLevel -> Word|] [|unDecideLevel|] [|DecideLevel|]

newtype Step = Step {unStep :: Word}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, Integral, Real, PL.Consumable, PL.Dupable, PL.Movable)

derivingUnbox "Step" [t|Step -> Word|] [|unStep|] [|Step|]

-- | Up to 32-bit
newtype Lit = Lit {runLit :: Word}
  deriving (Eq, Ord)
  deriving newtype (Hashable, NFData, PL.Consumable, PL.Dupable, PL.Movable)

{-# COMPLETE PosL, NegL :: Lit #-}

pattern PosL :: VarId -> Lit
pattern PosL w <- (decodeLit -> Positive w)
  where
    PosL (VarId w) = Lit (w .&. idMask)

pattern NegL :: VarId -> Lit
pattern NegL w <- (decodeLit -> Negative w)
  where
    NegL (VarId w) = Lit (negateMask .|. (w .&. idMask))

_PosL :: Prism' Lit VarId
_PosL = prism' PosL \(Lit l) -> do
  guard $ l .&. negateMask == 0
  pure $ VarId $ l .&. idMask

_NegL :: Prism' Lit VarId
_NegL = prism' NegL \(Lit l) -> do
  guard $ l .&. negateMask /= 0
  pure $ VarId $ l .&. idMask

litVar :: Lit -> VarId
{-# INLINE litVar #-}
litVar = VarId . (.&. idMask) . runLit

litVarL :: Lens' Lit VarId
{-# INLINE litVarL #-}
litVarL = lens litVar \l (VarId v) -> Lit (negateMask .&. runLit l .|. idMask .&. v)

instance Show Lit where
  showsPrec d = showsPrec d . decodeLit
  {-# INLINE showsPrec #-}

negateMask :: Word
negateMask = 0x8000000000000000

idMask :: Word
idMask = 0x7fffffffffffffff

encodeLit :: Literal VarId -> Lit
encodeLit (Positive (VarId w)) = Lit $ w .&. idMask
encodeLit (Negative (VarId w)) = Lit $ negateMask .|. (w .&. idMask)

decodeLit :: Lit -> Literal VarId
decodeLit (Lit w)
  | w .&. negateMask /= 0 = Negative $ VarId $ w .&. idMask
  | otherwise = Positive $ VarId $ w .&. idMask

derivingUnbox "Lit" [t|Lit -> Word|] [|runLit|] [|Lit|]

type Index = Int

data Variable = Variable
  { value :: !Bool
  , introduced :: {-# UNPACK #-} !(Pair DecideLevel Step)
  , antecedent :: {-# UNPACK #-} !ClauseId
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

data Clause = Clause
  { lits :: {-# UNPACK #-} !(U.Vector Lit)
  , watched1 :: {-# UNPACK #-} !Index
  , watched2 :: {-# UNPACK #-} !Index
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

type Valuation = LHM.HashMap VarId Variable

type WatchMap = LHM.HashMap VarId IntSet

type Clauses = LV.Vector Clause

data CDCLState where
  CDCLState ::
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
stepsL = LinLens.lens \(CDCLState ss cs ws vs) ->
  (ss, \ss -> CDCLState ss cs ws vs)

clausesL :: LinLens.Lens' CDCLState (LV.Vector Clause)
{-# INLINE clausesL #-}
clausesL = LinLens.lens \(CDCLState ss cs ws vs) ->
  (cs, \cs -> CDCLState ss cs ws vs)

watchMapL :: LinLens.Lens' CDCLState WatchMap
{-# INLINE watchMapL #-}
watchMapL = LinLens.lens \(CDCLState ss cs ws vs) ->
  (ws, \ws -> CDCLState ss cs ws vs)

variablesL :: LinLens.Lens' CDCLState Valuation
{-# INLINE variablesL #-}
variablesL = LinLens.lens \(CDCLState ss cs ws vs) -> (vs, CDCLState ss cs ws)

backtrack :: DecideLevel -> Clause -> CDCLState %1 -> CDCLState
{-# INLINE backtrack #-}
backtrack decLvl learnt =
  LinLens.over stepsL (LUV.slice 0 (fromIntegral (unDecideLevel decLvl) + 1))
    L.. LinLens.over clausesL (LV.push learnt)
    L.. LinLens.over variablesL (LHM.filter ((<= decLvl) . S.fst . introduced))

toCDCLState :: Linearly %1 -> CNF VarId -> Either (SatResult ()) CDCLState
toCDCLState lin (CNF cls) =
  let (cls', truth, contradicting) =
        L.fold
          ( (,,)
              <$> L.handles
                #_CNFClause
                (L.premap (L.fold L.nub . map encodeLit) L.nub)
              <*> Foldl.null
              <*> Foldl.any null
          )
          cls
      (upds, cls'') = imapAccumL buildClause Map.empty cls'
   in case () of
        _
          | truth -> lin `lseq` Left (Satisfiable ())
          | contradicting -> lin `lseq` Left Unsat
        _ ->
          besides lin (`LUV.fromListL` [0]) PL.& \(steps, lin) ->
            besides lin (`LV.fromListL` cls'') PL.& \(clauses, lin) ->
              besides lin (`LHM.fromListL` Map.toList upds)
                PL.& \(watcheds, lin) ->
                  Right
                    PL.$ CDCLState steps clauses watcheds
                    PL.$ LHM.emptyL lin (Map.size upds)

withCDCLState :: CNF VarId -> Either (SatResult ()) ((CDCLState %1 -> Ur a) %1 -> Ur a)
withCDCLState (CNF cls) =
  let (cls', truth, contradicting) =
        L.fold
          ( (,,)
              <$> L.handles
                #_CNFClause
                (L.premap (L.fold L.nub . map encodeLit) L.nub)
              <*> Foldl.null
              <*> Foldl.any null
          )
          cls
   in if
        | truth -> Left $ Satisfiable ()
        | contradicting -> Left Unsat
        | otherwise ->
            Right
              $ let (upds, cls'') = imapAccumL buildClause Map.empty cls'
                 in \k -> LUV.fromList [0] \steps -> LV.fromList cls'' \clauses ->
                      LHM.fromList (Map.toList upds) \watcheds ->
                        LHM.empty (Map.size upds) (k PL.. CDCLState steps clauses watcheds)

buildClause ::
  Int ->
  Map.Map VarId IntSet ->
  [Lit] ->
  (Map.Map VarId IntSet, Clause)
buildClause _ watches [] =
  (watches, Clause {lits = mempty, watched1 = -1, watched2 = -1})
buildClause i watches [x] =
  ( Map.insertWith IS.union (litVar x) (IS.singleton i) watches
  , Clause {lits = U.singleton x, watched1 = 0, watched2 = -1}
  )
buildClause i watches xs =
  ( Map.insertWith IS.union (litVar $ head xs) (IS.singleton i)
      $ Map.insertWith
        IS.union
        (litVar $ xs !! 1)
        (IS.singleton i)
        watches
  , Clause {lits = U.fromList xs, watched1 = 0, watched2 = 1}
  )

deriveGeneric ''CDCLState

deriving via L.Generically CDCLState instance PL.Consumable CDCLState

deriving via L.Generically CDCLState instance PL.Dupable CDCLState

data WatchVar = W1 | W2 deriving (Show, Eq, Ord, Generic)

deriveGeneric ''WatchVar

deriving via L.AsMovable WatchVar instance PL.Consumable WatchVar

deriving via L.AsMovable WatchVar instance PL.Dupable WatchVar

deriving via L.Generically WatchVar instance PL.Movable WatchVar

data UnitResult
  = Unit {-# UNPACK #-} !Lit
  | Conflict !(Maybe Lit)
  | -- | Optional 'Pair' records possible old watched variable and new variable.
    Satisfied !(Maybe (Pair (Pair WatchVar VarId) (Pair VarId Index)))
  | WatchChangedFromTo !WatchVar {-# UNPACK #-} !VarId {-# UNPACK #-} !VarId {-# UNPACK #-} !Index
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''UnitResult

deriving via L.AsMovable UnitResult instance PL.Consumable UnitResult

deriving via L.AsMovable UnitResult instance PL.Dupable UnitResult

deriving via L.Generically UnitResult instance PL.Movable UnitResult

deriveGeneric ''Variable

deriving via L.AsMovable Variable instance PL.Consumable Variable

deriving via L.AsMovable Variable instance PL.Dupable Variable

deriving via L.Generically Variable instance PL.Movable Variable

derivingUnbox
  "Variable"
  [t|Variable -> (Bit, DecideLevel, Step, ClauseId)|]
  [|\Variable {..} -> (Bit value, S.fst introduced, S.snd introduced, antecedent)|]
  [|\(Bit value, d, s, antecedent) -> Variable {introduced = d S.:!: s, ..}|]

isNegative :: Lit -> Bool
isNegative (Lit w) = w .&. negateMask /= 0

isPositive :: Lit -> Bool
isPositive (Lit w) = w .&. negateMask == 0

data AssignmentState = Unassigned | AssignedTrue
  deriving (Show, Eq, Ord, Generic)

derivingUnbox
  "AssignmentState"
  [t|AssignmentState -> Bit|]
  [|\case AssignedTrue -> Bit True; Unassigned -> Bit False|]
  [|\case Bit True -> AssignedTrue; Bit False -> Unassigned|]
deriveGeneric ''AssignmentState

deriving via L.AsMovable AssignmentState instance L.Consumable AssignmentState

deriving via L.AsMovable AssignmentState instance L.Dupable AssignmentState

deriving via L.Generically AssignmentState instance L.Movable AssignmentState

data PropResult
  = ConflictFound {-# UNPACK #-} !ClauseId !(Maybe Lit)
  | NoMorePropagation
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''PropResult

deriving via L.AsMovable PropResult instance L.Consumable PropResult

deriving via L.AsMovable PropResult instance L.Dupable PropResult

deriving via L.Generically PropResult instance L.Movable PropResult

watchVarL :: WatchVar -> Lens' Clause Index
watchVarL W1 = #watched1
watchVarL W2 = #watched1

numClauses :: CDCLState %1 -> (Ur Int, CDCLState)
numClauses (CDCLState steps clauses watches vals) =
  LV.size clauses & \(sz, clauses) ->
    (sz, CDCLState steps clauses watches vals)
