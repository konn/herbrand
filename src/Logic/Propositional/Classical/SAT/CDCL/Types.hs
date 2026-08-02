{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
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

module Logic.Propositional.Classical.SAT.CDCL.Types (
  CDCLOptions (..),
  defaultOptions,
  VariableSelection (..),
  defaultAdaptiveFactor,
  RestartStrategy (..),
  defaultRestartStrategy,
  defaultExponentialRestart,
  defaultLubyRestart,
  luby,
  AssertionResult (..),
  litBucketIndex,
  watchOccurrence,
  watchOccurrenceClause,
  watchOccurrenceSlot,
  moveToSatQueue,
  moveToUnsatQueue,
  VarQueue,
  VSIDSState (..),
  Index,

  -- * Compact literal
  Lit (PosL, NegL),
  litVar,
  negL,
  isPositive,

  -- * Clause
  Clause (..),
  ClauseBody (..),

  -- * Variable
  Variable (..),
  encodeLit,
  decodeLit,
  VarId (..),
  fromVarId,
  DecideLevel (..),
  Step (..),
  ClauseId (..),
  U.Vector (V_VarId, V_ClauseId, V_Step, V_DecideLevel),
  U.MVector (MV_VarId, MV_ClauseId, MV_Step, MV_DecideLevel),
  PropResult (..),
  WatchVar (..),
  RestartResult (..),
  SolverStats (..),
  zeroSolverStats,
  initialAnalysisEpoch,
  initialAnalysisStamp,
) where

import Control.DeepSeq (NFData)
import Control.Monad.Borrow.Pure.Copyable (Copyable)
import Data.Bit (Bit (..))
import Data.Bits (popCount, xor, (.&.), (.|.))
import Data.Coerce (coerce)
import Data.Hashable (Hashable)
import Data.IntPSQ qualified as PSQ
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Unrestricted.Linear qualified as L
import Data.Unrestricted.Linear.Orphans ()
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as MG
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Generics.Linear qualified as L
import Generics.Linear.TH (deriveGeneric)
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Math.NumberTheory.Logarithms (wordLog2')
import Prelude.Linear qualified as PL

data SolverStats = SolverStats
  { seedScanCount :: {-# UNPACK #-} !Int
  , postDrainScanCount :: {-# UNPACK #-} !Int
  , assignmentCount :: {-# UNPACK #-} !Int
  , trailAppendCount :: {-# UNPACK #-} !Int
  , duplicateEnqueueCount :: {-# UNPACK #-} !Int
  , propagationEventCount :: {-# UNPACK #-} !Int
  , watchVisitCount :: {-# UNPACK #-} !Int
  , watchMoveCount :: {-# UNPACK #-} !Int
  , literalInspectionCount :: {-# UNPACK #-} !Int
  , decisionCount :: {-# UNPACK #-} !Int
  , conflictCount :: {-# UNPACK #-} !Int
  , backtrackCallCount :: {-# UNPACK #-} !Int
  , backtrackBoundaryReadCount :: {-# UNPACK #-} !Int
  , backtrackTrailReadCount :: {-# UNPACK #-} !Int
  , backtrackClearedCount :: {-# UNPACK #-} !Int
  , backtrackValuationReadCount :: {-# UNPACK #-} !Int
  , backtrackValuationWriteCount :: {-# UNPACK #-} !Int
  , backtrackQueueRestoreCount :: {-# UNPACK #-} !Int
  , backtrackBoundaryProbeCount :: {-# UNPACK #-} !Int
  , backtrackNoOpCount :: {-# UNPACK #-} !Int
  , backtrackMaxSuffix :: {-# UNPACK #-} !Int
  , ordinaryBacktrackCount :: {-# UNPACK #-} !Int
  , restartBacktrackCount :: {-# UNPACK #-} !Int
  , observedRestartCount :: {-# UNPACK #-} !Int
  , analysisCount :: {-# UNPACK #-} !Int
  , analysisRootConflictCount :: {-# UNPACK #-} !Int
  , analysisConflictClauseVisitCount :: {-# UNPACK #-} !Int
  , analysisReasonClauseVisitCount :: {-# UNPACK #-} !Int
  , analysisConflictLiteralVisitCount :: {-# UNPACK #-} !Int
  , analysisReasonLiteralVisitCount :: {-# UNPACK #-} !Int
  , analysisTrailReadCount :: {-# UNPACK #-} !Int
  , analysisPivotCount :: {-# UNPACK #-} !Int
  , analysisMarkCount :: {-# UNPACK #-} !Int
  , analysisDuplicateMarkCount :: {-# UNPACK #-} !Int
  , analysisLearnedLiteralCount :: {-# UNPACK #-} !Int
  , analysisEpochClearCount :: {-# UNPACK #-} !Int
  , analysisSortComparisonCount :: {-# UNPACK #-} !Int
  , analysisSortSwapCount :: {-# UNPACK #-} !Int
  , analysisLastTargetLevel :: {-# UNPACK #-} !Int
  , analysisLastPivotTrace :: ![Literal Word]
  , analysisLastLearnedClause :: ![Literal Word]
  , analysisLearnedTrace :: ![([Literal Word], Int, [Literal Word])]
  }
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''SolverStats

deriving via L.AsMovable SolverStats instance PL.Consumable SolverStats

deriving via L.AsMovable SolverStats instance PL.Dupable SolverStats

deriving via L.Generically SolverStats instance PL.Movable SolverStats

zeroSolverStats :: SolverStats
zeroSolverStats =
  SolverStats
    { seedScanCount = 0
    , postDrainScanCount = 0
    , assignmentCount = 0
    , trailAppendCount = 0
    , duplicateEnqueueCount = 0
    , propagationEventCount = 0
    , watchVisitCount = 0
    , watchMoveCount = 0
    , literalInspectionCount = 0
    , decisionCount = 0
    , conflictCount = 0
    , backtrackCallCount = 0
    , backtrackBoundaryReadCount = 0
    , backtrackTrailReadCount = 0
    , backtrackClearedCount = 0
    , backtrackValuationReadCount = 0
    , backtrackValuationWriteCount = 0
    , backtrackQueueRestoreCount = 0
    , backtrackBoundaryProbeCount = 0
    , backtrackNoOpCount = 0
    , backtrackMaxSuffix = 0
    , ordinaryBacktrackCount = 0
    , restartBacktrackCount = 0
    , observedRestartCount = 0
    , analysisCount = 0
    , analysisRootConflictCount = 0
    , analysisConflictClauseVisitCount = 0
    , analysisReasonClauseVisitCount = 0
    , analysisConflictLiteralVisitCount = 0
    , analysisReasonLiteralVisitCount = 0
    , analysisTrailReadCount = 0
    , analysisPivotCount = 0
    , analysisMarkCount = 0
    , analysisDuplicateMarkCount = 0
    , analysisLearnedLiteralCount = 0
    , analysisEpochClearCount = 0
    , analysisSortComparisonCount = 0
    , analysisSortSwapCount = 0
    , analysisLastTargetLevel = -1
    , analysisLastPivotTrace = []
    , analysisLastLearnedClause = []
    , analysisLearnedTrace = []
    }

initialAnalysisEpoch, initialAnalysisStamp :: Word64
#ifdef HERBRAND_CDCL_INSTRUMENTED
initialAnalysisEpoch = maxBound
initialAnalysisStamp = 1
#else
initialAnalysisEpoch = 0
initialAnalysisStamp = 0
#endif

data RestartResult = Continued | Restarted
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''RestartResult

deriving via L.AsMovable RestartResult instance PL.Consumable RestartResult

deriving via L.AsMovable RestartResult instance PL.Dupable RestartResult

deriving via L.Generically RestartResult instance PL.Movable RestartResult

defaultDecayFactor :: VariableSelection
defaultDecayFactor = 0.95

defaultAdaptiveFactor :: VariableSelection
defaultAdaptiveFactor =
  Adaptive
    { lowLBDDecay = 0.85
    , highLBDDecay = 0.99
    , lbdEmaDecayFactor = 0.95
    }

data VariableSelection
  = ConstantFactor {-# UNPACK #-} !Double
  | Adaptive
      { lowLBDDecay :: {-# UNPACK #-} !Double
      , highLBDDecay :: {-# UNPACK #-} !Double
      , lbdEmaDecayFactor :: {-# UNPACK #-} !Double
      }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

instance Num VariableSelection where
  fromInteger = ConstantFactor . fromInteger
  (+) = error "VariableSelection: (+) not implemented"
  (-) = error "VariableSelection: (-) not implemented"
  (*) = error "VariableSelection: (*) not implemented"
  signum = error "VariableSelection: signum not implemented"
  abs = error "VariableSelection: abs not implemented"

instance Fractional VariableSelection where
  fromRational = ConstantFactor . fromRational
  (/) = error "VariableSelection: (/) not implemented"
  recip = error "VariableSelection: recip not implemented"

data RestartStrategy
  = NoRestart
  | ExponentialRestart
      { initialRestart :: !Word
      , increaseFactor :: !Word
      }
  | LubyRestart {initialRestart :: !Word}
  deriving (Show, Eq, Ord, Generic)

luby :: Word -> Word
luby = go
  where
    go 0 = 1
    go 1 = 1
    go !i =
      let !k = wordLog2' (i + 1)
       in if popCount (i + 2) == 1
            then 2 ^ k
            else go (i - 2 ^ k + 1)

defaultRestartStrategy :: RestartStrategy
defaultRestartStrategy = defaultLubyRestart

defaultExponentialRestart :: RestartStrategy
defaultExponentialRestart =
  ExponentialRestart
    { initialRestart = 100
    , increaseFactor = 2
    }

defaultLubyRestart :: RestartStrategy
defaultLubyRestart =
  LubyRestart
    { initialRestart = 100
    }

data CDCLOptions = CDCLOptions
  { decayFactor :: !VariableSelection
  , activateResolved :: !Bool
  , restartStrategy :: !RestartStrategy
  }
  deriving (Show, Eq, Ord, Generic)

defaultOptions :: CDCLOptions
defaultOptions =
  CDCLOptions
    { decayFactor = defaultDecayFactor
    , activateResolved = True
    , restartStrategy = NoRestart
    }

newtype VarId = VarId {unVarId :: Word}
  deriving (Eq, Ord, Generic)
  deriving newtype (Show, NFData, Hashable, Num, Enum, PL.Consumable, PL.Dupable, PL.Movable)

deriveGeneric ''VarId

deriving via L.Generically VarId instance Copyable VarId

fromVarId :: VarId -> Int
fromVarId = fromIntegral . unVarId

derivingUnbox "VarId" [t|VarId -> Word|] [|unVarId|] [|VarId|]

newtype ClauseId = ClauseId {unClauseId :: Int}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, PL.Consumable, PL.Dupable, PL.Movable)

deriveGeneric ''ClauseId

deriving via L.Generically ClauseId instance Copyable ClauseId

derivingUnbox "ClauseId" [t|ClauseId -> Int|] [|unClauseId|] [|ClauseId|]

newtype DecideLevel = DecideLevel {unDecideLevel :: Int}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, Integral, Real, PL.Consumable, PL.Dupable, PL.Movable)

deriveGeneric ''DecideLevel

deriving via L.Generically DecideLevel instance Copyable DecideLevel

derivingUnbox "DecideLevel" [t|DecideLevel -> Int|] [|unDecideLevel|] [|DecideLevel|]

newtype Step = Step {unStep :: Word}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, Integral, Real, PL.Consumable, PL.Dupable, PL.Movable)

deriveGeneric ''Step

deriving via L.Generically Step instance Copyable Step

derivingUnbox "Step" [t|Step -> Word|] [|unStep|] [|Step|]

-- | Up to 32-bit
newtype Lit = Lit {runLit :: Word}
  deriving (Eq, Ord, Generic)
  deriving newtype (Hashable, NFData, PL.Consumable, PL.Dupable, PL.Movable)

deriveGeneric ''Lit

deriving via L.Generically Lit instance Copyable Lit

{-# COMPLETE PosL, NegL :: Lit #-}

pattern PosL :: VarId -> Lit
pattern PosL w <- (decodeLit -> Positive w)
  where
    PosL (VarId w) = Lit (w .&. idMask)

pattern NegL :: VarId -> Lit
pattern NegL w <- (decodeLit -> Negative w)
  where
    NegL (VarId w) = Lit (negateMask .|. (w .&. idMask))

litVar :: Lit -> VarId
{-# INLINE litVar #-}
litVar = VarId . (.&. idMask) . runLit

negL :: Lit -> Lit
negL = coerce $ xor negateMask

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

data Variable
  = Definite
      { decideLevel :: {-# UNPACK #-} !DecideLevel
      , decisionStep :: {-# UNPACK #-} !Step
      , antecedent :: !(Maybe ClauseId)
      , value :: !Bool
      }
  | Indefinite
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

deriveGeneric ''Variable

deriving via L.AsMovable Variable instance PL.Consumable Variable

deriving via L.AsMovable Variable instance PL.Dupable Variable

deriving via L.Generically Variable instance PL.Movable Variable

deriving via L.Generically Variable instance Copyable Variable

derivingUnbox
  "Variable"
  [t|Variable -> (DecideLevel, Step, ClauseId, Bit)|]
  [|
    \case
      Indefinite -> (-1, -1, -1, Bit False)
      Definite {..} -> (decideLevel, decisionStep, fromMaybe (-1) antecedent, Bit value)
    |]
  [|
    \(decideLevel, decisionStep, ante, Bit value) ->
      if decideLevel < 0
        then Indefinite
        else
          let antecedent = if ante < 0 then Nothing else Just ante
           in Definite {..}
    |]

data Clause = Clause
  { lits :: {-# UNPACK #-} !(U.Vector Lit)
  , watched1 :: {-# UNPACK #-} !Index
  , watched2 :: {-# UNPACK #-} !Index
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

data WatchVar = W1 | W2 deriving (Show, Eq, Ord, Generic)

deriveGeneric ''WatchVar

deriving via L.AsMovable WatchVar instance PL.Consumable WatchVar

deriving via L.AsMovable WatchVar instance PL.Dupable WatchVar

deriving via L.Generically WatchVar instance PL.Movable WatchVar

litBucketIndex :: Lit -> Int
{-# INLINE litBucketIndex #-}
litBucketIndex lit =
  2 * fromVarId (litVar lit)
    + case decodeLit lit of
      Negative {} -> 1
      Positive {} -> 0

watchOccurrence :: ClauseId -> WatchVar -> Int
{-# INLINE watchOccurrence #-}
watchOccurrence cid W1 = 2 * unClauseId cid
watchOccurrence cid W2 = 2 * unClauseId cid + 1

watchOccurrenceClause :: Int -> ClauseId
{-# INLINE watchOccurrenceClause #-}
watchOccurrenceClause = ClauseId . (`quot` 2)

watchOccurrenceSlot :: Int -> WatchVar
{-# INLINE watchOccurrenceSlot #-}
watchOccurrenceSlot occurrence
  | even occurrence = W1
  | otherwise = W2

data ClauseBody = ClauseBody
  { wat1, wat2 :: {-# UNPACK #-} !Index
  }
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''ClauseBody

deriving via L.AsMovable ClauseBody instance PL.Consumable ClauseBody

deriving via L.AsMovable ClauseBody instance PL.Dupable ClauseBody

deriving via L.Generically ClauseBody instance PL.Movable ClauseBody

deriving via L.Generically ClauseBody instance Copyable ClauseBody

data instance U.Vector ClauseBody
  = V_CB
      {-# UNPACK #-} !Int
      {-# UNPACK #-} !(U.Vector Int)

data instance U.MVector s ClauseBody
  = MV_CB
      {-# UNPACK #-} !Int
      {-# UNPACK #-} !(U.MVector s Int)

instance U.Unbox ClauseBody

{- HLINT ignore "Redundant lambda" -}
instance G.Vector U.Vector ClauseBody where
  basicUnsafeFreeze (MV_CB i mu) = V_CB i <$> G.basicUnsafeFreeze mu
  {-# INLINE basicUnsafeFreeze #-}
  basicUnsafeThaw (V_CB i mu) = MV_CB i <$> G.basicUnsafeThaw mu
  {-# INLINE basicUnsafeThaw #-}
  basicLength = \(V_CB l _) -> l
  {-# INLINE basicLength #-}
  basicUnsafeSlice off len = \(V_CB _ v) ->
    V_CB len (G.basicUnsafeSlice (off * 2) (len * 2) v)
  {-# INLINE basicUnsafeSlice #-}
  basicUnsafeIndexM = \(V_CB _ v) i -> do
    wat1 <- G.basicUnsafeIndexM v (2 * i)
    wat2 <- G.basicUnsafeIndexM v (2 * i + 1)
    pure $! ClauseBody {..}
  {-# INLINE basicUnsafeIndexM #-}
  basicUnsafeCopy = \(MV_CB _ mv) (V_CB _ v) ->
    G.basicUnsafeCopy mv v
  {-# INLINE basicUnsafeCopy #-}

instance MG.MVector U.MVector ClauseBody where
  basicLength = \(MV_CB l _) -> l
  {-# INLINE basicLength #-}
  basicUnsafeSlice off len = \(MV_CB _ v) ->
    MV_CB len (MG.basicUnsafeSlice (off * 2) (len * 2) v)
  {-# INLINE basicUnsafeSlice #-}
  basicOverlaps = \(MV_CB _ l) (MV_CB _ r) -> MG.basicOverlaps l r
  {-# INLINE basicOverlaps #-}
  basicUnsafeNew l = MV_CB l <$> MG.unsafeNew (2 * l)
  {-# INLINE basicUnsafeNew #-}
  basicInitialize (MV_CB _ l) = MG.basicInitialize l
  {-# INLINE basicInitialize #-}
  basicUnsafeRead (MV_CB _ v) i = do
    wat1 <- MG.basicUnsafeRead v (2 * i)
    wat2 <- MG.basicUnsafeRead v (2 * i + 1)
    pure $! ClauseBody {..}
  {-# INLINE basicUnsafeRead #-}
  basicUnsafeWrite (MV_CB _ v) i ClauseBody {..} = do
    MG.basicUnsafeWrite v (2 * i) wat1
    MG.basicUnsafeWrite v (2 * i + 1) wat2
  {-# INLINE basicUnsafeWrite #-}
  basicClear (MV_CB _ l) = MG.basicClear l
  {-# INLINE basicClear #-}
  basicUnsafeCopy (MV_CB _ dst) (MV_CB _ src) = MG.basicUnsafeCopy dst src
  {-# INLINE basicUnsafeCopy #-}
  basicUnsafeMove (MV_CB _ dst) (MV_CB _ src) = MG.basicUnsafeMove dst src
  {-# INLINE basicUnsafeMove #-}
  basicUnsafeGrow = \(MV_CB l mv) growth ->
    MV_CB (l + growth) <$> MG.basicUnsafeGrow mv (2 * growth)

type VarQueue = PSQ.IntPSQ (Down Double) ()

type LBD = Double

type VarActivityIncr = Double

data VSIDSState s where
  VSIDSState ::
    -- | Unsatisfieds
    !VarQueue ->
    -- | Satisfieds
    !VarQueue ->
    -- | Moving average of LBD (if adaptive mode)
    {-# UNPACK #-} !LBD ->
    -- | True if the last learnt clause exceeds LBD
    !Bool ->
    -- | Current variable activity increment
    !VarActivityIncr ->
    VSIDSState s

deriving via L.AsMovable (VSIDSState s) instance PL.Consumable (VSIDSState s)

deriving via L.AsMovable (VSIDSState s) instance PL.Dupable (VSIDSState s)

instance PL.Movable (VSIDSState s) where
  move (VSIDSState ql qr spec x l) = PL.Ur (VSIDSState ql qr spec x l)

moveToSatQueue :: VarId -> VSIDSState s %1 -> VSIDSState s
moveToSatQueue vid = \(VSIDSState unsats sats lbdEma exc l) ->
  case PSQ.deleteView vidInt unsats of
    Nothing -> VSIDSState unsats sats lbdEma exc l
    Just (p, (), unsats) ->
      VSIDSState unsats (PSQ.unsafeInsertNew vidInt p () sats) lbdEma exc l
  where
    !vidInt = fromIntegral $ unVarId vid

moveToUnsatQueue :: VarId -> VSIDSState s %1 -> VSIDSState s
moveToUnsatQueue vid = \(VSIDSState unsats sats lbdEma exc l) ->
  case PSQ.deleteView vidInt sats of
    Nothing -> VSIDSState unsats sats lbdEma exc l
    Just (p, (), sats) ->
      VSIDSState (PSQ.unsafeInsertNew vidInt p () unsats) sats lbdEma exc l
  where
    !vidInt = fromIntegral $ unVarId vid

isPositive :: Lit -> Bool
isPositive (Lit w) = w .&. negateMask == 0

data PropResult
  = ConflictFound {-# UNPACK #-} !ClauseId !Lit
  | NoMorePropagation
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''PropResult

deriving via L.AsMovable PropResult instance L.Consumable PropResult

deriving via L.AsMovable PropResult instance L.Dupable PropResult

deriving via L.Generically PropResult instance L.Movable PropResult

data AssertionResult
  = NewlyAsserted
  | AlreadyAsserted
  | ContradictingAssertion
  deriving (Show)

deriveGeneric ''AssertionResult

deriving via L.AsMovable AssertionResult instance L.Consumable AssertionResult

deriving via L.AsMovable AssertionResult instance L.Dupable AssertionResult

deriving via L.Generically AssertionResult instance L.Movable AssertionResult
