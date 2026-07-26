{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QualifiedDo #-}
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
  toCDCLState,
  extractValuation,
  CDCLState (..),
  CDCLOptions (..),
  defaultOptions,
  VariableSelection (..),
  defaultDecayFactor,
  defaultAdaptiveFactor,
  RestartStrategy (..),
  defaultRestartStrategy,
  defaultExponentialRestart,
  defaultLubyRestart,
  luby,
  AssertionResult (..),
  Valuation,
  Clauses,
  WatchMap,
  levelStartsL,
  trailL,
  qheadL,
  clearTrailSuffix,
  pushClause,
  getClauseLits,
  getClauseSearch,
  getNumClauses,
  setWatchVar,
  detachWatchBucket,
  getNextWatchOccurrence,
  appendWatchOccurrence,
  linkWatchOccurrence,
  getWatchHeadAt,
  getWatchTailAt,
  getWatchMapSizes,
  litBucketIndex,
  watchOccurrence,
  watchOccurrenceClause,
  watchOccurrenceSlot,
  withClauseLits,
  foldClauseLits,
  watchesL,
  clausesL,
  valuationL,
  vsidsStateL,
  satVarQL,
  unsatVarQL,
  moveToSatQueue,
  moveToUnsatQueue,
  incrementVarM,
  findUnsatVar,
  decayVarPriosM,
  VarQueue,
  VSIDSState (..),
  numInitialClausesL,
  runClausesValsM,
  unsatisfiedsL,
  clausesAndValsL,
  -- ifoldClauseLitsM,
  clausesValsAndUnsatsL,
  Index,

  -- * Compact literal
  Lit (PosL, NegL),
  litVar,
  negL,
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
  fromVarId,
  toVarId,
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
  WatchedLits (..),
  WatchedLitIndices (..),
  getWatchedLits,
  getLit1,
  getLit2,
  getClauseLitAt,
  elemWatchLit,
  watchLitOf,
  getWatchedLitIndices,
  elemWatchLitIdx,
  RestartResult (..),
  tryRestart,
  bumpSeedScan,
  bumpPostDrainScan,
  bumpAssignment,
  bumpTrailAppend,
  bumpDuplicateEnqueue,
  bumpPropagationEvent,
  bumpWatchVisit,
  bumpWatchMove,
  bumpLiteralInspections,
  bumpDecision,
  bumpConflict,
  recordBacktrack,
  SolverStats (..),
  solverStatsL,
  zeroSolverStats,
) where

import Control.DeepSeq (NFData)
import Control.Foldl qualified as Foldl
import Control.Foldl qualified as L
import Control.Functor.Linear qualified as C
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens (Lens', Prism', foldring, lens, prism', (.~))
import Control.Monad (guard)
import Control.Monad.ST (runST)
import Control.Optics.Linear qualified as LinLens
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Array.Polarized.Push.Extra qualified as Push
import Data.Bifunctor.Linear qualified as BiL
import Data.Bit (Bit (..))
import Data.Bits (popCount, xor, (.&.), (.|.))
import Data.Coerce (coerce)
import Data.DList qualified as DL
import Data.Foldable qualified as F
import Data.Function (fix)
import Data.Functor.Linear qualified as D
import Data.Generics.Labels ()
import Data.Hashable (Hashable)
import Data.IntPSQ qualified as PSQ
import Data.List (mapAccumL)
import Data.Maybe (fromMaybe)
import Data.Monoid.Linear.Orphans ()
import Data.Ord (Down (..))
import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies, reflect)
import Data.Semigroup (Max (..))
import Data.Set qualified as Set
import Data.Set.Mutable.Linear.Extra qualified as LSet
import Data.Strict.Tuple (Pair (..))
import Data.Unrestricted.Linear (Ur (..), UrT (..))
import Data.Unrestricted.Linear qualified as L
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Orphans ()
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as MG
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import Data.Vector.Unboxed.Mutable qualified as UM
import GHC.Generics (Generic)
import Generics.Linear qualified as L
import Generics.Linear.TH (deriveGeneric)
import Linear.Token.Linearly
import Linear.Token.Linearly.Unsafe (HasLinearWitness)
import Logic.Propositional.Classical.SAT.Types (SatResult (..))
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Math.NumberTheory.Logarithms (wordLog2')
import Prelude.Linear (lseq, (&))
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe

type RunCount = Word

type RestartAt = Word

type RestartCount = Word

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
    }

#ifdef HERBRAND_CDCL_INSTRUMENTED
data Instrumentation = Instrumentation !SolverStats
  deriving (Show, Eq, Ord, Generic)
#else
data Instrumentation = Instrumentation
  deriving (Show, Eq, Ord, Generic)
#endif

deriveGeneric ''Instrumentation

deriving via L.AsMovable Instrumentation instance PL.Consumable Instrumentation

deriving via L.AsMovable Instrumentation instance PL.Dupable Instrumentation

deriving via L.Generically Instrumentation instance PL.Movable Instrumentation

zeroInstrumentation :: Instrumentation
#ifdef HERBRAND_CDCL_INSTRUMENTED
zeroInstrumentation = Instrumentation zeroSolverStats
#else
zeroInstrumentation = Instrumentation
#endif

data RestartState where
  RestartState ::
    {-# UNPACK #-} !RunCount ->
    {-# UNPACK #-} !RestartAt ->
    {-# UNPACK #-} !RestartCount ->
    {-# UNPACK #-} !Instrumentation %1 ->
    RestartState
  deriving (Show, Eq, Ord, Generic)

deriving via L.AsMovable RestartState instance PL.Consumable RestartState

deriving via L.AsMovable RestartState instance PL.Dupable RestartState

instance PL.Movable RestartState where
  move = Unsafe.toLinear Ur

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

nextRestartState :: RestartStrategy -> RestartState %1 -> RestartState
nextRestartState = \case
  NoRestart -> PL.id
  ExponentialRestart {..} -> \(RestartState _ thresh c instrumentation) ->
    RestartState 0 (thresh * increaseFactor) (c + 1) instrumentation
  LubyRestart {..} -> \(RestartState _ _ c instrumentation) ->
    RestartState 0 (initialRestart * luby (c + 1)) (c + 1) instrumentation

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

getInitRestart :: RestartStrategy -> Maybe Word
getInitRestart NoRestart = Nothing
getInitRestart ExponentialRestart {..} = Just initialRestart
getInitRestart LubyRestart {..} = Just initialRestart

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

fromVarId :: VarId -> Int
fromVarId = fromIntegral . unVarId

toVarId :: Int -> VarId
toVarId = fromIntegral

derivingUnbox "VarId" [t|VarId -> Word|] [|unVarId|] [|VarId|]

newtype ClauseId = ClauseId {unClauseId :: Int}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, PL.Consumable, PL.Dupable, PL.Movable)

derivingUnbox "ClauseId" [t|ClauseId -> Int|] [|unClauseId|] [|ClauseId|]

newtype DecideLevel = DecideLevel {unDecideLevel :: Int}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, Integral, Real, PL.Consumable, PL.Dupable, PL.Movable)

derivingUnbox "DecideLevel" [t|DecideLevel -> Int|] [|unDecideLevel|] [|DecideLevel|]

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

type Valuation = LUA.UArray Variable

data WatchVar = W1 | W2 deriving (Show, Eq, Ord, Generic)

deriveGeneric ''WatchVar

deriving via L.AsMovable WatchVar instance PL.Consumable WatchVar

deriving via L.AsMovable WatchVar instance PL.Dupable WatchVar

deriving via L.Generically WatchVar instance PL.Movable WatchVar

data WatchMap where
  WatchMap ::
    {-# UNPACK #-} !(LUA.UArray Int) %1 ->
    {-# UNPACK #-} !(LUA.UArray Int) %1 ->
    {-# UNPACK #-} !(LUV.Vector Int) %1 ->
    WatchMap

instance PL.Consumable WatchMap where
  consume (WatchMap heads tails nexts) =
    heads `lseq` tails `lseq` nexts `lseq` ()

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

detachWatchBucket :: Lit -> S.State WatchMap (Ur Int)
{-# INLINE detachWatchBucket #-}
detachWatchBucket lit =
  S.state \(WatchMap heads tails nexts) ->
    LUA.unsafeGet (litBucketIndex lit) heads & \(Ur head, heads) ->
      ( Ur head
      , WatchMap
          (LUA.unsafeSet (litBucketIndex lit) (-1) heads)
          (LUA.unsafeSet (litBucketIndex lit) (-1) tails)
          nexts
      )

getNextWatchOccurrence :: Int -> S.State WatchMap (Ur Int)
{-# INLINE getNextWatchOccurrence #-}
getNextWatchOccurrence occurrence =
  S.state \(WatchMap heads tails nexts) ->
    LUV.unsafeGet occurrence nexts & \(Ur next, nexts) ->
      (Ur next, WatchMap heads tails nexts)

appendWatchOccurrence :: Lit -> Int -> S.State WatchMap ()
{-# INLINE appendWatchOccurrence #-}
appendWatchOccurrence lit occurrence =
  S.modify PL.$ \(WatchMap heads tails nexts) ->
    let bucket = litBucketIndex lit
     in LUA.unsafeGet bucket tails & \(Ur oldTail, tails) ->
          if oldTail < 0
            then
              WatchMap
                (LUA.unsafeSet bucket occurrence heads)
                (LUA.unsafeSet bucket occurrence tails)
                (LUV.unsafeSet occurrence (-1) nexts)
            else
              WatchMap
                heads
                (LUA.unsafeSet bucket occurrence tails)
                ( LUV.unsafeSet occurrence (-1) PL.$
                    LUV.unsafeSet oldTail occurrence nexts
                )

linkWatchOccurrence :: Lit -> Int -> S.State WatchMap ()
{-# INLINE linkWatchOccurrence #-}
linkWatchOccurrence lit occurrence =
  S.modify PL.$ \(WatchMap heads tails nexts) ->
    let bucket = litBucketIndex lit
     in LUA.unsafeGet bucket heads & \(Ur oldHead, heads) ->
          LUA.unsafeGet bucket tails & \(Ur oldTail, tails) ->
            if oldTail < 0
              then
                WatchMap
                  (LUA.unsafeSet bucket occurrence heads)
                  (LUA.unsafeSet bucket occurrence tails)
                  (LUV.unsafeSet occurrence (-1) nexts)
              else
                if occurrence < oldHead
                  then
                    WatchMap
                      (LUA.unsafeSet bucket occurrence heads)
                      tails
                      (LUV.unsafeSet occurrence oldHead nexts)
                  else
                    WatchMap
                      heads
                      (LUA.unsafeSet bucket occurrence tails)
                      ( LUV.unsafeSet occurrence (-1) PL.$
                          LUV.unsafeSet oldTail occurrence nexts
                      )

getWatchHeadAt :: Int -> S.State WatchMap (Ur Int)
getWatchHeadAt bucket =
  S.state \(WatchMap heads tails nexts) ->
    LUA.unsafeGet bucket heads & \(head, heads) ->
      (head, WatchMap heads tails nexts)

getWatchTailAt :: Int -> S.State WatchMap (Ur Int)
getWatchTailAt bucket =
  S.state \(WatchMap heads tails nexts) ->
    LUA.unsafeGet bucket tails & \(tailOccurrence, tails) ->
      (tailOccurrence, WatchMap heads tails nexts)

getWatchMapSizes :: S.State WatchMap (Ur (Int, Int, Int))
getWatchMapSizes =
  S.state \(WatchMap heads tails nexts) ->
    LUA.size heads & \(Ur headCount, heads) ->
      LUA.size tails & \(Ur tailCount, tails) ->
        LUV.size nexts & \(Ur nextCount, nexts) ->
          (Ur (headCount, tailCount, nextCount), WatchMap heads tails nexts)

appendWatchSlots :: S.State WatchMap ()
{-# INLINE appendWatchSlots #-}
appendWatchSlots =
  S.modify PL.$ \(WatchMap heads tails nexts) ->
    WatchMap heads tails PL.$ LUV.push (-1) PL.$ LUV.push (-1) nexts

data ClauseBody = ClauseBody
  { wat1, wat2 :: {-# UNPACK #-} !Index
  }
  deriving (Show, Eq, Ord, Generic)

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

data Clauses where
  Clauses ::
    {-# UNPACK #-} !(LV.Vector (U.Vector Lit)) %1 ->
    {-# UNPACK #-} !(LUV.Vector ClauseBody) %1 ->
    Clauses

instance PL.Consumable Clauses where
  consume (Clauses lits bs) = lits `lseq` bs `lseq` ()

instance PL.Dupable Clauses where
  dup2 (Clauses lits bs) =
    PL.dup2 (lits, bs) & \((lits, bs), (lits', bs')) ->
      (Clauses lits bs, Clauses lits' bs')

type VarQueue = PSQ.IntPSQ (Down Double) ()

type LBD = Double

getDecideLevel :: Variable -> Maybe DecideLevel
getDecideLevel = \case
  Definite {..} -> Just decideLevel
  _ -> Nothing

calcLBDL :: L.FoldM (UrT (S.State Valuation)) Lit Int
calcLBDL =
  L.premapM
    ( \l -> do
        UrT $
          S.state
            ( BiL.first (Ur.lift getDecideLevel)
                PL.. LUA.unsafeGet (fromIntegral $ unVarId $ litVar l)
            )
    )
    $ L.generalize
      (L.handles L.folded $ Set.size <$> L.set)

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
  move (VSIDSState ql qr spec x l) = Ur (VSIDSState ql qr spec x l)

data CDCLState s where
  CDCLState ::
    -- | Number of original clauses
    {-# UNPACK #-} !Int %1 ->
    -- | Trail start index for each decision level
    {-# UNPACK #-} !(LUV.Vector Step) %1 ->
    -- | Assigned literals in propagation order
    {-# UNPACK #-} !(LUV.Vector Lit) %1 ->
    -- | Index of the next trail literal to propagate
    {-# UNPACK #-} !Int %1 ->
    -- | Clauses
    {-# UNPACK #-} !Clauses %1 ->
    -- | Watches
    {-# UNPACK #-} !WatchMap %1 ->
    -- | Valuations
    {-# UNPACK #-} !Valuation %1 ->
    -- | Unsatisfied Clauses
    {-# UNPACK #-} !(LSet.Set ClauseId) %1 ->
    -- | Variable queue
    {-# UNPACK #-} !(VSIDSState s) %1 ->
    -- | Restart State
    {-# UNPACK #-} !RestartState %1 ->
    CDCLState s
  deriving anyclass (HasLinearWitness)

clausesL :: LinLens.Lens' (CDCLState s) Clauses
{-# INLINE clausesL #-}
clausesL = LinLens.lens \(CDCLState numOrig ss trail qhead cs ws vs vids varQ rs) ->
  (cs, \cs -> CDCLState numOrig ss trail qhead cs ws vs vids varQ rs)

pushClause :: forall s. (Reifies s CDCLOptions) => Clause -> S.State (CDCLState s) ()
{-# INLINE pushClause #-}
{- HLINT ignore pushClause "Redundant lambda" -}
pushClause = \Clause {..} -> S.do
  Ur cid <- Ur.lift ClauseId C.<$> getNumClauses
  clausesL S.%= \(Clauses litss bs) ->
    LUV.push
      ClauseBody
        { wat1 = watched1
        , wat2 = watched2
        }
      bs
      & \bs ->
        LV.push lits litss & \litss -> Clauses litss bs
  S.zoom watchesL appendWatchSlots
  if watched1 >= 0
    then
      S.zoom watchesL PL.$
        linkWatchOccurrence
          (U.unsafeIndex lits watched1)
          (watchOccurrence cid W1)
    else S.pure ()
  if watched2 >= 0
    then
      S.zoom watchesL PL.$
        linkWatchOccurrence
          (U.unsafeIndex lits watched2)
          (watchOccurrence cid W2)
    else S.pure ()
  Ur !lbd <- S.zoom valuationL (Ur.runUrT (L.foldOverM (foldring U.foldr) calcLBDL lits))
  vsidsStateL
    S.%= case decayFactor $ reflect @s Proxy of
      ConstantFactor {} -> \(VSIDSState unsats sats ema x l) ->
        let (unsats' :!: mq1) = insertsQ l unsats lits
            (sats' :!: mq2) = insertsQ l sats lits
            !mq = mq1 <> mq2
         in adjustVarActivities
              mq
              (VSIDSState unsats' sats' ema x l)
      Adaptive {..} -> \(VSIDSState unsats sats ema _ l) ->
        let (unsats' :!: mq1) = insertsQ l unsats lits
            (sats' :!: mq2) = insertsQ l sats lits
            !mq = mq1 <> mq2
            !ema' = ema * lbdEmaDecayFactor + fromIntegral lbd * (1 - lbdEmaDecayFactor)
         in adjustVarActivities mq $
              VSIDSState unsats' sats' ema' (fromIntegral lbd >= ema') l
  where
    insertsQ !l !q0 =
      U.foldr'
        ( \lit (q :!: mMax) ->
            let (mp, q') = incrementVar l lit q
             in (q' :!: (Max <$> mp) <> mMax)
        )
        (q0 :!: Nothing)

decayVarPriosM :: forall s. (Reifies s CDCLOptions) => S.State (VSIDSState s) ()
{-# INLINE decayVarPriosM #-}
decayVarPriosM = S.modify \(VSIDSState ls qs spec exc l) ->
  case decayFactor (reflect $ Proxy @s) of
    ConstantFactor alpha -> VSIDSState ls qs spec exc (l / alpha)
    Adaptive {..}
      | exc -> VSIDSState ls qs spec exc (l / highLBDDecay)
      | otherwise -> VSIDSState ls qs spec exc (l / lowLBDDecay)

multiplyVarActs :: Double -> VarQueue -> VarQueue
{-# INLINE multiplyVarActs #-}
multiplyVarActs = \alpha -> PSQ.unsafeMapMonotonic \_ (Down p) v -> (Down $ p * alpha, v)

findUnsatVar :: S.State (VSIDSState s) (Ur (Maybe VarId))
findUnsatVar = S.state \(VSIDSState unsat sat lbdEma exc l) ->
  PSQ.minView unsat & \case
    Just (k, p, (), unsat) ->
      ( Ur (Just $ fromIntegral k)
      , VSIDSState unsat (PSQ.unsafeInsertNew k p () sat) lbdEma exc l
      )
    Nothing -> (Ur Nothing, VSIDSState unsat sat lbdEma exc l)

incrementVarM :: Lit -> S.State (VSIDSState s) ()
incrementVarM lit = S.modify \(VSIDSState unsats sats lbdEma exc l) ->
  let (mq, uns') = incrementVar l lit unsats
      (mq', sat') = incrementVar l lit sats
   in adjustVarActivities ((Max <$> mq) <> (Max <$> mq')) $
        VSIDSState uns' sat' lbdEma exc l

adjustVarActivities :: Maybe (Max Double) -> VSIDSState s -> VSIDSState s
{-# INLINE adjustVarActivities #-}
adjustVarActivities (Just (Max p)) | p >= 1e100 =
  \(VSIDSState uns sat lbdEma exc l) ->
    VSIDSState (multiplyVarActs 1e-100 uns) (multiplyVarActs 1e-100 sat) lbdEma exc (l * 1e-100)
adjustVarActivities _ = id

incrementVar :: Double -> Lit -> VarQueue -> (Maybe Double, VarQueue)
incrementVar l =
  PSQ.alter
    ( maybe (Nothing, Nothing) \(p, ()) ->
        let !p' = p + Down l
         in (Just $ getDown p', Just (p', ()))
    )
    . fromIntegral
    . unVarId
    . litVar

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

getClauseLits :: ClauseId -> S.State Clauses (Ur (U.Vector Lit))
{-# INLINE getClauseLits #-}
getClauseLits i = S.state \(Clauses litss bs) ->
  LV.unsafeGet (unClauseId i) litss & \(lits, litss) ->
    (lits, Clauses litss bs)

withClauseLits ::
  ClauseId ->
  Clauses %1 ->
  (U.Vector Lit -> b) %1 ->
  (b, Clauses)
{-# INLINE withClauseLits #-}
withClauseLits i c f =
  S.runState (getClauseLits i) c & \(Ur lits, c) ->
    (f lits, c)

foldClauseLits :: L.Fold Lit b -> ClauseId -> S.State Clauses (Ur b)
{-# INLINE foldClauseLits #-}
foldClauseLits f cid =
  Ur.lift (L.purely (\step ini out -> out . U.foldl step ini) f)
    D.<$> getClauseLits cid

{-
ifoldClauseLitsM :: (C.Monad m) => L.FoldM (UrT m) (Int, Lit) b -> ClauseId -> S.StateT Clauses m (Ur b)
{-# INLINE ifoldClauseLitsM #-}
ifoldClauseLitsM f cid =
  Ur.lift
    ( L.impurely
        (\step ini out -> out . U.ifoldl (curry . step) ini)
        f
    )
    C.=<< getClauseLits cid
 -}
runClausesValsM :: S.StateT Clauses (S.State Valuation) a %1 -> S.State (CDCLState s) a
{-# INLINE runClausesValsM #-}
{- HLINT ignore runClausesValsM "Redundant lambda" -}
runClausesValsM = \act -> S.uses clausesAndValsL \(clauses, vals) ->
  S.runState
    (S.runStateT act clauses)
    vals
    & \((ans, clauses), val) -> (ans, (clauses, val))

getNumClauses :: S.State (CDCLState s) (Ur Int)
{-# INLINE getNumClauses #-}
getNumClauses =
  S.uses clausesL \(Clauses litss bs) ->
    Clauses litss C.<$> LUV.size bs

levelStartsL :: LinLens.Lens' (CDCLState s) (LUV.Vector Step)
{-# INLINE levelStartsL #-}
levelStartsL = LinLens.lens \(CDCLState numOrig ss trail qhead cs ws vs vids varQ rs) ->
  (ss, \ss -> CDCLState numOrig ss trail qhead cs ws vs vids varQ rs)

trailL :: LinLens.Lens' (CDCLState s) (LUV.Vector Lit)
{-# INLINE trailL #-}
trailL = LinLens.lens \(CDCLState numOrig ss trail qhead cs ws vs vids varQ rs) ->
  (trail, \trail -> CDCLState numOrig ss trail qhead cs ws vs vids varQ rs)

qheadL :: LinLens.Lens' (CDCLState s) Int
{-# INLINE qheadL #-}
qheadL = LinLens.lens \(CDCLState numOrig ss trail qhead cs ws vs vids varQ rs) ->
  (qhead, \qhead -> CDCLState numOrig ss trail qhead cs ws vs vids varQ rs)

trailValuationVSIDSL ::
  LinLens.Lens'
    (CDCLState s)
    (LUV.Vector Lit, Valuation, VSIDSState s)
{-# INLINE trailValuationVSIDSL #-}
trailValuationVSIDSL =
  LinLens.lens \(CDCLState numOrig ss trail qhead cs ws vals vids varQ rs) ->
    ( (trail, vals, varQ)
    , \(trail, vals, varQ) ->
        CDCLState numOrig ss trail qhead cs ws vals vids varQ rs
    )

clearTrailSuffix :: Int -> S.State (CDCLState s) (Ur Int)
{-# INLINE clearTrailSuffix #-}
clearTrailSuffix cutoff =
  S.uses trailValuationVSIDSL \(trail, vals, varQ) ->
    LUV.size trail & \(Ur trailLength, trail) ->
      fix
        ( \go !index !cleared trail vals varQ ->
            if index < cutoff
              then
                ( Ur cleared
                , (LUV.slice 0 cutoff trail, vals, varQ)
                )
              else
                LUV.unsafeGet index trail & \(Ur lit, trail) ->
                  LUA.unsafeSet (fromVarId $ litVar lit) Indefinite vals & \vals ->
                    go
                      (index - 1)
                      (cleared + 1)
                      trail
                      vals
                      (moveToUnsatQueue (litVar lit) varQ)
        )
        (trailLength - 1)
        0
        trail
        vals
        varQ

numInitialClausesL :: LinLens.Lens' (CDCLState s) Int
numInitialClausesL = LinLens.lens \(CDCLState numOrig ss trail qhead cs ws vs vids varQ rs) ->
  (numOrig, \numOrig -> CDCLState numOrig ss trail qhead cs ws vs vids varQ rs)

watchesL :: LinLens.Lens' (CDCLState s) WatchMap
{-# INLINE watchesL #-}
watchesL = LinLens.lens \(CDCLState numOrig ss trail qhead cs ws vs vids varQ rs) ->
  (ws, \ws -> CDCLState numOrig ss trail qhead cs ws vs vids varQ rs)

valuationL :: LinLens.Lens' (CDCLState s) Valuation
{-# INLINE valuationL #-}
valuationL = LinLens.lens \(CDCLState norig ss trail qhead cs ws vs vids varQ rs) ->
  (vs, \vs -> CDCLState norig ss trail qhead cs ws vs vids varQ rs)

vsidsStateL :: LinLens.Lens' (CDCLState s) (VSIDSState s)
vsidsStateL = LinLens.lens \(CDCLState norig ss trail qhead cs ws vs vids varQ rs) ->
  (varQ, \varQ -> CDCLState norig ss trail qhead cs ws vs vids varQ rs)

unsatVarQL :: LinLens.Lens' (CDCLState s) (Ur VarQueue)
unsatVarQL =
  vsidsStateL LinLens..> LinLens.lens \(VSIDSState qs rs x exc l) ->
    (Ur qs, \(Ur qs) -> VSIDSState qs rs x exc l)

satVarQL :: LinLens.Lens' (CDCLState s) (Ur VarQueue)
satVarQL =
  vsidsStateL LinLens..> LinLens.lens \(VSIDSState qs rs x exc l) ->
    (Ur rs, \(Ur rs) -> VSIDSState qs rs x exc l)

unsatisfiedsL :: LinLens.Lens' (CDCLState s) (LSet.Set ClauseId)
{-# INLINE unsatisfiedsL #-}
unsatisfiedsL = LinLens.lens \(CDCLState norig ss trail qhead cs ws vs vids varQ rs) ->
  (vids, \vids -> CDCLState norig ss trail qhead cs ws vs vids varQ rs)

clausesValsAndUnsatsL :: LinLens.Lens' (CDCLState s) (Clauses, Valuation, LSet.Set ClauseId)
{-# INLINE clausesValsAndUnsatsL #-}
clausesValsAndUnsatsL = LinLens.lens \(CDCLState norig ss trail qhead cs ws vs vids varQ rs) ->
  ((cs, vs, vids), \(cs, vs, vids) -> CDCLState norig ss trail qhead cs ws vs vids varQ rs)

clausesAndValsL :: LinLens.Lens' (CDCLState s) (Clauses, Valuation)
{-# INLINE clausesAndValsL #-}
clausesAndValsL = LinLens.lens \(CDCLState norig ss trail qhead cs ws vs vids varQ rs) ->
  ((cs, vs), \(cs, vs) -> CDCLState norig ss trail qhead cs ws vs vids varQ rs)

extractValuation :: CDCLState s %1 -> Valuation
extractValuation (CDCLState numOrig levelStarts trail qhead clauses watches vals vids varQs rs) =
  numOrig `lseq`
    levelStarts `lseq`
      trail `lseq`
        qhead `lseq`
          clauses `lseq`
            watches `lseq`
              vids `lseq`
                varQs `lseq`
                  rs `lseq`
                    vals

toCDCLState ::
  forall s.
  (Reifies s CDCLOptions) =>
  CNF VarId ->
  Linearly %1 ->
  Either (Ur (SatResult ())) (CDCLState s)
toCDCLState (CNF cls) lin =
  let restartOpt = restartStrategy $ reflect @s Proxy
      (cls', truth, contradicting, maxVar) =
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
      numVars = maybe 0 ((+ 1) . fromEnum) maxVar
      rs =
        RestartState
          0
          (fromMaybe 0 $ getInitRestart restartOpt)
          0
          zeroInstrumentation
      vsidsS =
        VSIDSState
          (PSQ.fromList [(vid, 0, ()) | vid <- [0 .. (numVars - 1)]])
          PSQ.empty
          0
          True
          1.0
      (numOrigCls, cls'') = mapAccumL buildClause 0 cls'
      (!watchHeads, !watchTails, !watchNexts) = buildWatchVectors numVars cls''
   in case () of
        _
          | truth -> lin `lseq` Left (Ur (Satisfiable ()))
          | contradicting -> lin `lseq` Left (Ur Unsat)
        _ ->
          besides lin (LUV.constantL (numVars + 1) 0) PL.& \(levelStarts0, lin) ->
            let levelStarts = LUV.slice 0 1 levelStarts0
             in besides lin (LUV.constantL numVars (PosL 0)) PL.& \(trail0, lin) ->
                  let trail = LUV.slice 0 0 trail0
                   in besides lin (toClauses cls'') PL.& \(clauses, lin) ->
                        besides lin (toWatchMap watchHeads watchTails watchNexts) & \(watcheds, lin) ->
                          besides lin (LUA.allocL (maybe 0 ((+ 1) . fromEnum) maxVar) Indefinite) PL.& \(vals, lin) ->
                            Right PL.$
                              CDCLState
                                numOrigCls
                                levelStarts
                                trail
                                0
                                clauses
                                watcheds
                                vals
                                (LSet.fromListL [ClauseId 0 .. ClauseId (numOrigCls - 1)] lin)
                                vsidsS
                                rs

toClauses :: [Clause] -> Linearly %1 -> Clauses
toClauses cs l =
  PL.dup2 l & \(l, l') ->
    F.foldMap'
      ( \Clause {..} ->
          ( Ur (DL.singleton lits)
          , Push.singleton
              ClauseBody
                { wat1 = watched1
                , wat2 = watched2
                }
          )
      )
      cs
      & \(Ur lits, bs) ->
        Clauses
          (LV.fromListL (DL.toList lits) l)
          (LUV.fromVectorL (Push.alloc bs) l')

buildClause ::
  Int ->
  [Lit] ->
  (Int, Clause)
buildClause i [] =
  (i + 1, Clause {lits = mempty, watched1 = -1, watched2 = -1})
buildClause i [x] =
  (i + 1, Clause {lits = U.singleton x, watched1 = 0, watched2 = -1})
buildClause i xs =
  (i + 1, Clause {lits = U.fromList xs, watched1 = 0, watched2 = 1})

buildWatchVectors :: Int -> [Clause] -> (U.Vector Int, U.Vector Int, U.Vector Int)
buildWatchVectors numVars clauses = runST do
  heads <- UM.replicate (2 * numVars) (-1)
  tails <- UM.replicate (2 * numVars) (-1)
  nexts <- UM.replicate (2 * length clauses) (-1)
  let add occurrence lit = do
        let bucket = litBucketIndex lit
        oldTail <- UM.unsafeRead tails bucket
        if oldTail < 0
          then UM.unsafeWrite heads bucket occurrence
          else UM.unsafeWrite nexts oldTail occurrence
        UM.unsafeWrite tails bucket occurrence
  mapM_
    ( \(clauseIndex, Clause {..}) -> do
        let cid = ClauseId clauseIndex
        if watched1 >= 0
          then add (watchOccurrence cid W1) $ U.unsafeIndex lits watched1
          else pure ()
        if watched2 >= 0
          then add (watchOccurrence cid W2) $ U.unsafeIndex lits watched2
          else pure ()
    )
    $ zip [0 ..] clauses
  (,,)
    <$> U.unsafeFreeze heads
    <*> U.unsafeFreeze tails
    <*> U.unsafeFreeze nexts

toWatchMap :: U.Vector Int -> U.Vector Int -> U.Vector Int -> Linearly %1 -> WatchMap
toWatchMap heads tails nexts lin =
  PL.dup2 lin & \(headsLin, restLin) ->
    PL.dup2 restLin & \(tailsLin, nextsLin) ->
      WatchMap
        (LUA.fromVectorL heads headsLin)
        (LUA.fromVectorL tails tailsLin)
        (LUV.fromVectorL nexts nextsLin)

deriveGeneric ''CDCLState

deriving via L.Generically (CDCLState s) instance PL.Consumable (CDCLState s)

data UnitResult
  = Unit {-# UNPACK #-} !Lit
  | Conflict {-# UNPACK #-} !Lit
  | -- | Optional 'Pair' records possible old watched literal and new literal.
    Satisfied !(Maybe (Pair (Pair WatchVar Lit) (Pair Lit Index)))
  | WatchChangedFromTo !WatchVar {-# UNPACK #-} !Lit {-# UNPACK #-} !Lit {-# UNPACK #-} !Index
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''UnitResult

deriving via L.AsMovable UnitResult instance PL.Consumable UnitResult

deriving via L.AsMovable UnitResult instance PL.Dupable UnitResult

deriving via L.Generically UnitResult instance PL.Movable UnitResult

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
  = ConflictFound {-# UNPACK #-} !ClauseId !Lit
  | NoMorePropagation
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''PropResult

deriving via L.AsMovable PropResult instance L.Consumable PropResult

deriving via L.AsMovable PropResult instance L.Dupable PropResult

deriving via L.Generically PropResult instance L.Movable PropResult

watchVarL :: WatchVar -> Lens' Clause Index
watchVarL W1 = #watched1
watchVarL W2 = #watched2

data AssertionResult
  = NewlyAsserted
  | AlreadyAsserted
  | ContradictingAssertion
  deriving (Show)

deriveGeneric ''AssertionResult

deriving via L.AsMovable AssertionResult instance L.Consumable AssertionResult

deriving via L.AsMovable AssertionResult instance L.Dupable AssertionResult

deriving via L.Generically AssertionResult instance L.Movable AssertionResult

{- NOTE:

  1.  We cannot use 'watchVarL' here because `LV.modify_` consumes
      the first argument non-linearly!
  2.  Use of Unsafe.toLienar is safe here because vid = Int is freely dupable.
-}
setWatchVar :: ClauseId -> WatchVar %1 -> Index %1 -> S.State (CDCLState s) ()
{-# INLINE setWatchVar #-}
setWatchVar cid W1 = Unsafe.toLinear \vid ->
  clausesL S.%= \(Clauses litss bs) ->
    LUV.modify_ (#wat1 .~ vid) (unClauseId cid) bs & \bs ->
      Clauses litss bs
setWatchVar cid W2 = Unsafe.toLinear \vid ->
  clausesL S.%= \(Clauses litss bs) ->
    LUV.modify_ (#wat2 .~ vid) (unClauseId cid) bs & \bs ->
      Clauses litss bs

data WatchedLits
  = WatchOne {-# UNPACK #-} !Lit
  | WatchThese {-# UNPACK #-} !Lit {-# UNPACK #-} !Lit
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''WatchedLits

deriving via L.AsMovable WatchedLits instance PL.Consumable WatchedLits

deriving via L.AsMovable WatchedLits instance PL.Dupable WatchedLits

deriving via L.Generically WatchedLits instance PL.Movable WatchedLits

getWatchedLits :: ClauseId -> S.State Clauses (Ur WatchedLits)
getWatchedLits cid = S.state \(Clauses ls bs) ->
  LUV.unsafeGet (unClauseId cid) bs & \(Ur ClauseBody {..}, bs) ->
    LV.unsafeGet (unClauseId cid) ls & \(Ur lts, ls) ->
      let l1 = U.unsafeIndex lts wat1
          l2 = U.unsafeIndex lts wat2
       in wat2 >= 0 & \case
            True -> (Ur (WatchThese l1 l2), Clauses ls bs)
            False -> (Ur (WatchOne l1), Clauses ls bs)

getLit1 :: WatchedLits -> Lit
getLit1 (WatchOne l) = l
getLit1 (WatchThese l _) = l

getLit2 :: WatchedLits -> Maybe Lit
getLit2 WatchOne {} = Nothing
getLit2 (WatchThese _ l) = Just l

watchLitOf :: WatchVar -> WatchedLits -> Lit
watchLitOf W1 = getLit1
watchLitOf W2 = fromMaybe (error "watchLitOf: no lit2") . getLit2

getClauseLitAt :: ClauseId -> Index -> S.State Clauses (Ur Lit)
getClauseLitAt cid j = S.state \(Clauses ls bs) ->
  LV.unsafeGet (unClauseId cid) ls & \(Ur l, ls) ->
    (Ur (U.unsafeIndex l j), Clauses ls bs)

elemWatchLit :: Lit -> WatchedLits -> Bool
elemWatchLit l (WatchOne l1) = l == l1
elemWatchLit l (WatchThese l1 l2) = l == l1 || l == l2

-- NOTE: We use different ADT to make use of UNPACK pragma, instead of making it a functor.
data WatchedLitIndices
  = WatchOneI {-# UNPACK #-} !Index
  | WatchTheseI {-# UNPACK #-} !Index {-# UNPACK #-} !Index
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''WatchedLitIndices

deriving via L.AsMovable WatchedLitIndices instance PL.Consumable WatchedLitIndices

deriving via L.AsMovable WatchedLitIndices instance PL.Dupable WatchedLitIndices

deriving via L.Generically WatchedLitIndices instance PL.Movable WatchedLitIndices

getClauseSearch :: ClauseId -> S.State Clauses (Ur (U.Vector Lit, WatchedLitIndices))
getClauseSearch cid = S.state \(Clauses ls bs) ->
  LUV.unsafeGet (unClauseId cid) bs & \(Ur ClauseBody {..}, bs) ->
    LV.unsafeGet (unClauseId cid) ls & \(Ur clauseLits, ls) ->
      let watchedIndices =
            if wat2 >= 0
              then WatchTheseI wat1 wat2
              else WatchOneI wat1
       in (Ur (clauseLits, watchedIndices), Clauses ls bs)

getWatchedLitIndices :: ClauseId -> S.State Clauses (Ur WatchedLitIndices)
getWatchedLitIndices cid = S.state \(Clauses ls bs) ->
  LUV.unsafeGet (unClauseId cid) bs & \(Ur ClauseBody {..}, bs) ->
    if wat2 >= 0
      then (Ur (WatchTheseI wat1 wat2), Clauses ls bs)
      else (Ur (WatchOneI wat1), Clauses ls bs)

elemWatchLitIdx :: Index -> WatchedLitIndices -> Bool
elemWatchLitIdx l (WatchOneI l1) = l == l1
elemWatchLitIdx l (WatchTheseI l1 l2) = l == l1 || l == l2

restartStateL :: LinLens.Lens' (CDCLState s) RestartState
{- HLINT ignore restartStateL "Avoid lambda" -}
restartStateL = LinLens.lens \(CDCLState numOrig ss trail qhead cs ws vs vids varQ rs) ->
  (rs, \rs -> CDCLState numOrig ss trail qhead cs ws vs vids varQ rs)

#ifdef HERBRAND_CDCL_INSTRUMENTED
solverStatsL :: LinLens.Lens' (CDCLState s) SolverStats
solverStatsL =
  restartStateL LinLens..> LinLens.lens \(RestartState count threshold restarts (Instrumentation stats)) ->
    (stats, \stats -> RestartState count threshold restarts (Instrumentation stats))
#else
solverStatsL :: LinLens.Lens' (CDCLState s) SolverStats
solverStatsL =
  restartStateL LinLens..> LinLens.lens \(RestartState count threshold restarts instrumentation) ->
    ( zeroSolverStats
    , \stats ->
        stats `lseq`
          RestartState count threshold restarts instrumentation
    )
#endif

#ifdef HERBRAND_CDCL_INSTRUMENTED
bumpStats :: (SolverStats %1 -> SolverStats) %1 -> S.State (CDCLState s) ()
{-# INLINE bumpStats #-}
bumpStats update = solverStatsL S.%= update

-- SolverStats contains only unrestricted Int fields, so changing the
-- multiplicity of these instrumentation-only updates is safe.
bumpSeedScan, bumpPostDrainScan, bumpAssignment, bumpTrailAppend, bumpDuplicateEnqueue :: S.State (CDCLState s) ()
bumpSeedScan = bumpStats PL.$ Unsafe.toLinear \stats -> stats {seedScanCount = seedScanCount stats + 1}
bumpPostDrainScan = bumpStats PL.$ Unsafe.toLinear \stats -> stats {postDrainScanCount = postDrainScanCount stats + 1}
bumpAssignment = bumpStats PL.$ Unsafe.toLinear \stats -> stats {assignmentCount = assignmentCount stats + 1}
bumpTrailAppend = bumpStats PL.$ Unsafe.toLinear \stats -> stats {trailAppendCount = trailAppendCount stats + 1}
bumpDuplicateEnqueue = bumpStats PL.$ Unsafe.toLinear \stats -> stats {duplicateEnqueueCount = duplicateEnqueueCount stats + 1}

bumpPropagationEvent, bumpWatchVisit, bumpWatchMove, bumpDecision, bumpConflict :: S.State (CDCLState s) ()
bumpPropagationEvent = bumpStats PL.$ Unsafe.toLinear \stats -> stats {propagationEventCount = propagationEventCount stats + 1}
bumpWatchVisit = bumpStats PL.$ Unsafe.toLinear \stats -> stats {watchVisitCount = watchVisitCount stats + 1}
bumpWatchMove = bumpStats PL.$ Unsafe.toLinear \stats -> stats {watchMoveCount = watchMoveCount stats + 1}
bumpDecision = bumpStats PL.$ Unsafe.toLinear \stats -> stats {decisionCount = decisionCount stats + 1}
bumpConflict = bumpStats PL.$ Unsafe.toLinear \stats -> stats {conflictCount = conflictCount stats + 1}

bumpLiteralInspections :: Int -> S.State (CDCLState s) ()
bumpLiteralInspections count =
  bumpStats PL.$
    Unsafe.toLinear \stats ->
      stats {literalInspectionCount = literalInspectionCount stats + count}

recordBacktrack :: Bool -> Int -> Int -> Int -> Int -> Int -> S.State (CDCLState s) ()
recordBacktrack isRestart boundaryReads trailReads clears valuationReads boundaryProbes =
  bumpStats PL.$
    Unsafe.toLinear \stats ->
      stats
        { backtrackCallCount = backtrackCallCount stats + 1
        , backtrackBoundaryReadCount =
            backtrackBoundaryReadCount stats + boundaryReads
        , backtrackTrailReadCount = backtrackTrailReadCount stats + trailReads
        , backtrackClearedCount = backtrackClearedCount stats + clears
        , backtrackValuationReadCount =
            backtrackValuationReadCount stats + valuationReads
        , backtrackValuationWriteCount = backtrackValuationWriteCount stats + clears
        , backtrackQueueRestoreCount = backtrackQueueRestoreCount stats + clears
        , backtrackBoundaryProbeCount =
            backtrackBoundaryProbeCount stats + boundaryProbes
        , backtrackNoOpCount =
            backtrackNoOpCount stats + if clears == 0 then 1 else 0
        , backtrackMaxSuffix = max (backtrackMaxSuffix stats) clears
        , ordinaryBacktrackCount =
            ordinaryBacktrackCount stats + if isRestart then 0 else 1
        , restartBacktrackCount =
            restartBacktrackCount stats + if isRestart then 1 else 0
        }

bumpRestart :: S.State (CDCLState s) ()
bumpRestart = bumpStats PL.$ Unsafe.toLinear \stats -> stats {observedRestartCount = observedRestartCount stats + 1}
#else
bumpSeedScan, bumpPostDrainScan, bumpAssignment, bumpTrailAppend, bumpDuplicateEnqueue :: S.State (CDCLState s) ()
bumpSeedScan = S.pure ()
bumpPostDrainScan = S.pure ()
bumpAssignment = S.pure ()
bumpTrailAppend = S.pure ()
bumpDuplicateEnqueue = S.pure ()

bumpPropagationEvent, bumpWatchVisit, bumpWatchMove, bumpDecision, bumpConflict :: S.State (CDCLState s) ()
bumpPropagationEvent = S.pure ()
bumpWatchVisit = S.pure ()
bumpWatchMove = S.pure ()
bumpDecision = S.pure ()
bumpConflict = S.pure ()

bumpLiteralInspections :: Int -> S.State (CDCLState s) ()
bumpLiteralInspections _ = S.pure ()

recordBacktrack :: Bool -> Int -> Int -> Int -> Int -> Int -> S.State (CDCLState s) ()
recordBacktrack _ _ _ _ _ _ = S.pure ()

bumpRestart :: S.State (CDCLState s) ()
bumpRestart = S.pure ()
#endif

tryRestart :: forall s. (Reifies s CDCLOptions) => S.State (CDCLState s) RestartResult
{-# INLINE tryRestart #-}
tryRestart = case restartStrategy $ reflect @s Proxy of
  NoRestart -> S.pure Continued
  strat -> S.do
    RestartState count thresh c instrumentation <- S.use restartStateL
    instrumentation `lseq`
      let count' = count + 1
       in if thresh <= count'
            then S.do
              bumpRestart
              restartStateL S.%= nextRestartState strat
              S.pure Restarted
            else S.do
              restartStateL S.%= \(RestartState _ _ _ instrumentation) ->
                RestartState count' thresh c instrumentation
              S.pure Continued
