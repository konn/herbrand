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
  isAssignedAfter,
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
  AssertionResult (..),
  Valuation,
  Clauses,
  WatchMap,
  stepsL,
  pushClause,
  getClauseLits,
  getNumClauses,
  setWatchVar,
  setSatisfiedLevel,
  getSatisfiedLevel,
  withClauseLitsM,
  withClauseLits,
  foldClauseLits,
  watchesL,
  clausesL,
  valuationL,
  vsidsStateL,
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
  ifoldClauseLitsM,
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
  tryRestart,
) where

import Control.Arrow ((&&&))
import Control.DeepSeq (NFData)
import Control.Foldl qualified as Foldl
import Control.Foldl qualified as L
import Control.Functor.Linear qualified as C
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens (Lens', Prism', foldring, lens, prism', (.~))
import Control.Monad (guard)
import Control.Optics.Linear qualified as LinLens
import Data.Alloc.Linearly.Token
import Data.Alloc.Linearly.Token.Unsafe (HasLinearWitness)
import Data.Array.Mutable.Linear.Extra qualified as LA
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Array.Polarized.Push.Extra qualified as Push
import Data.Bifunctor qualified as Bi
import Data.Bifunctor.Linear qualified as BiL
import Data.Bit (Bit (..))
import Data.Bits (popCount, xor, (.&.), (.|.))
import Data.Coerce (coerce)
import Data.DList qualified as DL
import Data.Foldable qualified as F
import Data.Generics.Labels ()
import Data.Hashable (Hashable)
import Data.IntPSQ qualified as PSQ
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.List (mapAccumL)
import Data.Map.Strict qualified as Map
import Data.Matrix.Mutable.Linear.Unboxed qualified as LUM
import Data.Maybe (fromMaybe)
import Data.Monoid.Linear.Orphans ()
import Data.Ord (Down (..))
import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies, reflect)
import Data.Set qualified as Set
import Data.Set.Mutable.Linear.Extra qualified as LSet
import Data.Strict.Tuple (Pair (..))
import Data.Unrestricted.Linear (Ur (..), UrT (..))
import Data.Unrestricted.Linear qualified as L
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Orphans ()
import Data.Vector qualified as V
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as MG
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import GHC.Generics (Generic)
import Generics.Linear qualified as L
import Generics.Linear.TH (deriveGeneric)
import Logic.Propositional.Classical.SAT.Types (SatResult (..))
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Math.NumberTheory.Logarithms (wordLog2')
import Prelude.Linear (lseq, (&))
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe

type RunCount = Word

type RestartAt = Word

type RestartCount = Word

data RestartState where
  RestartState ::
    {-# UNPACK #-} !RunCount ->
    {-# UNPACK #-} !RestartAt ->
    {-# UNPACK #-} !RestartCount ->
    RestartState
  deriving (Show, Eq, Ord, Generic)

deriving via L.AsMovable RestartState instance PL.Consumable RestartState

deriving via L.AsMovable RestartState instance PL.Dupable RestartState

instance PL.Movable RestartState where
  move = Unsafe.toLinear Ur

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
  ExponentialRestart {..} -> \(RestartState _ thresh c) ->
    RestartState 0 (thresh * increaseFactor) (c + 1)
  LubyRestart {..} -> \(RestartState _ _ c) ->
    RestartState 0 (initialRestart * luby c) (c + 1)

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
  ExponentialRestart
    { initialRestart = 100
    , increaseFactor = 2
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

isAssignedAfter :: DecideLevel -> Variable -> Bool
isAssignedAfter _ Indefinite {} = False
isAssignedAfter decLvl Definite {..} = decideLevel > decLvl

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
  , satisfiedAt :: {-# UNPACK #-} !DecideLevel
  , watched1 :: {-# UNPACK #-} !Index
  , watched2 :: {-# UNPACK #-} !Index
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

type Valuation = LUA.UArray Variable

type WatchMap = LA.Array IntSet

data ClauseBody = ClauseBody
  { satAt :: {-# UNPACK #-} !DecideLevel
  , wat1, wat2 :: {-# UNPACK #-} !Index
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
    V_CB len (G.basicUnsafeSlice (off * 3) (len * 3) v)
  {-# INLINE basicUnsafeSlice #-}
  basicUnsafeIndexM = \(V_CB _ v) i -> do
    satAt <- DecideLevel <$> G.basicUnsafeIndexM v (3 * i)
    wat1 <- G.basicUnsafeIndexM v (3 * i + 1)
    wat2 <- G.basicUnsafeIndexM v (3 * i + 2)
    pure $! ClauseBody {..}
  {-# INLINE basicUnsafeIndexM #-}
  basicUnsafeCopy = \(MV_CB _ mv) (V_CB _ v) ->
    G.basicUnsafeCopy mv v
  {-# INLINE basicUnsafeCopy #-}

instance MG.MVector U.MVector ClauseBody where
  basicLength = \(MV_CB l _) -> l
  {-# INLINE basicLength #-}
  basicUnsafeSlice off len = \(MV_CB _ v) ->
    MV_CB len (MG.basicUnsafeSlice (off * 3) (len * 3) v)
  {-# INLINE basicUnsafeSlice #-}
  basicOverlaps = \(MV_CB _ l) (MV_CB _ r) -> MG.basicOverlaps l r
  {-# INLINE basicOverlaps #-}
  basicUnsafeNew l = MV_CB l <$> MG.unsafeNew (3 * l)
  {-# INLINE basicUnsafeNew #-}
  basicInitialize (MV_CB _ l) = MG.basicInitialize l
  {-# INLINE basicInitialize #-}
  basicUnsafeRead (MV_CB _ v) i = do
    satAt <- DecideLevel <$> MG.basicUnsafeRead v (3 * i)
    wat1 <- MG.basicUnsafeRead v (3 * i + 1)
    wat2 <- MG.basicUnsafeRead v (3 * i + 2)
    pure $! ClauseBody {..}
  {-# INLINE basicUnsafeRead #-}
  basicUnsafeWrite (MV_CB _ v) i ClauseBody {..} = do
    MG.basicUnsafeWrite v (3 * i) $ unDecideLevel satAt
    MG.basicUnsafeWrite v (3 * i + 1) wat1
    MG.basicUnsafeWrite v (3 * i + 2) wat2
  {-# INLINE basicUnsafeWrite #-}
  basicClear (MV_CB _ l) = MG.basicClear l
  {-# INLINE basicClear #-}
  basicUnsafeCopy (MV_CB _ dst) (MV_CB _ src) = MG.basicUnsafeCopy dst src
  {-# INLINE basicUnsafeCopy #-}
  basicUnsafeMove (MV_CB _ dst) (MV_CB _ src) = MG.basicUnsafeMove dst src
  {-# INLINE basicUnsafeMove #-}
  basicUnsafeGrow = \(MV_CB l mv) growth ->
    MV_CB (l + growth) <$> MG.basicUnsafeGrow mv (3 * growth)

data Clauses where
  Clauses ::
    {-# UNPACK #-} !(LUM.Matrix Lit) %1 ->
    {-# UNPACK #-} !(LUV.Vector ClauseBody) %1 ->
    Clauses

instance PL.Consumable Clauses where
  consume (Clauses lits bs) = lits `lseq` bs `lseq` ()

instance PL.Dupable Clauses where
  dup2 (Clauses lits bs) =
    PL.dup2 (lits, bs) & \((lits, bs), (lits', bs')) ->
      (Clauses lits bs, Clauses lits' bs')

type VarQueue = PSQ.IntPSQ (Down Double) ()

data UnassignedVars where
  MkUnassignedVars ::
    !(PSQ.IntPSQ (Down Double) Int) ->
    {-# UNPACK #-} !(LUV.Vector VarId) %1 ->
    UnassignedVars

insertUnassigned :: VarId -> Down Double -> UnassignedVars %1 -> UnassignedVars
insertUnassigned v prio (MkUnassignedVars q vids) =
  LUV.size vids & \(Ur i, vids) ->
    LUV.push v vids & \vids ->
      MkUnassignedVars (PSQ.insert (fromIntegral $ unVarId v) prio i q) vids

deleteUnasigedAt :: Int -> UnassignedVars %1 -> (Ur (Maybe (VarId, Down Double)), UnassignedVars)
deleteUnasigedAt i (MkUnassignedVars q vids) =
  LUV.size vids & \(Ur sz, vids) ->
    LUV.pop vids & \(Ur mvLast, vids) ->
      case mvLast of
        Nothing -> (Ur Nothing, MkUnassignedVars q vids)
        Just vLast ->
          i == sz - 1 & \case
            True ->
              -- Just remove the last element and pop
              case PSQ.deleteView (fromIntegral $ unVarId vLast) q of
                Nothing -> (Ur Nothing, MkUnassignedVars q vids)
                Just (prio, _, q) -> (Ur $ Just (vLast, prio), MkUnassignedVars q vids)
            False ->
              -- Removing the variable in-between.
              -- Do not move the rest, just swapping with the last would suffice.
              LUV.get i vids & \(Ur vid, vids) ->
                LUV.set i vLast vids & \vids ->
                  case PSQ.deleteView (fromIntegral $ unVarId vid) q of
                    Nothing -> (Ur Nothing, MkUnassignedVars q vids)
                    Just (prio, _, q) ->
                      ( Ur $ Just (vid, prio)
                      , MkUnassignedVars
                          ( snd
                              $ PSQ.alter
                                (const () &&& fmap (fmap $ const i))
                                (fromIntegral $ unVarId vLast)
                                q
                          )
                          vids
                      )

popUnassignedBy ::
  ( PSQ.IntPSQ (Down Double) Int ->
    Maybe (Int, Down Double, Int, PSQ.IntPSQ (Down Double) Int)
  ) ->
  UnassignedVars %1 ->
  (Ur (Maybe (VarId, Down Double)), UnassignedVars)
popUnassignedBy uncons (MkUnassignedVars q vids) =
  case uncons q of
    Nothing -> (Ur Nothing, MkUnassignedVars q vids)
    Just (vid, prio, i, q) ->
      LUV.size vids & \(Ur sz, vids) ->
        i == sz - 1 & \case
          True ->
            LUV.pop vids & \(Ur _, vids) ->
              (Ur (Just (fromIntegral vid, prio)), MkUnassignedVars q vids)
          False ->
            LUV.pop vids & \case
              (Ur Nothing, vids) -> error "Impossible" vids
              (Ur (Just vLast), vids) ->
                LUV.set i vLast vids & \vids ->
                  ( Ur (Just (fromIntegral vid, prio))
                  , MkUnassignedVars
                      ( snd
                          $ PSQ.alter
                            (const () &&& fmap (fmap $ const i))
                            (fromIntegral $ unVarId vLast)
                            q
                      )
                      vids
                  )

popUnassignedByPrio :: UnassignedVars %1 -> (Ur (Maybe (VarId, Down Double)), UnassignedVars)
{-# INLINE popUnassignedByPrio #-}
popUnassignedByPrio = popUnassignedBy PSQ.minView

popUnassignedVarId :: VarId -> UnassignedVars %1 -> (Ur (Maybe (Down Double)), UnassignedVars)
{-# INLINE popUnassignedVarId #-}
popUnassignedVarId = \vid ->
  popUnassignedBy
    (fmap (\(x, y, z) -> (fromIntegral $ unVarId vid, x, y, z)) <$> PSQ.deleteView (fromIntegral $ unVarId vid))
    C.<&> (\(Ur ma, x) -> (Ur $ snd <$> ma, x))

instance PL.Consumable UnassignedVars where
  consume (MkUnassignedVars _ r) = PL.consume r

instance PL.Dupable UnassignedVars where
  dup2 (MkUnassignedVars l r) =
    BiL.bimap (MkUnassignedVars l) (MkUnassignedVars l) (PL.dup2 r)

type LBD = Double

getDecideLevel :: Variable -> Maybe DecideLevel
getDecideLevel = \case
  Definite {..} -> Just decideLevel
  _ -> Nothing

calcLBDL :: L.FoldM (UrT (S.State Valuation)) Lit Int
calcLBDL =
  L.premapM
    ( \l -> do
        UrT
          $ S.state
            ( BiL.first (Ur.lift getDecideLevel)
                PL.. LUA.unsafeGet (fromIntegral $ unVarId $ litVar l)
            )
    )
    $ L.generalize
      (L.handles L.folded $ Set.size <$> L.set)

data VSIDSState s where
  VSIDSState ::
    -- | Unsatisfieds
    !UnassignedVars %1 ->
    -- | Satisfieds
    !VarQueue ->
    -- | Moving average of LBD (if adaptive mode)
    {-# UNPACK #-} !LBD ->
    -- | True if the last learnt clause exceeds LBD
    !Bool ->
    VSIDSState s

instance PL.Consumable (VSIDSState s) where
  consume (VSIDSState ua _ _ _) = PL.consume ua

instance PL.Dupable (VSIDSState s) where
  dup2 (VSIDSState ua v lbd p) =
    PL.dup2 ua & \(ua, ua') ->
      (VSIDSState ua v lbd p, VSIDSState ua' v lbd p)

data CDCLState s where
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
clausesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs) ->
  (cs, \cs -> CDCLState numOrig ss cs ws vs vids varQ rs)

clauseBodiesL :: LinLens.Lens' Clauses (LUV.Vector ClauseBody)
clauseBodiesL = LinLens.lens \(Clauses lits bodies) ->
  (bodies, \bodies -> Clauses lits bodies)

pushClause :: forall s. (Reifies s CDCLOptions) => Clause -> S.State (CDCLState s) ()
{-# INLINE pushClause #-}
{- HLINT ignore pushClause "Redundant lambda" -}
{- HLINT ignore pushClause "Avoid lambda" -}
pushClause = \Clause {..} -> S.do
  clausesL S.%= \(Clauses litss bs) ->
    LUV.push
      ClauseBody
        { satAt = satisfiedAt
        , wat1 = watched1
        , wat2 = watched2
        }
      bs
      & \bs ->
        LUM.pushRow lits litss & \litss -> Clauses litss bs
  Ur !lbd <- S.zoom valuationL (Ur.runUrT (L.foldOverM (foldring U.foldr) calcLBDL lits))
  vsidsStateL
    S.%= case decayFactor $ reflect @s Proxy of
      ConstantFactor {} -> \(VSIDSState unsats sats ema x) ->
        VSIDSState
          (Unsafe.toLinear (U.foldl' (\uns l -> incrementUnsatVar l uns)) unsats lits)
          (U.foldr incrementVar sats lits)
          ema
          x
      Adaptive {..} -> \(VSIDSState unsats sats ema _) ->
        let ema' = ema * lbdEmaDecayFactor + fromIntegral lbd * (1 - lbdEmaDecayFactor)
         in VSIDSState
              (Unsafe.toLinear (U.foldl' (\uns l -> incrementUnsatVar l uns)) unsats lits)
              (U.foldr incrementVar sats lits)
              ema'
              (fromIntegral lbd >= ema')
  S.pure ()

decayVarPriosM :: forall s. (Reifies s CDCLOptions) => S.State (VSIDSState s) ()
{-# INLINE decayVarPriosM #-}
decayVarPriosM = S.modify \(VSIDSState ls qs spec exc) ->
  case decayFactor (reflect $ Proxy @s) of
    ConstantFactor alpha -> VSIDSState (decayUnsatVars alpha ls) (decayVars alpha qs) spec exc
    Adaptive {..}
      | exc -> VSIDSState (decayUnsatVars highLBDDecay ls) (decayVars highLBDDecay qs) spec exc
      | otherwise -> VSIDSState (decayUnsatVars lowLBDDecay ls) (decayVars lowLBDDecay qs) spec exc

-- Adaptive {..} -> VSIDSState (decayVars alpha ls) (decayVars alpha qs) spec

decayVars :: Double -> PSQ.IntPSQ (Down Double) v -> PSQ.IntPSQ (Down Double) v
{-# INLINE decayVars #-}
decayVars = \alpha -> PSQ.unsafeMapMonotonic \_ (Down p) v -> (Down $ p * alpha, v)

decayUnsatVars :: Double -> UnassignedVars %1 -> UnassignedVars
{-# INLINE decayUnsatVars #-}
decayUnsatVars = \alpha (MkUnassignedVars q w) ->
  MkUnassignedVars (decayVars alpha q) w

findUnsatVar :: S.State (VSIDSState s) (Ur (Maybe VarId))
findUnsatVar = S.state \(VSIDSState unsat sat lbdEma exc) ->
  popUnassignedByPrio unsat & \case
    (Ur (Just (k, p)), unsat) ->
      ( Ur $ Just k
      , VSIDSState unsat (PSQ.unsafeInsertNew (fromIntegral $ unVarId k) p () sat) lbdEma exc
      )
    (Ur Nothing, unsat) -> (Ur Nothing, VSIDSState unsat sat lbdEma exc)

incrementVarM :: Lit -> S.State (VSIDSState s) ()
incrementVarM l = S.modify \(VSIDSState unsats sats lbdEma exc) ->
  VSIDSState
    (incrementUnsatVar l unsats)
    (incrementVar l sats)
    lbdEma
    exc

incrementUnsatVar :: Lit -> UnassignedVars %1 -> UnassignedVars
incrementUnsatVar l (MkUnassignedVars q u) =
  MkUnassignedVars (incrementVar l q) u

incrementVar :: Lit -> PSQ.IntPSQ (Down Double) v -> PSQ.IntPSQ (Down Double) v
incrementVar =
  fmap snd
    . PSQ.alter (((),) . fmap (Bi.first (+ 1)))
    . fromIntegral
    . unVarId
    . litVar

moveToSatQueue :: VarId -> VSIDSState s %1 -> VSIDSState s
moveToSatQueue vid = \(VSIDSState unsats sats lbdEma exc) ->
  popUnassignedVarId vid unsats & \case
    (Ur Nothing, unsats) -> VSIDSState unsats sats lbdEma exc
    (Ur (Just p), unsats) ->
      VSIDSState unsats (PSQ.unsafeInsertNew vidInt p () sats) lbdEma exc
  where
    !vidInt = fromIntegral $ unVarId vid

moveToUnsatQueue :: VarId -> VSIDSState s %1 -> VSIDSState s
moveToUnsatQueue vid = \(VSIDSState unsats sats lbdEma exc) ->
  case PSQ.deleteView vidInt sats of
    Nothing -> VSIDSState unsats sats lbdEma exc
    Just (p, (), sats) ->
      VSIDSState (insertUnassigned vid p unsats) sats lbdEma exc
  where
    !vidInt = fromIntegral $ unVarId vid

getClauseLits :: ClauseId -> S.State (CDCLState s) (Ur (U.Vector Lit))
getClauseLits i = S.uses clausesL \(Clauses litss bs) ->
  LUM.unsafeGetRow (unClauseId i) litss & \(lits, litss) ->
    (lits, Clauses litss bs)

withClauseLitsM ::
  ClauseId ->
  (forall s. LUM.Slice s Lit %1 -> (b, LUM.Slice s Lit)) %1 ->
  S.State Clauses b
{-# INLINE withClauseLitsM #-}
withClauseLitsM cid f = S.state \(Clauses litss bs) ->
  LUM.unsafeWithRow (unClauseId cid) f litss & \(b, litss) ->
    (b, Clauses litss bs)

withClauseLits ::
  ClauseId ->
  Clauses %1 ->
  (forall s. LUM.Slice s Lit %1 -> (b, LUM.Slice s Lit)) %1 ->
  (b, Clauses)
{-# INLINE withClauseLits #-}
withClauseLits cid = \(Clauses litss bs) f ->
  LUM.unsafeWithRow (unClauseId cid) f litss & \(b, litss) ->
    (b, Clauses litss bs)

foldClauseLits :: L.Fold Lit b -> ClauseId -> S.State Clauses (Ur b)
{-# INLINE foldClauseLits #-}
foldClauseLits f cid = withClauseLitsM cid (L.purely LUV.foldS' f)

ifoldClauseLitsM :: (C.Monad m) => L.FoldM (UrT m) (Int, Lit) b -> ClauseId -> S.StateT Clauses m (Ur b)
{-# INLINE ifoldClauseLitsM #-}
ifoldClauseLitsM f cid = S.StateT \(Clauses litss bs) ->
  C.fmap (`Clauses` bs)
    C.<$> LUM.unsafeWithRowM
      (unClauseId cid)
      (L.impurely LUV.ifoldSML' f)
      litss

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

stepsL :: LinLens.Lens' (CDCLState s) (LUV.Vector Step)
{-# INLINE stepsL #-}
stepsL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs) ->
  (ss, \ss -> CDCLState numOrig ss cs ws vs vids varQ rs)

numInitialClausesL :: LinLens.Lens' (CDCLState s) Int
numInitialClausesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs) ->
  (numOrig, \numOrig -> CDCLState numOrig ss cs ws vs vids varQ rs)

watchesL :: LinLens.Lens' (CDCLState s) WatchMap
{-# INLINE watchesL #-}
watchesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs) ->
  (ws, \ws -> CDCLState numOrig ss cs ws vs vids varQ rs)

valuationL :: LinLens.Lens' (CDCLState s) Valuation
{-# INLINE valuationL #-}
valuationL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs) ->
  (vs, \vs -> CDCLState norig ss cs ws vs vids varQ rs)

vsidsStateL :: LinLens.Lens' (CDCLState s) (VSIDSState s)
vsidsStateL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs) ->
  (varQ, \varQ -> CDCLState norig ss cs ws vs vids varQ rs)

unsatisfiedsL :: LinLens.Lens' (CDCLState s) (LSet.Set ClauseId)
{-# INLINE unsatisfiedsL #-}
unsatisfiedsL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs) ->
  (vids, \vids -> CDCLState norig ss cs ws vs vids varQ rs)

clausesValsAndUnsatsL :: LinLens.Lens' (CDCLState s) (Clauses, Valuation, LSet.Set ClauseId)
{-# INLINE clausesValsAndUnsatsL #-}
clausesValsAndUnsatsL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs) ->
  ((cs, vs, vids), \(cs, vs, vids) -> CDCLState norig ss cs ws vs vids varQ rs)

clausesAndValsL :: LinLens.Lens' (CDCLState s) (Clauses, Valuation)
{-# INLINE clausesAndValsL #-}
clausesAndValsL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs) ->
  ((cs, vs), \(cs, vs) -> CDCLState norig ss cs ws vs vids varQ rs)

extractValuation :: CDCLState s %1 -> Valuation
extractValuation (CDCLState numOrig steps clauses watches vals vids varQs rs) =
  numOrig
    `lseq` steps
    `lseq` clauses
    `lseq` watches
    `lseq` vids
    `lseq` varQs
    `lseq` rs
    `lseq` vals

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
      rs = RestartState 0 (fromMaybe 0 $ getInitRestart restartOpt) 0
      (numOrigCls :!: upds, cls'') = mapAccumL buildClause (0 :!: Map.empty) cls'
      watches0 = V.toList $ V.update (V.replicate numVars mempty) (V.fromList $ Map.toList upds)
   in case () of
        _
          | truth -> lin `lseq` Left (Ur $ Satisfiable ())
          | contradicting -> lin `lseq` Left (Ur Unsat)
        _ ->
          besides lin (`LUV.fromListL` [0]) PL.& \(steps, lin) ->
            besides lin (toClauses cls'') PL.& \(clauses, lin) ->
              besides lin (`LA.fromListL` watches0) & \(watcheds, lin) ->
                besides lin (\lin -> LUA.allocL lin (maybe 0 ((+ 1) . fromEnum) maxVar) Indefinite) PL.& \(vals, lin) ->
                  besides
                    lin
                    ( `LUV.fromListL`
                        [fromIntegral i | i <- [0 .. numVars - 1]]
                    )
                    PL.& \(varIdcs, lin) ->
                      Right
                        PL.$ CDCLState
                          numOrigCls
                          steps
                          clauses
                          watcheds
                          vals
                          (LSet.fromListL lin [ClauseId 0 .. ClauseId (numOrigCls - 1)])
                          ( VSIDSState
                              ( MkUnassignedVars
                                  (PSQ.fromList [(vid, 0, vid) | vid <- [0 .. (numVars - 1)]])
                                  varIdcs
                              )
                              PSQ.empty
                              0
                              True
                          )
                          rs

toClauses :: [Clause] -> Linearly %1 -> Clauses
toClauses cs l =
  PL.dup2 l & \(l, l') ->
    F.foldMap'
      ( \Clause {..} ->
          ( Ur (DL.singleton lits)
          , Push.singleton ClauseBody {satAt = satisfiedAt, wat1 = watched1, wat2 = watched2}
          )
      )
      cs
      & \(Ur lits, bs) ->
        Clauses
          (LUM.fromRowsL l (DL.toList lits))
          (LUV.fromVectorL l' (Push.alloc bs))

buildClause ::
  Pair Int (Map.Map Int IntSet) ->
  [Lit] ->
  (Pair Int (Map.Map Int IntSet), Clause)
buildClause (i :!: watches) [] =
  (i :!: watches, Clause {lits = mempty, satisfiedAt = -1, watched1 = -1, watched2 = -1})
buildClause (i :!: watches) [x] =
  ( (i + 1) :!: Map.insertWith IS.union (fromEnum $ litVar x) (IS.singleton i) watches
  , Clause {lits = U.singleton x, satisfiedAt = -1, watched1 = 0, watched2 = -1}
  )
buildClause (i :!: watches) xs =
  ( i
      + 1
      :!: Map.insertWith
        IS.union
        (fromEnum $ litVar $ head xs)
        (IS.singleton i)
        ( Map.insertWith
            IS.union
            (fromEnum $ litVar $ xs !! 1)
            (IS.singleton i)
            watches
        )
  , Clause {lits = U.fromList xs, satisfiedAt = -1, watched1 = 0, watched2 = 1}
  )

deriveGeneric ''CDCLState

deriving via L.Generically (CDCLState s) instance PL.Consumable (CDCLState s)

data WatchVar = W1 | W2 deriving (Show, Eq, Ord, Generic)

deriveGeneric ''WatchVar

deriving via L.AsMovable WatchVar instance PL.Consumable WatchVar

deriving via L.AsMovable WatchVar instance PL.Dupable WatchVar

deriving via L.Generically WatchVar instance PL.Movable WatchVar

data UnitResult
  = Unit {-# UNPACK #-} !Lit
  | Conflict {-# UNPACK #-} !Lit
  | -- | Optional 'Pair' records possible old watched variable and new variable.
    Satisfied !(Maybe (Pair (Pair WatchVar VarId) (Pair VarId Index)))
  | WatchChangedFromTo !WatchVar {-# UNPACK #-} !VarId {-# UNPACK #-} !VarId {-# UNPACK #-} !Index
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

data AssertionResult = Asserted | ContradictingAssertion
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

setSatisfiedLevel :: ClauseId -> DecideLevel -> S.State (CDCLState s) ()
{-# INLINE setSatisfiedLevel #-}
setSatisfiedLevel cid lvl =
  clausesL S.%= \(Clauses litss bs) ->
    LUV.modify_ (#satAt .~ lvl) (unClauseId cid) bs & \bs ->
      Clauses litss bs

getSatisfiedLevel :: ClauseId -> S.State (CDCLState s) (Ur DecideLevel)
getSatisfiedLevel cid =
  S.uses clausesL \(Clauses ls bs) ->
    LUV.unsafeGet (unClauseId cid) bs & \(Ur ClauseBody {..}, bs) ->
      (Ur satAt, Clauses ls bs)

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
    LUM.unsafeGetEntry (unClauseId cid) wat1 ls & \(Ur l1, ls) ->
      wat2 >= 0 & \case
        True ->
          LUM.unsafeGetEntry (unClauseId cid) wat2 ls & \(Ur l2, ls) ->
            (Ur (WatchThese l1 l2), Clauses ls bs)
        False ->
          (Ur (WatchOne l1), Clauses ls bs)

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
  LUM.unsafeGetEntry (unClauseId cid) j ls & \(Ur l1, ls) ->
    (Ur l1, Clauses ls bs)

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

getWatchedLitIndices :: ClauseId -> S.State Clauses (Ur WatchedLitIndices)
getWatchedLitIndices cid = S.state \(Clauses ls bs) ->
  LUV.unsafeGet (unClauseId cid) bs & \(Ur ClauseBody {..}, bs) ->
    wat2 >= 0 & \case
      True -> (Ur (WatchTheseI wat1 wat2), Clauses ls bs)
      False ->
        (Ur (WatchOneI wat1), Clauses ls bs)

elemWatchLitIdx :: Index -> WatchedLitIndices -> Bool
elemWatchLitIdx l (WatchOneI l1) = l == l1
elemWatchLitIdx l (WatchTheseI l1 l2) = l == l1 || l == l2

restartStateL :: LinLens.Lens' (CDCLState s) RestartState
{- HLINT ignore restartStateL "Avoid lambda" -}
restartStateL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs) ->
  (rs, \rs -> CDCLState numOrig ss cs ws vs vids varQ rs)

tryRestart :: forall s. (Reifies s CDCLOptions) => S.State (CDCLState s) ()
{-# INLINE tryRestart #-}
tryRestart = case restartStrategy $ reflect @s Proxy of
  NoRestart -> S.pure ()
  strat -> S.do
    RestartState count thresh c <- S.use restartStateL
    let count' = count + 1
    if thresh <= count'
      then S.do
        valuationL S.%= LUA.map (const Indefinite)
        restartStateL S.%= nextRestartState strat
        (clausesL LinLens..> clauseBodiesL) S.%= PL.flip LUV.map \cf -> cf {satAt = -1}
        vsidsStateL S.%= \(VSIDSState unsats sats lbd p) ->
          VSIDSState
            ( Unsafe.toLinear
                (PSQ.fold' (\l p () x -> insertUnassigned (fromIntegral l) p x))
                unsats
                sats
            )
            PSQ.empty
            lbd
            p
        steps0 <- S.state \s -> besides s (`LUV.fromListL` [0])
        stepsL S..= steps0
        Ur numCls <- getNumClauses
        unsats0 <- S.state \s -> besides s (`LSet.fromListL` [0 .. fromIntegral $ numCls - 1])
        unsatisfiedsL S..= unsats0
      else restartStateL S..= RestartState count' thresh c
