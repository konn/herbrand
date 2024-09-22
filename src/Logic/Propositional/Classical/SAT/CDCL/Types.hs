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
{-# OPTIONS_GHC -fplugin Foreign.Storable.Generic.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt=Foreign.Storable.Generic.Plugin:-v0 #-}
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
  tryRestart,
) where

import Control.DeepSeq (NFData, force)
import Control.Foldl qualified as Foldl
import Control.Foldl qualified as L
import Control.Functor.Linear qualified as C
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens (Lens', Prism', foldring, lens, prism', (.~))
import Control.Monad (guard)
import Control.Optics.Linear qualified as LinLens
import Data.Array.Mutable.Linear.Extra qualified as LA
import Data.Array.Mutable.Linear.Storable qualified as LSA
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Bifunctor.Linear qualified as BiL
import Data.Bit (Bit (..))
import Data.Bits (popCount, xor, (.&.), (.|.))
import Data.Coerce (coerce)
import Data.Generics.Labels ()
import Data.Hashable (Hashable)
import Data.IntPSQ qualified as PSQ
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.List (mapAccumL)
import Data.List.Linear qualified as LL
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Monoid.Linear.Orphans ()
import Data.Ord (Down (..))
import Data.Proxy (Proxy (..))
import Data.Ref.Linear.ReferenceCount.ThreadUnsafe (Rc, Weak)
import Data.Ref.Linear.ReferenceCount.ThreadUnsafe qualified as RC
import Data.Reflection (Reifies, reflect)
import Data.Semigroup (Max (..))
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
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import Foreign (Storable)
import Foreign.Marshal.Pure.Extra
import Foreign.Storable.Generic (GStorable)
import GHC.Generics (Generic)
import Generics.Linear qualified as L
import Generics.Linear.TH (deriveGeneric)
import Linear.Token.Linearly
import Linear.Token.Linearly.Unsafe (HasLinearWitness, linearWitness)
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
  deriving newtype (Storable, Representable)

derivingUnbox "ClauseId" [t|ClauseId -> Int|] [|unClauseId|] [|ClauseId|]

newtype DecideLevel = DecideLevel {unDecideLevel :: Int}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, Integral, Real, PL.Consumable, PL.Dupable, PL.Movable)
  deriving newtype (Storable, Representable)

instance KnownRepresentable DecideLevel

derivingUnbox "DecideLevel" [t|DecideLevel -> Int|] [|unDecideLevel|] [|DecideLevel|]

newtype Step = Step {unStep :: Word}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (NFData, Hashable, Num, Enum, Integral, Real, PL.Consumable, PL.Dupable, PL.Movable)

derivingUnbox "Step" [t|Step -> Word|] [|unStep|] [|Step|]

-- | Up to 32-bit
newtype Lit = Lit {runLit :: Word}
  deriving (Eq, Ord)
  deriving newtype (Hashable, NFData, PL.Consumable, PL.Dupable, PL.Movable, Storable, Representable)

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

data Clause = Clause
  { lits :: {-# UNPACK #-} !(LSA.SArray Lit)
  , satisfiedAt :: {-# UNPACK #-} !DecideLevel
  , watched1 :: {-# UNPACK #-} !Index
  , watched2 :: {-# UNPACK #-} !Index
  }
  deriving (Generic)
  deriving anyclass (GStorable, KnownRepresentable)

instance Representable Clause where
  type AsKnown Clause = Clause
  ofKnown = PL.id
  toKnown = PL.id

deriveGeneric ''Clause

deriving via L.Generically Clause instance PL.Consumable Clause

deriving via L.Generically Clause instance PL.Dupable Clause

data Variable
  = Definite
      { decideLevel :: {-# UNPACK #-} !DecideLevel
      , decisionStep :: {-# UNPACK #-} !Step
      , antecedent :: !(Maybe (RC.Weak Clause))
      , value :: !Bool
      }
  | Indefinite
  deriving (Generic)

isAssignedAfter :: DecideLevel -> Variable -> Bool
isAssignedAfter _ Indefinite {} = False
isAssignedAfter decLvl Definite {..} = decideLevel > decLvl

deriveGeneric ''Variable

deriving via L.Generically Variable instance PL.Consumable Variable

deriving via L.Generically Variable instance PL.Dupable Variable

derivingUnbox
  "Variable"
  [t|Variable -> (DecideLevel, Step, Weak Clause, Bit)|]
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

type Clauses = [Rc Clause]

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
    {-# UNPACK #-} !Pool %1 ->
    CDCLState s
  deriving anyclass (HasLinearWitness)

clausesL :: LinLens.Lens' (CDCLState s) Clauses
{-# INLINE clausesL #-}
clausesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs pool) ->
  (cs, \cs -> CDCLState numOrig ss cs ws vs vids varQ rs pool)

dupPool :: S.State (CDCLState s) Pool
dupPool = S.state \(CDCLState numOrig ss cs ws vs vids varQ rs pool) ->
  PL.dup pool & \(pool, pool') ->
    (pool', CDCLState numOrig ss cs ws vs vids varQ rs pool)

allocM :: a %1 -> S.State (CDCLState s) (Rc a)
allocM a = RC.alloc a C.<$> dupPool

pushClause :: forall s. (Reifies s CDCLOptions) => Clause -> S.State (CDCLState s) ()
{-# INLINE pushClause #-}
{- HLINT ignore pushClause "Redundant lambda" -}
pushClause = \Clause {..} -> S.do
  (lits0, lits) <- S.pure (PL.dup lits)
  !box <- allocM Clause {..}
  Ur lits <- S.pure (U.convert `Ur.lift` LSA.freeze lits0)
  clausesL S.%= (box :)
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

getClauseLits :: Weak Clause %1 -> (Ur (Maybe (U.Vector Lit)), Weak Clause)
{-# INLINE getClauseLits #-}
getClauseLits cls =
  RC.upgrade cls & \case
    (Nothing, w) -> (Ur Nothing, w)
    (Just cRc, w) ->
      RC.deref cRc & \Clause {..} ->
        LSA.freeze lits & \(Ur lits) ->
          satisfiedAt
            `lseq` watched1
            `lseq` watched2
            `lseq` (Ur (Just $ U.convert lits), w)

foldClauseLits :: L.Fold Lit b -> Weak Clause %1 -> (Ur (Maybe b), Weak Clause)
{-# INLINE foldClauseLits #-}
foldClauseLits f cid =
  BiL.first
    (Ur.lift $ fmap (L.purely (\step ini out -> out . U.foldl step ini) f))
    (getClauseLits cid)

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
  -- FIXME: length is toooo costly
  S.uses clausesL LL.length

stepsL :: LinLens.Lens' (CDCLState s) (LUV.Vector Step)
{-# INLINE stepsL #-}
stepsL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs pool) ->
  (ss, \ss -> CDCLState numOrig ss cs ws vs vids varQ rs pool)

numInitialClausesL :: LinLens.Lens' (CDCLState s) Int
numInitialClausesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs pool) ->
  (numOrig, \numOrig -> CDCLState numOrig ss cs ws vs vids varQ rs pool)

watchesL :: LinLens.Lens' (CDCLState s) WatchMap
{-# INLINE watchesL #-}
watchesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs pool) ->
  (ws, \ws -> CDCLState numOrig ss cs ws vs vids varQ rs pool)

valuationL :: LinLens.Lens' (CDCLState s) Valuation
{-# INLINE valuationL #-}
valuationL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs pool) ->
  (vs, \vs -> CDCLState norig ss cs ws vs vids varQ rs pool)

vsidsStateL :: LinLens.Lens' (CDCLState s) (VSIDSState s)
vsidsStateL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs pool) ->
  (varQ, \varQ -> CDCLState norig ss cs ws vs vids varQ rs pool)

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
unsatisfiedsL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs pool) ->
  (vids, \vids -> CDCLState norig ss cs ws vs vids varQ rs pool)

clausesValsAndUnsatsL :: LinLens.Lens' (CDCLState s) (Clauses, Valuation, LSet.Set ClauseId)
{-# INLINE clausesValsAndUnsatsL #-}
clausesValsAndUnsatsL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs pool) ->
  ((cs, vs, vids), \(cs, vs, vids) -> CDCLState norig ss cs ws vs vids varQ rs pool)

clausesAndValsL :: LinLens.Lens' (CDCLState s) (Clauses, Valuation)
{-# INLINE clausesAndValsL #-}
clausesAndValsL = LinLens.lens \(CDCLState norig ss cs ws vs vids varQ rs pool) ->
  ((cs, vs), \(cs, vs) -> CDCLState norig ss cs ws vs vids varQ rs pool)

extractValuation :: CDCLState s %1 -> Valuation
extractValuation (CDCLState numOrig steps clauses watches vals vids varQs rs pool) =
  numOrig
    `lseq` steps
    `lseq` clauses
    `lseq` watches
    `lseq` vids
    `lseq` varQs
    `lseq` rs
    `lseq` pool
    `lseq` vals

toCDCLState ::
  forall s.
  (Reifies s CDCLOptions) =>
  CNF VarId ->
  Pool %1 ->
  Either (Ur (SatResult ())) (CDCLState s)
toCDCLState (CNF cls) pool =
  linearWitness pool & \(pool, lin) ->
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
        vsidsS =
          VSIDSState
            (PSQ.fromList [(vid, 0, ()) | vid <- [0 .. (numVars - 1)]])
            PSQ.empty
            0
            True
            1.0
        (numOrigCls :!: upds, cls'') = mapAccumL buildClause (0 :!: Map.empty) cls'
        !watches0 = force $ V.toList $ V.update (V.replicate numVars mempty) (V.fromList $ Map.toList upds)
     in case () of
          _
            | truth -> pool `lseq` lin `lseq` Left (Ur (Satisfiable ()))
            | contradicting -> pool `lseq` lin `lseq` Left (Ur Unsat)
          _ ->
            besides lin (LUV.fromListL [0]) PL.& \(steps, lin) ->
              besides lin (toClauses cls'') PL.& \(clauses, lin) ->
                besides lin (LA.fromListL watches0) & \(watcheds, lin) ->
                  besides lin (LUA.allocL (maybe 0 ((+ 1) . fromEnum) maxVar) Indefinite) PL.& \(vals, lin) ->
                    Right
                      PL.$ CDCLState
                        numOrigCls
                        steps
                        clauses
                        watcheds
                        vals
                        (LSet.fromListL [ClauseId 0 .. ClauseId (numOrigCls - 1)] lin)
                        vsidsS
                        rs
                        pool

toClauses :: [Clause] -> Linearly %1 -> Clauses
toClauses = LSV.fromListL

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
setWatchVar :: Weak Clause %1 -> WatchVar %1 -> Index %1 -> Weak Clause
{-# INLINE setWatchVar #-}
setWatchVar cid W1 = Unsafe.toLinear \vid ->
  RC.modify_ (#watched1 .~ vid) cid
setWatchVar cid W2 = Unsafe.toLinear \vid ->
  RC.modify_ (#watched2 .~ vid) cid

setSatisfiedLevel :: Weak Clause %1 -> DecideLevel -> Weak Clause
{-# INLINE setSatisfiedLevel #-}
setSatisfiedLevel cid lvl =
  RC.modify_ (#satisfiedAt .~ lvl) cid

getSatisfiedLevel :: Weak Clause %1 -> (Ur DecideLevel, Weak Clause)
getSatisfiedLevel cid =
  BiL.first (Ur.lift satisfiedAt) (RC.get cid)

data WatchedLits
  = WatchOne {-# UNPACK #-} !Lit
  | WatchThese {-# UNPACK #-} !Lit {-# UNPACK #-} !Lit
  deriving (Show, Eq, Ord, Generic)

deriveGeneric ''WatchedLits

deriving via L.AsMovable WatchedLits instance PL.Consumable WatchedLits

deriving via L.AsMovable WatchedLits instance PL.Dupable WatchedLits

deriving via L.Generically WatchedLits instance PL.Movable WatchedLits

getWatchedLits :: Weak Clause %1 -> (Ur (Maybe WatchedLits), Weak Clause)
getWatchedLits cid =
  RC.upgrade cid & \case
    (Nothing, cid) -> (Ur Nothing, cid)
    (Just rc, cid) ->
      RC.deref rc & \Clause {..} ->
        satisfiedAt
          `lseq` PL.move (watched1, watched2)
          & \(Ur (wat1, wat2)) ->
            LSA.get wat1 lits & \(Ur l1, lits) ->
              (wat2 >= 0) & \case
                True ->
                  LSA.get wat2 lits & \(Ur l2, lits) ->
                    lits `lseq` (Ur (Just (WatchThese l1 l2)), cid)
                False ->
                  lits `lseq` (Ur (Just (WatchOne l1)), cid)

getLit1 :: WatchedLits -> Lit
getLit1 (WatchOne l) = l
getLit1 (WatchThese l _) = l

getLit2 :: WatchedLits -> Maybe Lit
getLit2 WatchOne {} = Nothing
getLit2 (WatchThese _ l) = Just l

watchLitOf :: WatchVar -> WatchedLits -> Lit
watchLitOf W1 = getLit1
watchLitOf W2 = fromMaybe (error "watchLitOf: no lit2") . getLit2

getClauseLitAt :: Weak Clause %1 -> Index -> (Ur (Maybe Lit), Weak Clause)
getClauseLitAt cid j =
  RC.upgrade cid & \case
    (Nothing, cid) -> (Ur Nothing, cid)
    (Just cRc, cid) ->
      RC.deref cRc & \Clause {..} ->
        LSA.get j lits & \(Ur l, lits) ->
          satisfiedAt
            `lseq` lits
            `lseq` watched1
            `lseq` watched2
            `lseq` (Ur (Just l), cid)

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

getWatchedLitIndices :: Weak Clause %1 -> (Ur (Maybe WatchedLitIndices), Weak Clause)
getWatchedLitIndices cid =
  RC.upgrade cid & \case
    (Nothing, cid) -> (Ur Nothing, cid)
    (Just rc, cid) ->
      RC.deref rc & \Clause {..} ->
        satisfiedAt
          `lseq` lits
          `lseq` PL.move (watched1, watched2)
          & \(Ur (wat1, wat2)) ->
            (wat2 >= 0) & \case
              True -> (Ur (Just (WatchOneI wat1)), cid)
              False -> (Ur (Just (WatchTheseI wat1 wat2)), cid)

elemWatchLitIdx :: Index -> WatchedLitIndices -> Bool
elemWatchLitIdx l (WatchOneI l1) = l == l1
elemWatchLitIdx l (WatchTheseI l1 l2) = l == l1 || l == l2

restartStateL :: LinLens.Lens' (CDCLState s) RestartState
{- HLINT ignore restartStateL "Avoid lambda" -}
restartStateL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids varQ rs p) ->
  (rs, \rs -> CDCLState numOrig ss cs ws vs vids varQ rs p)

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
        clausesL
          S.%= LL.map
            ( RC.modify_
                ( \Clause {..} ->
                    satisfiedAt
                      `lseq` Clause {satisfiedAt = -1, ..}
                )
            )
        vsidsStateL S.%= \(VSIDSState unsats sats lbd p i) ->
          VSIDSState
            ( Unsafe.toLinear
                (PSQ.fold' (\l p () x -> PSQ.insert l p () x))
                unsats
                sats
            )
            PSQ.empty
            lbd
            p
            i
        steps0 <- S.state \s -> besides s (LUV.fromListL [0])
        stepsL S..= steps0
        Ur numCls <- getNumClauses
        unsats0 <- S.state \s -> besides s (LSet.fromListL [0 .. fromIntegral $ numCls - 1])
        unsatisfiedsL S..= unsats0
      else restartStateL S..= RestartState count' thresh c
