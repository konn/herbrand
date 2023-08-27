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

module Logic.Propositional.Classical.SAT.CDCL.Types (
  isAssignedAfter,
  toCDCLState,
  CDCLState (..),
  AssertionResult (..),
  Valuation,
  Clauses,
  WatchMap,
  stepsL,
  pushClause,
  getClause,
  getClauseLits,
  getNumClauses,
  setWatchVar,
  setSatisfiedLevel,
  getSatisfiedLevel,
  watchesL,
  clausesL,
  valuationL,
  numInitialClausesL,
  unsatisfiedsL,
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
  getWatchedLits,
  getLit1,
  getLit2,
) where

import Control.DeepSeq (NFData)
import Control.Foldl qualified as Foldl
import Control.Foldl qualified as L
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens (Lens', Prism', lens, prism', (.~))
import Control.Monad (guard)
import Control.Optics.Linear qualified as LinLens
import Data.Alloc.Linearly.Token
import Data.Alloc.Linearly.Token.Unsafe (HasLinearWitness)
import Data.Array.Mutable.Linear.Extra qualified as LA
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Array.Polarized.Push.Extra qualified as Push
import Data.Bit (Bit (..))
import Data.Bits (xor, (.&.), (.|.))
import Data.Coerce (coerce)
import Data.DList qualified as DL
import Data.Foldable qualified as F
import Data.Generics.Labels ()
import Data.Hashable (Hashable)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.List (mapAccumL)
import Data.Map.Strict qualified as Map
import Data.Matrix.Mutable.Linear.Unboxed qualified as LUM
import Data.Maybe (fromMaybe)
import Data.Monoid.Linear.Orphans ()
import Data.Set.Mutable.Linear.Extra qualified as LSet
import Data.Strict.Tuple (Pair (..))
import Data.Unrestricted.Linear (Ur (..))
import Data.Unrestricted.Linear qualified as L
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
import Prelude.Linear (lseq, (&))
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe

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
    -- | Unsatisfied Clauses
    {-# UNPACK #-} !(LSet.Set ClauseId) %1 ->
    CDCLState
  deriving anyclass (HasLinearWitness)

clausesL :: LinLens.Lens' CDCLState Clauses
{-# INLINE clausesL #-}
clausesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids) ->
  (cs, \cs -> CDCLState numOrig ss cs ws vs vids)

pushClause :: Clause -> S.State CDCLState ()
{-# INLINE pushClause #-}
{- HLINT ignore pushClause "Redundant lambda" -}
pushClause = \Clause {..} ->
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

getClause :: ClauseId -> S.State CDCLState (Ur Clause)
{-# INLINE getClause #-}
getClause i = S.uses clausesL \(Clauses litss bs) ->
  LUV.unsafeGet (unClauseId i) bs & \(Ur ClauseBody {..}, bs) ->
    LUM.unsafeGetRow (unClauseId i) litss & \(Ur lits, litss) ->
      ( Ur (Clause {lits, satisfiedAt = satAt, watched1 = wat1, watched2 = wat2})
      , Clauses litss bs
      )

getClauseLits :: ClauseId -> S.State CDCLState (Ur (U.Vector Lit))
getClauseLits i = S.uses clausesL \(Clauses litss bs) ->
  LUM.unsafeGetRow (unClauseId i) litss & \(lits, litss) ->
    (lits, Clauses litss bs)

getNumClauses :: S.State CDCLState (Ur Int)
{-# INLINE getNumClauses #-}
getNumClauses =
  S.uses clausesL \(Clauses litss bs) ->
    LUV.size bs & \(sz, bs) -> (sz, Clauses litss bs)

stepsL :: LinLens.Lens' CDCLState (LUV.Vector Step)
{-# INLINE stepsL #-}
stepsL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids) ->
  (ss, \ss -> CDCLState numOrig ss cs ws vs vids)

numInitialClausesL :: LinLens.Lens' CDCLState Int
numInitialClausesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids) ->
  (numOrig, \numOrig -> CDCLState numOrig ss cs ws vs vids)

watchesL :: LinLens.Lens' CDCLState WatchMap
{-# INLINE watchesL #-}
watchesL = LinLens.lens \(CDCLState numOrig ss cs ws vs vids) ->
  (ws, \ws -> CDCLState numOrig ss cs ws vs vids)

valuationL :: LinLens.Lens CDCLState CDCLState Valuation Valuation
{-# INLINE valuationL #-}
valuationL = LinLens.lens \(CDCLState norig ss cs ws vs vids) ->
  (vs, \vs -> CDCLState norig ss cs ws vs vids)

unsatisfiedsL :: LinLens.Lens' CDCLState (LSet.Set ClauseId)
{-# INLINE unsatisfiedsL #-}
unsatisfiedsL = LinLens.lens \(CDCLState norig ss cs ws vs vids) ->
  (vids, CDCLState norig ss cs ws vs)

clausesValsAndUnsatsL :: LinLens.Lens' CDCLState (Clauses, Valuation, LSet.Set ClauseId)
clausesValsAndUnsatsL = LinLens.lens \(CDCLState norig ss cs ws vs vids) ->
  ((cs, vs, vids), \(cs, vs, vids) -> CDCLState norig ss cs ws vs vids)

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
      numVars = maybe 0 ((+ 1) . fromEnum) maxVar
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
                  Right
                    PL.$ CDCLState numOrigCls steps clauses watcheds vals
                    PL.$ LSet.fromListL lin [ClauseId 0 .. ClauseId (numOrigCls - 1)]

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

deriving via L.Generically CDCLState instance PL.Consumable CDCLState

deriving via L.Generically CDCLState instance PL.Dupable CDCLState

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
setWatchVar :: ClauseId -> WatchVar %1 -> Index %1 -> S.State CDCLState ()
{-# INLINE setWatchVar #-}
setWatchVar cid W1 = Unsafe.toLinear \vid ->
  clausesL S.%= \(Clauses litss bs) ->
    LUV.modify_ (#wat1 .~ vid) (unClauseId cid) bs & \bs ->
      Clauses litss bs
setWatchVar cid W2 = Unsafe.toLinear \vid ->
  clausesL S.%= \(Clauses litss bs) ->
    LUV.modify_ (#wat2 .~ vid) (unClauseId cid) bs & \bs ->
      Clauses litss bs

setSatisfiedLevel :: ClauseId -> DecideLevel -> S.State CDCLState ()
{-# INLINE setSatisfiedLevel #-}
setSatisfiedLevel cid lvl =
  clausesL S.%= \(Clauses litss bs) ->
    LUV.modify_ (#satAt .~ lvl) (unClauseId cid) bs & \bs ->
      Clauses litss bs

getSatisfiedLevel :: ClauseId -> S.State CDCLState (Ur DecideLevel)
getSatisfiedLevel cid =
  S.uses clausesL \(Clauses ls bs) ->
    LUV.unsafeGet (unClauseId cid) bs & \(Ur ClauseBody {..}, bs) ->
      (Ur satAt, Clauses ls bs)

data WatchedLits
  = WatchOne {-# UNPACK #-} !Lit
  | WatchThese {-# UNPACK #-} !Lit !Lit
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
