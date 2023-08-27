{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | DPLL Algorithm, supercharged with Conflict-Driven Clause Learning (CDCL).
module Logic.Propositional.Classical.SAT.CDCL (
  solve,
  solveVarId,
  solveState,
  propagateUnit,

  -- * Re-exports
  CNF (..),
  CNFClause (..),
  Literal (..),
  VarId (..),
) where

import Control.Applicative
import Control.Arrow ((>>>))
import Control.Foldl qualified as L
import Control.Functor.Linear qualified as C
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens hiding (Index, lens, (%=), (&), (.=))
import Control.Lens qualified as Lens
import Control.Lens.Extras qualified as Lens
import Control.Monad (guard)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Optics.Linear qualified as LinOpt
import Data.Alloc.Linearly.Token (besides, linearly)
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Bifunctor.Linear qualified as BiL
import Data.Coerce (coerce)
import Data.Foldable qualified as Foldable
import Data.Function (fix)
import Data.Functor.Linear qualified as D
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as LHM
import Data.HashSet qualified as HS
import Data.Hashable
import Data.IntSet qualified as IS
import Data.Maybe qualified as P
import Data.Semigroup (Arg (..), Max (..))
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Mutable.Linear.Extra qualified as LSet
import Data.Strict (Pair (..))
import Data.Strict.Classes qualified as St
import Data.Strict.Maybe qualified as St
import Data.Tuple qualified as P
import Data.Unrestricted.Linear (UrT (..), liftUrT, runUrT)
import Data.Unrestricted.Linear qualified as Ur
import Data.Vector.Generic.Lens (vectorTraverse)
import Data.Vector.Mutable.Linear.Helpers qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Debug.Trace.Lienar.Extra qualified as DT
import GHC.Generics qualified as GHC
import Logic.Propositional.Classical.SAT.CDCL.Types
import Logic.Propositional.Classical.SAT.Types
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Prelude.Linear hiding (not, (&&), (+), (-), (.), (/=), (<), (<>), (==), (>), (>=), (||))
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe
import Prelude hiding (uncurry, ($))
import Prelude qualified as P

data FinalState = Ok | Failed
  deriving (Show, P.Eq, P.Ord, GHC.Generic)

solve :: (LHM.Keyed a) => CNF a -> SatResult (Model a)
{-# INLINE [1] solve #-}
{-# ANN solve "HLint: ignore Avoid lambda" #-}
solve cnf = unur $ LHM.empty 128 \dic ->
  besides dic (`LHM.emptyL` 128) & \(rev, dic) ->
    S.runState
      (runUrT (traverse (\v -> liftUrT (renameCNF v)) cnf))
      ((rev, Ur 0), dic)
      & \(Ur cnf, ((dic, Ur _), rev)) ->
        dic
          `lseq` besides rev (toCDCLState cnf)
          & \case
            (Left (Ur resl), rev) ->
              rev `lseq` Ur (P.mempty P.<$ resl)
            (Right state, rev) ->
              solveState state & \case
                (Ur Unsat) -> rev `lseq` Ur Unsat
                (Ur (Satisfiable m)) ->
                  Satisfiable D.<$> S.evalState (unrenameModel m) rev

unrenameModel ::
  (Hashable a) =>
  Model VarId ->
  S.State (LHM.HashMap VarId a) (Ur (Model a))
unrenameModel (Model pos neg) = S.do
  Ur !positive <- backHS pos
  Ur !negative <- backHS neg
  S.pure $ Ur Model {..}

backHS ::
  (Hashable a) =>
  HS.HashSet VarId ->
  S.StateT (LHM.HashMap VarId a) Identity (Ur (HS.HashSet a))
{-# INLINE backHS #-}
backHS vs =
  C.fmap (Ur.lift HS.fromList)
    $ runUrT
    $ traverse
      ( \v ->
          UrT
            $ S.state
            $ \dic ->
              BiL.first
                ( D.fmap
                    ( fromMaybe
                        ( error
                            $ "unrenameModel: variable out of bound: "
                            P.<> show v
                        )
                    )
                )
                $ LHM.lookup v dic
      )
    $ HS.toList vs

renameCNF :: (LHM.Keyed a) => a -> S.State ((LHM.HashMap a VarId, Ur VarId), LHM.HashMap VarId a) VarId
renameCNF a = S.do
  Ur m <- S.uses (LinOpt._1 LinOpt..> LinOpt._1) $ LHM.lookup a
  case m of
    Just a -> S.pure a
    Nothing -> S.do
      Ur i <- S.uses (LinOpt._1 LinOpt..> LinOpt._2) \(Ur i) ->
        (Ur i, Ur (i + 1))
      (LinOpt._1 LinOpt..> LinOpt._1) S.%= LHM.insert a i
      LinOpt._2 S.%= LHM.insert i a
      S.pure i

{-# RULES "solve/VarId" solve = solveVarId #-}

solveVarId :: CNF VarId -> SatResult (Model VarId)
solveVarId cnf =
  unur PL.$ linearly \l ->
    toCDCLState cnf l PL.& \case
      Left (Ur resl) -> Ur (P.mempty P.<$ resl)
      Right stt -> solveState stt

solveState :: CDCLState %1 -> Ur (SatResult (Model VarId))
solveState = toSatResult PL.. S.runState (solverLoop Nothing)

solverLoop :: Maybe (Lit, ClauseId) -> S.State CDCLState FinalState
solverLoop = fix $ \go mlit -> S.do
  DT.traceStackM $ "Loop: New decision: " <> show mlit
  -- First, check if the original clauses are all satisfied (at the current stage)
  -- We only have to traverse the initial segment, as the lerant clauses are always
  -- deducible from the original clauses.
  -- Without this, CDCL solver seems at most x1000 slower than DPLL and even Naïve tableaux...
  Ur numIniCls <- move C.<$> S.use numInitialClausesL

  Ur vals <- S.uses valuationL $ BiL.first LUA.freeze PL.. dup2
  DT.traceStackM $ "Traversing first " <> show numIniCls <> " clauses for satcheck"
  DT.traceStackM $ "Current valuation: " <> show vals
  Ur mstt <-
    fix
      ( \self !i -> S.do
          (i == numIniCls) & \case
            True -> S.do
              DT.traceStackM "All the clauses true!"
              S.pure $ Ur True
            False -> S.do
              Ur c <- S.uses clausesL $ LV.unsafeGet i
              DT.traceStackM $ "Checking eval clause: " <> show (i, c)
              Ur val <- S.zoom valuationL (evalClause c)
              DT.traceStackM $ "Clause value: " <> show (i, val)
              val & \case
                Just True -> S.do
                  unsatisfiedsL S.%= LSet.delete (ClauseId i)
                  self PL.$! i + 1
                Just False -> S.do
                  DT.traceStackM "Falsity found! Ignores, but reporting not satisified"
                  S.pure $ Ur False
                Nothing -> S.do
                  DT.traceStackM "Unassigned value found. Returning."
                  S.pure $ Ur False
      )
      0
  DT.traceStackM $ "Satisfiedness check: " <> show mstt
  -- S.uses clausesL $ LV.allFirstN numIniCls ((>= 0) . satisfiedAt)
  mstt & \case
    True -> S.pure Ok
    -- Contracdiction! The last assigned variable must be
    False -> S.do
      Ur resl <- propagateUnit mlit
      case resl of
        ConflictFound cid l -> backjump cid l -- Conflict found. Let's Backjump!
        NoMorePropagation -> S.do
          -- Decide indefinite variable
          -- FIXME: Use heuristics for variable selection.
          Ur mid <- S.uses valuationL (LUA.findIndex (Lens.is #_Indefinite))
          case mid of
            Nothing -> S.pure Ok -- No vacant variable - model is full!
            Just vid -> S.do
              stepsL S.%= LUV.push 0
              let decLit = PosL $ toEnum vid
              assResult <- assertLit (-1) decLit
              case assResult of
                Asserted -> go (Just (decLit, -1))
                ContradictingAssertion -> error $ "Impossible: decide variable is contradicting!: " <> show decLit

backjump :: ClauseId -> Lit -> S.State CDCLState FinalState
backjump confCls lit = S.do
  Ur c <- S.uses clausesL $ LV.unsafeGet $ fromEnum confCls
  Ur mLearnt <- findUIP1 lit $ L.foldOver (Lens.foldring U.foldr) L.set $ lits c
  case mLearnt of
    Nothing ->
      -- No valid backjumping destination found. Unsat.
      S.pure Failed
    Just (decLvl, mlearnt, truth) -> S.do
      Ur numCls <- S.uses clausesL LV.size
      fix
        ( \self !i ->
            if i == numCls
              then S.pure ()
              else S.do
                Ur Clause {..} <- S.uses clausesL $ LV.unsafeGet i
                satisfiedAt > decLvl & \case
                  True -> S.do
                    clausesL S.%= LV.modify_ (\c -> c {satisfiedAt = -1}) i
                    unsatisfiedsL S.%= LSet.insert (ClauseId i)
                  False -> S.pure ()
                self (i + 1)
        )
        0

      Ur reason <- case mlearnt of
        Just learnt -> S.do
          stepsL S.%= LUV.slice 0 (unDecideLevel decLvl + 1)
          clausesL S.%= LV.push learnt
          Ur reason <- Ur.lift (fromIntegral . subtract 1) C.<$> S.uses clausesL LV.size
          watch reason $ litVar (lits learnt U.! watched1 learnt)
          if watched2 learnt >= 0
            then watch reason $ litVar (lits learnt U.! watched2 learnt)
            else S.pure ()
          S.pure $ Ur reason
        Nothing -> S.pure $ Ur confCls

      valuationL S.%= LUA.mapSame \v ->
        PL.move v & \(Ur v) ->
          if isAssignedAfter decLvl v
            then Indefinite
            else v

      C.void $ assertLit reason truth
      solverLoop $ Just (truth, reason)

findUIP1 ::
  Lit ->
  Set Lit ->
  S.State CDCLState (Ur (Maybe (DecideLevel, Maybe Clause, Lit)))
findUIP1 !lit !curCls
  | Set.null curCls = S.pure $ Ur Nothing
  | otherwise = S.do
      ml <- checkUnitClauseLit curCls
      case ml of
        Ur (Just (l', decLvl)) ->
          -- Already Unit clause. Learn it!
          S.pure
            $ Ur
            $ Just
            $ mkLearntClause decLvl l' curCls
        Ur Nothing -> S.do
          -- Not a UIP. resolve.
          Ur v <- S.uses valuationL $ LUA.unsafeGet $ fromEnum $ litVar lit
          case v of
            Indefinite -> error $ "Literal " P.<> show lit P.<> " was chosen as resolver, but indefinite!"
            Definite {..} -> S.do
              Ur cls' <- case antecedent of
                Just ante ->
                  Ur.lift (L.foldOver (Lens.foldring U.foldr) L.set . lits)
                    D.<$> S.uses clausesL (LV.unsafeGet (fromEnum ante))
                Nothing -> S.pure $ Ur Set.empty
              let resolved = resolve lit curCls cls'
              if Set.null resolved
                then S.pure $ Ur Nothing -- Conflicting clause
                else S.do
                  Ur mlit' <- findConflictingLit resolved
                  case mlit' of
                    Just lit' -> findUIP1 lit' resolved
                    Nothing -> S.do
                      Ur lvl <- currentDecideLevel
                      -- the literal is decision variable
                      S.pure
                        $ Ur
                        $ Just
                          (lvl - 1, Nothing, lit)

mkLearntClause :: DecideLevel -> Lit -> Set Lit -> (DecideLevel, Maybe Clause, Lit)
mkLearntClause decLvl l' curCls =
  let cls' = U.cons l' $ L.fold L.vector $ Set.delete l' curCls
   in ( decLvl
      , Just
          Clause
            { watched2 = if U.length cls' > 1 then 1 else -1
            , watched1 = 0
            , satisfiedAt = decLvl
            , lits = cls'
            }
      , l'
      )

findConflictingLit :: (Foldable t) => t Lit -> S.State CDCLState (Ur (Maybe Lit))
findConflictingLit lits = S.uses valuationL \vals ->
  foldlLin'
    vals
    ( \vals !mn !l ->
        LUA.unsafeGet (fromEnum $ litVar l) vals & \(Ur var, vals) ->
          let intro = introduced var
           in ( Ur.lift (P.<> Max (Arg intro (St.Just l))) mn
              , vals
              )
    )
    (Max (Arg (-1 :!: -1) St.Nothing))
    lits
    PL.& BiL.first (Ur.lift \(Max (Arg _ l)) -> St.toLazy l)

resolve :: Lit -> Set Lit -> Set Lit -> Set Lit
resolve lit l r =
  Set.filter ((/= litVar lit) . litVar) l
    P.<> Set.filter ((/= litVar lit) . litVar) r

data ULS = ULS
  { _ulCount :: {-# UNPACK #-} !Int
  , _mcand :: !(St.Maybe Lit)
  , _latestDec :: {-# UNPACK #-} !DecideLevel
  , _penultimateDec :: {-# UNPACK #-} !DecideLevel
  }
  deriving (Show)

checkUnitClauseLit :: Set Lit -> S.State CDCLState (Ur (Maybe (Lit, DecideLevel)))
checkUnitClauseLit ls = S.do
  Ur lvl <- currentDecideLevel
  Ur lcnd <- S.uses valuationL \vals ->
    foldlLin'
      vals
      ( \vals (Ur (ULS count mcand large small)) lit ->
          LUA.unsafeGet (fromEnum (litVar lit)) vals & \(Ur var, vals) ->
            case var of
              Definite {..} ->
                let (large', small')
                      | decideLevel > large = (decideLevel, large)
                      | decideLevel == large = (large, small)
                      | decideLevel > small = (large, decideLevel)
                      | otherwise = (large, small)
                    (count', mcand') =
                      if decideLevel P.>= lvl
                        then (count + 1, St.maybe (St.Just lit) St.Just mcand)
                        else (count, mcand)
                 in (Ur (ULS count' mcand' large' small'), vals)
              _ -> (Ur (ULS count mcand large small), vals)
      )
      (ULS 0 St.Nothing (-1) (-2))
      ls
  S.pure $ case lcnd of
    (ULS 1 mx _ pu) | pu >= 0 -> Ur $ (,pu) <$> St.toLazy mx
    _ -> Ur Nothing

foldlLin' :: (Foldable.Foldable t) => b %1 -> (b %1 -> Ur x -> a -> (Ur x, b)) -> x -> t a -> (Ur x, b)
foldlLin' b f x =
  Unsafe.toLinear
    (P.fmap (Foldable.foldl' (P.uncurry $ P.flip (forget f))) . P.flip (,))
    b
    (Ur x)

currentDecideLevel :: S.State CDCLState (Ur DecideLevel)
currentDecideLevel =
  Ur.lift (fromIntegral P.. P.subtract 1)
    D.<$> S.uses stepsL LUV.size

toSatResult :: (FinalState, CDCLState) %1 -> Ur (SatResult (Model VarId))
toSatResult (Failed, state) = state `lseq` Ur Unsat
toSatResult (Ok, CDCLState numOrig steps clauses watches vals vids) =
  numOrig
    `lseq` steps
    `lseq` clauses
    `lseq` watches
    `lseq` vids
    `lseq` ( LUA.freeze vals & Ur.lift do
              Satisfiable
                . Lens.foldMapOf
                  (Lens.foldring U.foldr)
                  ( \(k, var) ->
                      case var of
                        Definite {..} ->
                          if value
                            then P.mempty {positive = HS.singleton $ fromIntegral k}
                            else P.mempty {negative = HS.singleton $ fromIntegral k}
                        Indefinite -> P.mempty
                  )
                . U.indexed
           )

toClauseId :: Int -> ClauseId
toClauseId = fromIntegral

propagateUnit :: Maybe (Lit, ClauseId) -> S.State CDCLState (Ur PropResult)
propagateUnit ml = S.do
  go (P.maybe Seq.empty Seq.singleton ml)
  where
    go :: Seq.Seq (Lit, ClauseId) -> S.State CDCLState (Ur PropResult)
    go ((l, reason) :<| rest) = S.do
      assResl <- assertLit reason l
      case assResl of
        ContradictingAssertion -> S.pure (Ur (ConflictFound reason l))
        Asserted -> S.do
          Ur m <- S.uses watchesL $ LHM.lookup (litVar l)
          case m of
            Just (IS.delete (P.fromEnum reason) -> targs)
              | not (IS.null targs) -> loop (IS.toList targs) rest
            _ -> go rest
      where
        loop :: [Int] -> Seq.Seq (Lit, ClauseId) -> S.State CDCLState (Ur PropResult)
        loop [] !rest = go rest
        loop (!i : !is) !rest = S.do
          Ur c <- S.uses clausesL $ LV.unsafeGet i
          Ur resl <- S.zoom valuationL $ propLit l c
          case resl of
            Nothing -> loop is rest
            Just (Conflict l) ->
              S.pure (Ur (ConflictFound (toClauseId i) l))
            Just (Satisfied m) -> S.do
              setSatisfied m (ClauseId i)
              loop is rest
            Just (WatchChangedFromTo w old new newIdx) -> S.do
              updateWatchLit (ClauseId i) w old new newIdx
              loop is rest
            Just (Unit l) ->
              loop is (rest |> (l, toClauseId i))
    go Seq.Empty = S.do
      -- No literal given a priori. Find first literal.
      -- FIXME: Use heuristics for variable selection.
      (Ur resl) <- S.state \(CDCLState numCls steps clauses watches vals vids) ->
        dup2 vids & BiL.first LSet.toList & \(Ur targs, vids) ->
          LV.unsafeFindAtWith
            ( \vals c -> S.do
                if satisfiedAt c P.< 0
                  then
                    S.runState (findUnit c) vals
                      & \(Ur r, vals) -> (Ur r, vals)
                  else (Ur Nothing, vals)
            )
            vals
            (coerce targs)
            clauses
            & \(Ur ur, vals, clauses) ->
              (Ur ur, CDCLState numCls steps clauses watches vals vids)
      case resl of
        Nothing -> S.pure (Ur NoMorePropagation)
        Just (WatchChangedFromTo w old new newIdx, i) -> S.do
          updateWatchLit (ClauseId i) w old new newIdx
          go Seq.Empty
        Just (Satisfied m, i) -> S.do
          setSatisfied m (ClauseId i)
          go Seq.Empty
        Just (Conflict ml, i) ->
          S.pure (Ur (ConflictFound (toClauseId i) ml))
        Just (Unit l, i) -> S.do
          go (Seq.singleton (l, toClauseId i))

setSatisfied :: Maybe (Pair (Pair WatchVar VarId) (Pair VarId Index)) -> ClauseId -> S.StateT CDCLState Identity ()
setSatisfied m i = S.do
  Ur lvl <- currentDecideLevel
  clausesL S.%= LV.modify_ (\c -> c {satisfiedAt = lvl}) (unClauseId i)
  unsatisfiedsL S.%= LSet.delete i
  case m of
    Just ((w :!: old) :!: (new :!: newIdx)) ->
      updateWatchLit i w old new newIdx
    Nothing -> S.pure ()

updateWatchLit :: ClauseId -> WatchVar -> VarId -> VarId -> Index -> S.State CDCLState ()
updateWatchLit cid w old new vid = S.do
  S.zoom clausesL $ S.modify $ LV.modify_ (watchVarL w .~ vid) $ unClauseId cid
  unwatch cid old
  watch cid new

watch :: ClauseId -> VarId -> S.State CDCLState ()
watch cid v =
  watchesL
    S.%= LHM.alter
      (Just . P.maybe (IS.singleton $ fromEnum cid) (IS.insert $ fromEnum cid))
      v

unwatch :: ClauseId -> VarId -> S.State CDCLState ()
unwatch cid v =
  watchesL
    S.%= LHM.alter
      ( >>=
          IS.delete (fromEnum cid) >>> \s ->
            if IS.null s then Nothing else Just s
      )
      v

assertLit :: ClauseId -> Lit -> S.State CDCLState AssertionResult
assertLit ante lit = S.do
  let vid = fromEnum $ litVar lit :: Int
  mres <- S.uses valuationL (LUA.unsafeGet vid)
  case mres of
    -- Unassigned. We can safely assign
    Ur Indefinite {} -> S.do
      let antecedent
            | ante < 0 = Nothing
            | otherwise = Just ante
      Ur (decideLevel :!: decisionStep) <- S.zoom stepsL S.do
        Ur len <- S.state LUV.size
        let curStp = len - 1
        S.state $ LUV.modify (\i -> (i + 1, fromIntegral curStp :!: i)) curStp
      valuationL
        S.%= LUA.unsafeSet vid Definite {value = isPositive lit, ..}
      S.pure Asserted
    Ur Definite {..}
      | isPositive lit == value -> S.pure Asserted
      | otherwise -> S.pure ContradictingAssertion

-- | Propagate Literal.
propLit :: Lit -> Clause -> S.State Valuation (Ur (Maybe UnitResult))
propLit trueLit c@Clause {..}
  | satisfiedAt >= 0 = S.pure $ Ur $ Just $ Satisfied Nothing
  | otherwise =
      let l1 = lits U.! watched1
       in if litVar l1 == litVar trueLit
            then -- Have the same variable as watched var #1

              if l1 == trueLit
                then S.pure $ Ur $ Just $ Satisfied Nothing -- Satisfied.
                else S.do
                  -- False. Find next watched lit.
                  Ur mnext <- findNextAvailable W1 c
                  case mnext of
                    Just next -> S.pure $ Ur $ Just $ fromNextSlot next
                    Nothing -- No vacancy.
                      | watched2 < 0 -> S.pure $ Ur $ Just $ Conflict l1
                      | otherwise -> S.do
                          let l2 = (U.!) lits watched2
                          Ur mval2 <- evalLit l2
                          case mval2 of
                            Nothing -> S.pure $ Ur $ Just $ Unit l2
                            Just True -> S.pure $ Ur $ Just $ Satisfied Nothing
                            Just False ->
                              -- Unsatifiable! pick the oldest variable as conflicting lit.
                              Ur.lift Just D.<$> reportLastAddedAsConflict c
            else -- Otherwise it must be watched var #2

              let l2 = (U.!) lits watched2
               in if l2 == trueLit
                    then S.pure $ Ur $ Just $ Satisfied Nothing -- Satisfied
                    else S.do
                      Ur mnext <- findNextAvailable W2 c
                      case mnext of
                        Just next -> S.pure $ Ur $ Just $ fromNextSlot next
                        Nothing -> S.do
                          Ur mval1 <- evalLit l1
                          case mval1 of
                            Nothing -> S.pure $ Ur $ Just $ Unit l1
                            Just True -> S.pure $ Ur $ Just $ Satisfied Nothing
                            Just False ->
                              -- Unsatifiable! pick the oldest variable as conflicting lit.
                              Ur.lift Just D.<$> reportLastAddedAsConflict c

findUnit ::
  Clause ->
  S.State Valuation (Ur (Maybe UnitResult))
findUnit c@Clause {..}
  | watched2 < 0 = S.do
      -- Only the first literal is active.
      let !l = (U.!) lits watched1
      Ur mres <- evalLit l
      S.pure case mres of
        Just False -> Ur $ Just (Conflict l)
        Just True -> Ur $ Just $ Satisfied Nothing
        Nothing -> Ur $ Just (Unit l)
  | otherwise = S.do
      -- The clause has more than two literals.
      let l1 = (U.!) lits watched1
          l2 = (U.!) lits watched2
      Ur mres <- evalLit l1
      case mres of
        Just True ->
          -- satisfied; nothing to do.
          S.pure $ Ur $ Just $ Satisfied Nothing
        Just False -> S.do
          -- Unsatisfiable literal: find next available literal for watched1
          Ur mres <- findNextAvailable W1 c
          case mres of
            Just next ->
              -- Next slot found. Move to it.
              S.pure $ Ur $ Just $ fromNextSlot next
            Nothing -> S.do
              -- No vacancy. Trying to "satisfy" watched 2.
              Ur mres' <- evalLit l2
              case mres' of
                Nothing ->
                  -- w2 can be unit!
                  S.pure $ Ur $ Just $ Unit l2
                Just True -> S.pure $ Ur $ Just $ Satisfied Nothing
                Just False ->
                  -- Unsatifiable! pick the oldest variable as conflicting lit.
                  Ur.lift Just D.<$> reportLastAddedAsConflict c
        Nothing -> S.do
          -- Undetermined. Check for watched2
          Ur mres' <- evalLit l2
          case mres' of
            Just True ->
              -- satisfied; nothing to do.
              S.pure (Ur (Just $ Satisfied Nothing))
            Just False -> S.do
              -- Unsatisfiable literal: find next available literal for watched2
              Ur mres'' <- findNextAvailable W2 c
              S.pure $ Ur $ case mres'' of
                Just next -> Just $ fromNextSlot next
                Nothing -> Just $ Unit l1 -- w1 is unit!
            Nothing -> S.pure (Ur Nothing) -- No literal changed.

reportLastAddedAsConflict :: Clause -> S.State Valuation (Ur UnitResult)
reportLastAddedAsConflict c@Clause {..}
  | watched2 < 0 = S.pure $ Ur $ Conflict $ getWatchedLit W1 c
  | otherwise = S.do
      let l1 = getWatchedLit W1 c
          l2 = getWatchedLit W2 c
      Ur v1 <- S.state $ LUA.unsafeGet (fromEnum $ litVar l1)
      Ur v2 <- S.state $ LUA.unsafeGet (fromEnum $ litVar l2)
      S.pure
        $ Ur
        $ Conflict
        $ if introduced v1 > introduced v2 then l1 else l2

introduced :: Variable -> Pair DecideLevel Step
introduced Indefinite = -1 :!: -1
introduced Definite {..} = decideLevel :!: decisionStep

getWatchedLit :: WatchVar -> Clause -> Lit
getWatchedLit W1 Clause {..} = (U.!) lits watched1
getWatchedLit W2 Clause {..} = (U.!) lits watched2

fromNextSlot :: NextSlot -> UnitResult
fromNextSlot (NextSlot True w old new lid) = Satisfied $ Just $ (w :!: old) :!: (new :!: lid)
fromNextSlot (NextSlot False w old new lid) = WatchChangedFromTo w old new lid

data NextSlot = NextSlot
  { satisfied :: !Bool
  , target :: !WatchVar
  , oldVar, newVar :: {-# UNPACK #-} !VarId
  , litIndexInClause :: {-# UNPACK #-} !Index
  }
  deriving (Show, P.Eq, P.Ord, GHC.Generic)

findNextAvailable :: WatchVar -> Clause -> S.State Valuation (Ur (Maybe NextSlot))
findNextAvailable w c@Clause {..} = S.do
  let lit = getWatchedLit w c
      origVar = litVar lit
  Ur cands <- S.state \vals ->
    unsafeMapMaybeL
      vals
      (P.curry P.. unassigned watched1 watched2)
      lits

  let (mSat, mUndet) =
        L.foldOver
          (Lens.foldring U.foldr)
          ( (,)
              <$> (fmap fst <$> L.find ((== AssignedTrue) P.. P.snd))
              <*> (fmap fst <$> L.find ((== Unassigned) P.. P.snd))
          )
          cands
  case mSat of
    Just i ->
      let v' = litVar $ (U.!) lits i
       in S.pure $ Ur $ Just $ NextSlot True w origVar v' i
    Nothing -> case mUndet of
      Just i ->
        let v' = litVar $ (U.!) lits i
         in S.pure $ Ur $ Just $ NextSlot False w origVar v' i
      Nothing -> S.pure (Ur Nothing)

unassigned :: Index -> Index -> Valuation -> (Int, Lit) -> Maybe AssignmentState
unassigned exc1 exc2 vals (cur, l)
  | cur == exc1 || cur == exc2 = Nothing
  | otherwise =
      S.runState (evalLit l) vals & \case
        (Ur Nothing, _vals) -> Just Unassigned
        (Ur (Just True), _vals) -> Just AssignedTrue
        (Ur (Just False), _vals) -> Nothing

unsafeMapMaybeL ::
  forall a b s.
  (U.Unbox a, U.Unbox b) =>
  s %1 ->
  (s -> Int -> a -> Maybe b) ->
  U.Vector a ->
  (Ur (U.Vector (Int, b)), s)
unsafeMapMaybeL s p vs =
  Unsafe.toLinear (\s -> (Ur (p s), s)) s & \(Ur p, s) ->
    (Ur (U.imapMaybe (traverse P.. p) P.$ U.indexed vs), s)

evalLit :: Lit -> S.State Valuation (Ur (Maybe Bool))
evalLit l = S.do
  Ur m <- S.state $ LUA.unsafeGet (fromEnum $ litVar l)
  S.pure case m of
    Definite {..} ->
      Ur
        $ Just
        $ if Lens.is _PosL l
          then value
          else not value
    Indefinite -> Ur Nothing

evalClause :: Clause -> S.State Valuation (Ur (Maybe Bool))
evalClause Clause {..}
  | satisfiedAt >= 0 = S.pure $ Ur $ Just True
  | otherwise = S.do
      runUrT
        $ runMaybeT
          ( L.foldOverM
              vectorTraverse
              ( L.premapM
                  (MaybeT . fmap Just . UrT . evalLit)
                  $ L.handlesM _Just orLE
                  *> L.generalize (L.any P.isNothing)
              )
              lits
          )
        <&> \case
          Nothing -> Just True
          Just anyIndef
            | anyIndef -> Nothing
            | otherwise -> Just False

orLE :: (Monad m) => L.FoldM (MaybeT m) Bool ()
orLE = L.FoldM (P.const $ guard P.. not) (pure ()) pure
