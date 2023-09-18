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
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | DPLL Algorithm, supercharged with Conflict-Driven Clause Learning (CDCL).
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
  solveWith,
  solveVarIdWith,
  solveState,
  propagateUnit,

  -- * Re-exports
  CNF (..),
  CNFClause (..),
  Literal (..),
  VarId (..),
) where

import Control.Applicative
import Control.Foldl qualified as L
import Control.Functor.Linear qualified as C
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens hiding (Index, lens, (%=), (&), (.=))
import Control.Lens qualified as Lens
import Control.Monad qualified as P
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (runExceptT, throwE)
import Control.Monad.Trans.Maybe (runMaybeT)
import Control.Optics.Linear qualified as LinOpt
import Data.Alloc.Linearly.Token (besides, linearly)
import Data.Array.Mutable.Linear qualified as LA
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Bifunctor qualified as Bi
import Data.Bifunctor.Linear qualified as BiL
import Data.Foldable qualified as Foldable
import Data.Function (fix)
import Data.Functor.Linear qualified as D
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as LHM
import Data.HashSet qualified as HS
import Data.Hashable
import Data.IntSet qualified as IS
import Data.Maybe qualified as P
import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies, reflect, reify)
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
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import GHC.Generics qualified as GHC
import GHC.Stack
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
{-# INLINE solve #-}
solve = solveWith defaultOptions

solveWith :: (LHM.Keyed a) => CDCLOptions -> CNF a -> SatResult (Model a)
{-# INLINE [1] solveWith #-}
{-# ANN solveWith "HLint: ignore Avoid lambda" #-}
solveWith opts cnf = reify opts \(_ :: Proxy s) -> unur $ LHM.empty 128 \dic ->
  besides dic (`LHM.emptyL` 128) & \(rev, dic) ->
    S.runState
      (runUrT (traverse (\v -> liftUrT (renameCNF v)) cnf))
      ((rev, Ur 0), dic)
      & \(Ur cnf, ((dic, Ur _), rev)) ->
        dic
          `lseq` besides rev (toCDCLState @s cnf)
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

{-# RULES "solveWith/VarId" solveWith = solveVarIdWith #-}

solveVarId :: CNF VarId -> SatResult (Model VarId)
{-# INLINE solveVarId #-}
solveVarId = solveVarIdWith defaultOptions

solveVarIdWith :: CDCLOptions -> CNF VarId -> SatResult (Model VarId)
{-# INLINE solveVarIdWith #-}
solveVarIdWith opts cnf = reify opts \(_ :: Proxy s) ->
  unur PL.$ linearly \l ->
    toCDCLState @s cnf l PL.& \case
      Left (Ur resl) -> Ur (P.mempty P.<$ resl)
      Right stt -> solveState stt

solveState :: (Reifies s CDCLOptions) => CDCLState s %1 -> Ur (SatResult (Model VarId))
solveState = toSatResult PL.. S.runState (solverLoop Nothing)

solverLoop :: (Reifies s CDCLOptions, HasCallStack) => Maybe (Lit, ClauseId) -> S.State (CDCLState s) FinalState
solverLoop = fix $ \go mlit -> S.do
  -- First, check if the original clauses are all satisfied (at the current stage)
  -- We only have to traverse the initial segment, as the lerant clauses are always
  -- deducible from the original clauses.
  -- Without this, CDCL solver seems at most x1000 slower than DPLL and even Naïve tableaux...

  Ur allSat <- Ur.lift (== 0) C.<$> S.uses unsatisfiedsL LSet.size
  if allSat
    then S.pure Ok
    else S.do
      Ur numIniCls <- move C.<$> S.use numInitialClausesL
      mstt <-
        fix
          ( \self !i ->
              (i == numIniCls) & \case
                True -> S.pure True
                False -> S.do
                  val <- evalClause $ ClauseId i
                  val & \case
                    Just True -> S.do
                      unsatisfiedsL S.%= LSet.delete (ClauseId i)
                      self PL.$! i + 1
                    Just False -> S.pure False
                    Nothing -> S.pure False
          )
          0
      mstt & \case
        True -> S.pure Ok
        -- Contracdiction! The last assigned variable must be
        False -> S.do
          resl <- propagateUnit mlit
          case resl of
            ConflictFound cid l ->
              move (cid, l) & \(Ur (cid, l)) -> S.do
                backjump cid l -- Conflict found. Let's Backjump!
            NoMorePropagation -> S.do
              reduceLearntClause
              -- Decide indefinite variable
              -- FIXME: Perhaps we can choose the variable from unsatisified clause?
              -- FIXME: Use heuristics for variable selection.
              Ur mid <- S.zoom vsidsStateL findUnsatVar
              case mid of
                Nothing -> S.do
                  S.pure Ok -- No vacant variable - model is full!
                Just vid -> S.do
                  stepsL S.%= LUV.push 0
                  let decLit = NegL vid
                  C.void $ assertLit (-1) decLit
                  go (Just (decLit, -1))

backjump :: (Reifies s CDCLOptions) => ClauseId -> Lit -> S.State (CDCLState s) FinalState
backjump confCls lit = S.do
  S.zoom vsidsStateL decayVarPriosM
  S.zoom clausesL decayClauseActivity
  Ur confLits <- S.zoom clausesL $ foldClauseLits L.set confCls
  mLearnt <- findUIP1 lit confLits
  case mLearnt of
    Nothing ->
      -- No valid backjumping destination found. Unsat.
      S.pure Failed
    Just (Ur (decLvl, mlearnt, truth)) -> S.do
      Ur numCls <- getNumClauses
      fix
        ( \self !i ->
            if i == numCls
              then S.pure ()
              else S.do
                Ur satAt <- getSatisfiedLevel $ ClauseId i
                satAt > decLvl & \case
                  True -> S.do
                    setSatisfiedLevel (ClauseId i) (-1)
                    unsatisfiedsL S.%= LSet.insert (ClauseId i)
                  False -> S.pure ()
                self (i + 1)
        )
        0

      Ur reason <- case mlearnt of
        Just learnt -> S.do
          stepsL S.%= LUV.slice 0 (unDecideLevel decLvl + 1)
          pushClause learnt
          Ur reason <- Ur.lift (fromIntegral . subtract 1) C.<$> getNumClauses
          watch reason $ litVar (lits learnt U.! watched1 learnt)
          if watched2 learnt >= 0
            then watch reason $ litVar (lits learnt U.! watched2 learnt)
            else S.pure ()
          S.pure $ Ur reason
        Nothing -> S.pure $ Ur confCls

      -- FIXME: Perhaps we can iterate through unsats instead of entire vals?
      Ur unsats' <- S.uses valuationL \vals ->
        LUA.size vals & \(Ur n, vals) ->
          fix
            ( \go !i !upds vals ->
                if i == n
                  then (Ur upds, vals)
                  else
                    LUA.unsafeGet i vals & \(Ur v, vals) ->
                      isAssignedAfter decLvl v & \case
                        True ->
                          LUA.unsafeSet i Indefinite vals & \vals ->
                            go (i + 1) (fromIntegral i : upds) vals
                        False -> go (i + 1) upds vals
            )
            0
            []
            vals

      S.zoom vsidsStateL $ Ur.evalUrT $ P.forM_ unsats' \v ->
        liftUrT
          $ S.state
          $ ((),)
          PL.. moveToUnsatQueue v
      C.void $ assertLit reason truth
      tryRestart
      solverLoop $ Just (truth, reason)

findUIP1 ::
  forall s.
  (Reifies s CDCLOptions) =>
  Lit ->
  Set Lit ->
  S.State (CDCLState s) (Maybe (Ur (DecideLevel, Maybe Clause, Lit)))
findUIP1 !lit !curCls
  | Set.null curCls = S.do
      S.pure Nothing
  | otherwise = S.do
      ml <- checkUnitClauseLit curCls
      case ml of
        Ur (Just (l', decLvl)) -> S.do
          -- Already Unit clause. Learn it!
          S.pure $ Just $ Ur (mkLearntClause decLvl l' curCls)
        Ur Nothing -> S.do
          -- Not a UIP. resolve.
          Ur v <- S.uses valuationL $ LUA.unsafeGet $ fromVarId $ litVar lit
          case v of
            Indefinite -> error $ "Literal " P.<> show lit P.<> " was chosen as resolver, but indefinite!"
            Definite {..} -> S.do
              Ur cls' <- case antecedent of
                Just ante -> S.zoom clausesL S.do
                  bumpClauseActivity ante
                  foldClauseLits L.set ante
                Nothing -> S.pure (Ur Set.empty)
              activateResolved (reflect $ Proxy @s) & \case
                True -> S.zoom vsidsStateL $ incrementVarM lit
                False -> S.pure ()
              let resolved = resolve lit curCls cls'
              if Set.null resolved
                then S.do
                  S.pure Nothing -- Conflicting clause
                else S.do
                  Ur mlit' <- findConflictingLit resolved
                  case mlit' of
                    Just lit' -> findUIP1 lit' resolved
                    Nothing -> S.do
                      Ur lvl <- currentDecideLevel
                      -- the literal is decision variable
                      S.pure $ Just $ Ur (lvl - 1, Nothing, lit)

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

findConflictingLit :: (Foldable t) => t Lit -> S.State (CDCLState s) (Ur (Maybe Lit))
findConflictingLit lits = S.uses valuationL \vals ->
  foldlLin'
    vals
    ( \vals !mn !l ->
        LUA.unsafeGet (fromVarId $ litVar l) vals & \(Ur var, vals) ->
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

checkUnitClauseLit :: Set Lit -> S.State (CDCLState s) (Ur (Maybe (Lit, DecideLevel)))
checkUnitClauseLit ls = S.do
  Ur lvl <- currentDecideLevel
  Ur lcnd <- S.uses valuationL \vals ->
    foldlLin'
      vals
      ( \vals (Ur (ULS count mcand large small)) lit ->
          LUA.unsafeGet (fromVarId (litVar lit)) vals & \(Ur var, vals) ->
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
      (ULS 0 St.Nothing 0 (-1))
      ls
  S.pure $ case lcnd of
    (ULS 1 mx _ pu) | pu >= 0 -> Ur ((,pu) <$> St.toLazy mx)
    _ -> Ur Nothing

foldlLin' :: (Foldable.Foldable t) => b %1 -> (b %1 -> Ur x -> a -> (Ur x, b)) -> x -> t a -> (Ur x, b)
foldlLin' b f x =
  Unsafe.toLinear
    (P.fmap (Foldable.foldl' (P.uncurry $ P.flip (forget f))) . P.flip (,))
    b
    (Ur x)

currentDecideLevel :: S.State (CDCLState s) (Ur DecideLevel)
{-# INLINE currentDecideLevel #-}
currentDecideLevel =
  Ur.lift (fromIntegral P.. P.subtract 1)
    D.<$> S.uses stepsL LUV.size

toSatResult :: (FinalState, CDCLState s) %1 -> Ur (SatResult (Model VarId))
toSatResult (Failed, state) = state `lseq` Ur Unsat
toSatResult (Ok, state) =
  LUA.freeze (extractValuation state) & Ur.lift do
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

toClauseId :: Int -> ClauseId
toClauseId = fromIntegral

newtype Early s a = Early {runEarly :: UrT (S.State (CDCLState s)) (St.Maybe (Either (ClauseId, Lit) (Lit, ClauseId)))}
  deriving (Functor)

instance Applicative (Early s) where
  pure = P.const $ Early $ pure St.Nothing
  liftA2 _ (Early mf) (Early mx) = Early do
    f <- mf
    case f of
      St.Nothing -> mx
      St.Just x -> pure $ St.Just x

  Early mf <* Early mx = Early do
    f <- mf
    case f of
      St.Nothing -> mx
      St.Just x -> pure $ St.Just x

  Early mf *> Early mx = Early do
    f <- mf
    case f of
      St.Nothing -> mx
      St.Just x -> pure $ St.Just x

  Early mf <*> Early mx = Early do
    f <- mf
    case f of
      St.Nothing -> mx
      St.Just x -> pure $ St.Just x

propagateUnit :: (HasCallStack) => Maybe (Lit, ClauseId) -> S.State (CDCLState s) PropResult
propagateUnit ml = S.do
  go (P.maybe Seq.empty Seq.singleton ml)
  where
    go :: Seq.Seq (Lit, ClauseId) -> S.State (CDCLState s) PropResult
    go ((l, reason) :<| rest) = S.do
      assResl <- assertLit reason l
      case assResl of
        ContradictingAssertion -> S.do
          S.pure (ConflictFound reason l)
        Asserted -> S.do
          Ur !dest <-
            C.fmap
              (Ur.lift IS.toList)
              $ S.uses watchesL
              $ LA.unsafeGet (fromEnum $ litVar l)
          loop dest rest
      where
        loop :: [Int] -> Seq.Seq (Lit, ClauseId) -> S.State (CDCLState s) PropResult
        loop [] !rest = S.do
          go rest
        loop (!i : !is) !rest = S.do
          let cid = ClauseId i
          resl <- propLit l cid
          case resl of
            Nothing -> S.do
              loop is rest
            Just (Conflict confLit) -> S.do
              S.pure (ConflictFound (toClauseId i) confLit)
            Just (Satisfied m) -> S.do
              setSatisfied m (ClauseId i)
              loop is rest
            Just (WatchChangedFromTo w old new newIdx) -> S.do
              updateWatchLit (ClauseId i) w old new newIdx
              loop is rest
            Just (Unit newl) ->
              -- This move is essentally no-op, as it inherits instance
              -- from Word.
              move newl & \(Ur newl) ->
                loop is (rest |> (newl, toClauseId i))
    go Seq.Empty = S.do
      -- No literal given a priori. Find first literal.
      -- FIXME: Use heuristics for variable selection.
      Ur cands <- S.uses unsatisfiedsL $ BiL.first LSet.toList PL.. dup2
      Ur mresl <-
        runUrT
          $ runEarly
          $ Foldable.traverse_
            ( \ !i -> Early do
                w <- UrT $ S.zoom clausesL $ getWatchedLits i
                resl <- liftUrT $ findUnit i w
                case resl of
                  Nothing -> pure St.Nothing
                  Just (WatchChangedFromTo w old new newIdx) -> S.do
                    St.Nothing <$ liftUrT (updateWatchLit i w old new newIdx)
                  Just (Satisfied m) -> S.do
                    St.Nothing <$ liftUrT (setSatisfied m i)
                  Just (Conflict ml) -> S.do
                    pure $ St.Just $ Left (i, ml)
                  Just (Unit l) -> S.do
                    pure $ St.Just $ Right (l, i)
            )
            cands
      case mresl of
        St.Nothing -> S.pure NoMorePropagation
        St.Just (Left (i, ml)) -> S.pure $ ConflictFound i ml
        St.Just (Right (l, i)) ->
          -- NOTE: this Unsafe.toLinear is safe because (l, i) ~= (Int, Int).
          Unsafe.toLinear (go P.. Seq.singleton) (l, i)

setSatisfied :: Maybe (Pair (Pair WatchVar VarId) (Pair VarId Index)) %1 -> ClauseId -> S.State (CDCLState s) ()
{-# INLINE setSatisfied #-}
setSatisfied m i = S.do
  Ur lvl <- currentDecideLevel
  setSatisfiedLevel i lvl
  unsatisfiedsL S.%= LSet.delete i
  case m of
    Just ((w :!: old) :!: (new :!: newIdx)) ->
      updateWatchLit i w old new newIdx
    Nothing -> S.pure ()

updateWatchLit :: ClauseId -> WatchVar %1 -> VarId %1 -> VarId %1 -> Index %1 -> S.State (CDCLState s) ()
{-# INLINE updateWatchLit #-}
updateWatchLit cid w old new idx = S.do
  setWatchVar cid w idx
  unwatch cid old
  watch cid new

watch :: ClauseId -> VarId %1 -> S.State (CDCLState s) ()
watch cid =
  -- NOTE: This toLinear is safe b/c VarId ~ Int.
  Unsafe.toLinear \v ->
    watchesL
      S.%= \ws ->
        LA.unsafeGet (fromEnum v) ws & \(Ur !xs, ws) ->
          let !xs' = IS.insert (unClauseId cid) xs
           in LA.unsafeSet (fromEnum v) xs' ws

unwatch :: ClauseId -> VarId %1 -> S.State (CDCLState s) ()
unwatch cid =
  -- NOTE: This toLinear is safe b/c VarId ~ Int.
  Unsafe.toLinear \v ->
    watchesL
      S.%= \ws ->
        LA.unsafeGet (fromEnum v) ws & \(Ur !xs, ws) ->
          let !xs' = IS.delete (unClauseId cid) xs
           in LA.unsafeSet (fromEnum v) xs' ws

assertLit :: (HasCallStack) => ClauseId -> Lit -> S.State (CDCLState s) AssertionResult
assertLit ante lit = S.do
  let vid = fromVarId $ litVar lit :: Int
  mres <- S.uses valuationL (LUA.unsafeGet vid)
  case mres of
    -- Unassigned. We can safely assign
    Ur Indefinite {} -> S.do
      vsidsStateL S.%= moveToSatQueue (litVar lit)
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
propLit :: Lit -> ClauseId -> S.State (CDCLState s) (Maybe UnitResult)
propLit trueLit cid = S.do
  Ur satLvl <- getSatisfiedLevel cid
  if satLvl >= 0
    then S.pure $ Just $ Satisfied Nothing
    else S.do
      Ur wlits <- S.zoom clausesL (getWatchedLits cid)
      let !l1 = getLit1 wlits
      if litVar l1 == litVar trueLit
        then -- Have the same variable as watched var #1

          if l1 == trueLit
            then S.pure $ Just $ Satisfied Nothing -- Satisfied.
            else S.do
              -- False. Find next watched lit.
              mnext <- findNextAvailable W1 cid
              case mnext of
                Just next -> S.pure $ Just $ fromNextSlot next
                Nothing -> case getLit2 wlits of
                  Nothing ->
                    -- No vacancy
                    S.pure $ Just $ Conflict l1
                  Just l2 -> S.do
                    mval2 <- S.zoom valuationL $ evalLit l2
                    case mval2 of
                      Nothing -> S.pure $ Just $ Unit l2
                      Just True -> S.pure $ Just $ Satisfied Nothing
                      Just False ->
                        -- Unsatifiable! pick the oldest variable as conflicting lit.
                        Just D.<$> S.zoom valuationL (reportLastAddedAsConflict wlits)
        else -- Otherwise it must be watched var #2

          let !l2 =
                P.fromMaybe (error $ "Impossible: propagated literal matched neither of lits! (prop, watcheds) = " <> show (trueLit, wlits))
                  $ getLit2 wlits
           in if l2 == trueLit
                then S.pure $ Just $ Satisfied Nothing -- Satisfied
                else S.do
                  mnext <- findNextAvailable W2 cid
                  case mnext of
                    Just next -> S.pure $ Just $ fromNextSlot next
                    Nothing -> S.do
                      mval1 <- S.zoom valuationL (evalLit l1)
                      case mval1 of
                        Nothing -> S.pure $ Just $ Unit l1
                        Just True -> S.pure $ Just $ Satisfied Nothing
                        Just False ->
                          -- Unsatifiable! pick the oldest variable as conflicting lit.
                          S.zoom valuationL $ Just D.<$> reportLastAddedAsConflict wlits

findUnit ::
  ClauseId ->
  WatchedLits ->
  S.State (CDCLState s) (Maybe UnitResult)
findUnit _ (WatchOne l) = S.do
  -- Only the first literal is active.
  mres <- S.zoom valuationL $ evalLit l
  S.pure case mres of
    Just False -> Just (Conflict l)
    Just True -> Just $ Satisfied Nothing
    Nothing -> Just (Unit l)
findUnit cid w@(WatchThese l1 l2) = S.do
  -- The clause has more than two literals.
  mres <- S.zoom valuationL $ evalLit l1
  case mres of
    Just True ->
      -- satisfied; nothing to do.
      S.pure $ Just $ Satisfied Nothing
    Just False -> S.do
      -- Unsatisfiable literal: find next available literal for watched1
      mres <- findNextAvailable W1 cid
      case mres of
        Just next ->
          -- Next slot found. Move to it.
          S.pure $ Just $ fromNextSlot next
        Nothing -> S.do
          -- No vacancy. Trying to "satisfy" watched 2.
          mres' <- S.zoom valuationL $ evalLit l2
          case mres' of
            Nothing ->
              -- w2 can be unit!
              S.pure $ Just $ Unit l2
            Just True -> S.pure $ Just $ Satisfied Nothing
            Just False ->
              -- Unsatifiable! pick the oldest variable as conflicting lit.
              S.zoom valuationL $ Just D.<$> reportLastAddedAsConflict w
    Nothing -> S.do
      -- Undetermined. Check for watched2
      mres' <- S.zoom valuationL $ evalLit l2
      case mres' of
        Just True ->
          -- satisfied; nothing to do.
          S.pure $ Just $ Satisfied Nothing
        Just False -> S.do
          -- Unsatisfiable literal: find next available literal for watched2
          mres'' <- findNextAvailable W2 cid
          S.pure $ case mres'' of
            Just next -> Just $ fromNextSlot next
            Nothing -> Just $ Unit l1 -- w1 is unit!
        Nothing -> S.pure Nothing -- No literal changed.

reportLastAddedAsConflict :: WatchedLits -> S.State Valuation UnitResult
reportLastAddedAsConflict (WatchOne l1) = S.pure $ Conflict l1
reportLastAddedAsConflict (WatchThese l1 l2) = S.do
  Ur v1 <- S.state $ LUA.unsafeGet (fromVarId $ litVar l1)
  Ur v2 <- S.state $ LUA.unsafeGet (fromVarId $ litVar l2)
  S.pure
    $ Conflict
    $ if introduced v1 > introduced v2 then l1 else l2

introduced :: Variable -> Pair DecideLevel Step
introduced Indefinite = -1 :!: -1
introduced Definite {..} = decideLevel :!: decisionStep

fromNextSlot :: NextSlot %1 -> UnitResult
fromNextSlot (NextSlot True w old new lid) = Satisfied $ Just $ (w :!: old) :!: (new :!: lid)
fromNextSlot (NextSlot False w old new lid) = WatchChangedFromTo w old new lid

data NextSlot = NextSlot
  { satisfied :: !Bool
  , target :: !WatchVar
  , oldVar, newVar :: {-# UNPACK #-} !VarId
  , litIndexInClause :: {-# UNPACK #-} !Index
  }
  deriving (Show, P.Eq, P.Ord, GHC.Generic)

(<|>:) :: St.Maybe a -> St.Maybe a -> St.Maybe a
{-# INLINE (<|>:) #-}
(<|>:) = St.maybe P.id (P.const . St.Just)

findNextAvailable :: WatchVar -> ClauseId -> S.State (CDCLState s) (Maybe NextSlot)
findNextAvailable w cid = S.do
  Ur widx <- S.zoom clausesL $ getWatchedLitIndices cid
  Ur wlits <- S.zoom clausesL $ getWatchedLits cid
  let origVar = litVar $ watchLitOf w wlits

  Ur lits <- S.zoom clausesL $ getClauseLits cid
  Ur (mSat :!: mUndet) <-
    S.zoom valuationL
      $ runUrT
      $ fmap (P.either P.id P.id)
      $ runExceptT
      $ U.ifoldM'
        -- Loop invariant: both mSat and mUndet must be Nothing
        ( \(mSat :!: mUndet) !i !l -> do
            if i `elemWatchLitIdx` widx
              then pure (mSat :!: mUndet)
              else do
                !v <- lift $ liftUrT (evalLit l)
                let (!mSat', !mUndet') =
                      Bi.bimap
                        (mSat <|>:)
                        (mUndet <|>:)
                        case v of
                          Nothing -> (St.Nothing, St.Just i)
                          Just False -> (St.Nothing, St.Nothing)
                          Just True -> (St.Just i, St.Nothing)
                if St.isJust mSat' && St.isJust mUndet'
                  then throwE (mSat' :!: mUndet')
                  else pure (mSat' :!: mUndet')
        )
        (St.Nothing :!: St.Nothing)
        lits

  case mSat of
    St.Just i -> S.do
      Ur l' <- S.zoom clausesL $ getClauseLitAt cid i
      S.pure $ Just $ NextSlot True w origVar (litVar l') i
    St.Nothing -> case mUndet of
      St.Just i -> S.do
        Ur l' <- S.zoom clausesL $ getClauseLitAt cid i
        S.pure $ Just $ NextSlot False w origVar (litVar l') i
      St.Nothing -> S.pure Nothing

evalLit :: Lit -> S.State Valuation (Maybe Bool)
evalLit l = S.do
  Ur m <- S.state $ LUA.unsafeGet (fromVarId $ litVar l)
  S.pure case m of
    Definite {..} -> Just $ isPositive l == value
    Indefinite -> Nothing

evalClause :: ClauseId -> S.State (CDCLState s) (Maybe Bool)
{- HLINT ignore evalClause "Avoid lambda" -}
evalClause cid = S.do
  Ur lvl <- getSatisfiedLevel cid
  lvl >= 0 & \case
    True -> S.pure $ Just True
    False -> S.do
      Ur lits <- S.zoom clausesL $ getClauseLits cid
      S.zoom valuationL
        $ D.fmap unur
        $ runUrT
        $ fmap (P.fromMaybe (Just True))
        $ runMaybeT
        $ U.foldM'
          ( \ !anyNothing !l ->
              lift (liftUrT $ evalLit l) >>= \case
                Nothing -> pure Nothing
                Just False -> pure anyNothing
                Just True -> empty
          )
          (Just False)
          lits
