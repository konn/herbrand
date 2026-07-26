{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
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
  luby,
  SolverStats (..),
  solveWith,
  solveVarIdWith,
  solveVarIdWithStats,
  solveState,
  propagateUnit,

  -- * Re-exports
  CNF (..),
  CNFClause (..),
  Literal (..),
  VarId (..),
) where

import Control.Foldl qualified as L
import Control.Functor.Linear qualified as C
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens hiding (Index, lens, (%=), (&), (.=))
import Control.Lens qualified as Lens
import Control.Monad qualified as P
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (runExceptT, throwE)
import Control.Optics.Linear qualified as LinOpt
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
import Data.Set (Set)
import Data.Set qualified as Set
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
import Linear.Token.Linearly (besides, linearly)
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
  besides dic (LHM.emptyL 128) & \(rev, dic) ->
    S.runState
      (runUrT (traverse (\v -> liftUrT (renameCNF v)) cnf))
      ((rev, Ur 0), dic)
      & \(Ur cnf, ((dic, Ur _), rev)) ->
        dic `lseq`
          besides rev (toCDCLState @s cnf)
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
          UrT $
            S.state $
              \dic ->
                BiL.first
                  ( D.fmap
                      ( fromMaybe
                          ( error $
                              "unrenameModel: variable out of bound: "
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

solveVarIdWithStats :: CDCLOptions -> CNF VarId -> (SatResult (Model VarId), SolverStats)
solveVarIdWithStats opts cnf = reify opts \(_ :: Proxy s) ->
  unur PL.$ linearly \l ->
    toCDCLState @s cnf l PL.& \case
      Left (Ur resl) -> Ur (P.mempty P.<$ resl, zeroSolverStats)
      Right state -> solveStateWithStats state

solveStateWithStats ::
  (Reifies s CDCLOptions) =>
  CDCLState s %1 ->
  Ur (SatResult (Model VarId), SolverStats)
#ifdef HERBRAND_CDCL_INSTRUMENTED
solveStateWithStats = finalizeWithStats PL.. S.runState (solverLoop Nothing)

finalizeWithStats ::
  (FinalState, CDCLState s) %1 ->
  Ur (SatResult (Model VarId), SolverStats)
finalizeWithStats (finalState, finalSolverState) =
  S.runState (S.use solverStatsL) finalSolverState & \(stats, finalSolverState) ->
    PL.move stats & \(Ur stats) ->
      toSatResult (finalState, finalSolverState) & \(Ur result) ->
        Ur (result, stats)
#else
solveStateWithStats state =
  solveState state & \(Ur result) ->
    Ur (result, zeroSolverStats)
#endif

solveState :: (Reifies s CDCLOptions) => CDCLState s %1 -> Ur (SatResult (Model VarId))
solveState = toSatResult PL.. S.runState (solverLoop Nothing)

solverLoop :: (Reifies s CDCLOptions, HasCallStack) => Maybe (Lit, ClauseId) -> S.State (CDCLState s) FinalState
solverLoop = fix $ \go mlit -> S.do
  resl <- propagateUnit mlit
  case resl of
    ConflictFound cid l ->
      move (cid, l) & \(Ur (cid, l)) -> S.do
        backjump cid l
    NoMorePropagation -> S.do
      validateFixpoint
      Ur mid <- S.zoom vsidsStateL findUnsatVar
      case mid of
        Nothing -> S.pure Ok
        Just vid -> S.do
          bumpDecision
          stepsL S.%= LUV.push 0
          go (Just (NegL vid, -1))

backjump :: (Reifies s CDCLOptions) => ClauseId -> Lit -> S.State (CDCLState s) FinalState
backjump confCls lit = S.do
  bumpConflict
  S.zoom vsidsStateL decayVarPriosM
  Ur confLits <- S.zoom clausesL $ foldClauseLits L.set confCls
  mLearnt <- findUIP1 lit confLits
  case mLearnt of
    Nothing ->
      -- No valid backjumping destination found. Unsat.
      S.pure Failed
    Just (Ur (decLvl, mlearnt, truth)) -> S.do
      Ur reason <- case mlearnt of
        Just learnt -> S.do
          pushClause learnt
          Ur reason <- Ur.lift (fromIntegral . subtract 1) C.<$> getNumClauses
          watch reason $ litVar (lits learnt U.! watched1 learnt)
          if watched2 learnt >= 0
            then watch reason $ litVar (lits learnt U.! watched2 learnt)
            else S.pure ()
          S.pure $ Ur reason
        Nothing -> S.pure $ Ur confCls

      backtrackTrail decLvl
      clearSatisfiedAfter decLvl
      restart <- tryRestart
      case restart of
        Continued -> solverLoop $ Just (truth, reason)
        Restarted -> S.do
          backtrackTrail 0
          clearSatisfiedAfter (-1)
          qheadL S..= 0
          solverLoop Nothing

clearSatisfiedAfter :: DecideLevel -> S.State (CDCLState s) ()
clearSatisfiedAfter target = S.do
  Ur numCls <- getNumClauses
  fix
    ( \self !i ->
        if i == numCls
          then S.pure ()
          else S.do
            Ur satAt <- getSatisfiedLevel $ ClauseId i
            if satAt > target
              then setSatisfiedLevel (ClauseId i) (-1)
              else S.pure ()
            self (i + 1)
    )
    0

backtrackTrail :: DecideLevel -> S.State (CDCLState s) ()
backtrackTrail target = S.do
  stepsL S.%= LUV.slice 0 (unDecideLevel target + 1)
  Ur len <- S.uses trailL LUV.size
  Ur cutoff <-
    fix
      ( \go !i ->
          if i < 0
            then S.pure $ Ur 0
            else S.do
              Ur lit <- S.uses trailL $ LUV.unsafeGet i
              Ur var <- S.uses valuationL $ LUA.unsafeGet $ fromVarId $ litVar lit
              if isAssignedAfter target var
                then S.do
                  valuationL S.%= LUA.unsafeSet (fromVarId $ litVar lit) Indefinite
                  vsidsStateL S.%= moveToUnsatQueue (litVar lit)
                  go $ i - 1
                else S.pure $ Ur (i + 1)
      )
      (len - 1)
  trailL S.%= LUV.slice 0 cutoff
  qheadL S..= cutoff

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
          let remaining = Set.delete l' curCls
          Ur watch2 <-
            if Set.null remaining
              then S.pure $ Ur Nothing
              else findLitAtLevel decLvl remaining
          -- Already a unit clause. Watch the asserting literal and a literal
          -- at the backjump level so both watches are reset by deeper jumps.
          S.pure $ Just $ Ur (mkLearntClause decLvl l' watch2 remaining)
        Ur Nothing -> S.do
          -- Not a UIP. resolve.
          Ur v <- S.uses valuationL $ LUA.unsafeGet $ fromVarId $ litVar lit
          case v of
            Indefinite -> error $ "Literal " P.<> show lit P.<> " was chosen as resolver, but indefinite!"
            Definite {..} -> S.do
              Ur cls' <- case antecedent of
                Just ante -> S.zoom clausesL $ foldClauseLits L.set ante
                Nothing -> S.pure $ Ur Set.empty
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

findLitAtLevel :: DecideLevel -> Set Lit -> S.State (CDCLState s) (Ur (Maybe Lit))
findLitAtLevel targetLevel lits = S.uses valuationL \vals ->
  foldlLin'
    vals
    ( \vals (Ur found) lit ->
        LUA.unsafeGet (fromVarId $ litVar lit) vals & \(Ur variable, vals) ->
          let found' = case found of
                Just {} -> found
                Nothing -> case variable of
                  Definite {..}
                    | decideLevel == targetLevel -> Just lit
                  _ -> Nothing
           in (Ur found', vals)
    )
    Nothing
    lits

mkLearntClause :: DecideLevel -> Lit -> Maybe Lit -> Set Lit -> (DecideLevel, Maybe Clause, Lit)
mkLearntClause decLvl assertingLit watch2 remaining =
  let cls' =
        U.cons assertingLit case watch2 of
          Nothing
            | Set.null remaining -> U.empty
            | otherwise ->
                error $
                  "learned clause has no literal at its backjump level: "
                    P.<> show (decLvl, remaining)
          Just second ->
            U.cons second $
              L.fold L.vector $
                Set.delete second remaining
   in ( decLvl
      , Just
          Clause
            { watched2 = if U.length cls' > 1 then 1 else -1
            , watched1 = 0
            , satisfiedAt = decLvl
            , lits = cls'
            }
      , assertingLit
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

#ifdef HERBRAND_CDCL_INSTRUMENTED
validateFixpoint :: S.State (CDCLState s) ()
validateFixpoint = S.do
  Ur qhead <- move C.<$> S.use qheadL
  Ur trailSize <- S.uses trailL LUV.size
  if qhead /= trailSize
    then error $ "BCP fixpoint has qhead/trail mismatch: " P.<> show (qhead, trailSize)
    else S.pure ()

  Ur currentLevel <- currentDecideLevel
  Ur seen <- checkTrail currentLevel trailSize 0 IS.empty (-1)
  Ur numVars <- S.uses valuationL LUA.size
  checkValuation currentLevel seen numVars 0

  Ur numClauses <- getNumClauses
  checkClauses numClauses 0
  where
    checkTrail ::
      DecideLevel ->
      Int ->
      Int ->
      IS.IntSet ->
      DecideLevel ->
      S.State (CDCLState s) (Ur IS.IntSet)
    checkTrail currentLevel trailSize index seen previousLevel
      | index == trailSize = S.pure $ Ur seen
      | otherwise = S.do
          Ur lit <- S.uses trailL $ LUV.unsafeGet index
          let variableId = fromVarId $ litVar lit
          if IS.member variableId seen
            then error $ "duplicate variable on trail: " P.<> show (litVar lit)
            else S.pure ()
          Ur variable <- S.uses valuationL $ LUA.unsafeGet variableId
          case variable of
            Indefinite ->
              error $ "indefinite variable appears on trail: " P.<> show (litVar lit)
            Definite {..}
              | value /= isPositive lit ->
                  error $ "trail/valuation polarity mismatch: " P.<> show lit
              | decideLevel < previousLevel || decideLevel > currentLevel ->
                  error $
                    "non-monotone or future trail level: "
                      P.<> show (lit, previousLevel, decideLevel, currentLevel)
              | otherwise ->
                  checkTrail
                    currentLevel
                    trailSize
                    (index + 1)
                    (IS.insert variableId seen)
                    decideLevel

    checkValuation ::
      DecideLevel ->
      IS.IntSet ->
      Int ->
      Int ->
      S.State (CDCLState s) ()
    checkValuation currentLevel seen numVars index
      | index == numVars = S.pure ()
      | otherwise = S.do
          Ur variable <- S.uses valuationL $ LUA.unsafeGet index
          case variable of
            Indefinite -> S.pure ()
            Definite {..} -> S.do
              if IS.member index seen && decideLevel P.<= currentLevel
                then S.pure ()
                else
                  error $
                    "valuation/trail mismatch: "
                      P.<> show (index, decideLevel, currentLevel)
              case antecedent of
                Nothing -> S.pure ()
                Just reason -> S.do
                  Ur reasonLits <- S.zoom clausesL $ getClauseLits reason
                  let implied =
                        if value
                          then PosL $ toVarId index
                          else NegL $ toVarId index
                  if U.elem implied reasonLits
                    then S.pure ()
                    else
                      error $
                        "reason does not contain implied literal: "
                          P.<> show (reason, implied)
          checkValuation currentLevel seen numVars (index + 1)

    checkClauses :: Int -> Int -> S.State (CDCLState s) ()
    checkClauses numClauses index
      | index == numClauses = S.pure ()
      | otherwise = S.do
          Ur clauseLits <- S.zoom clausesL $ getClauseLits $ ClauseId index
          Ur (hasTrue :!: unassignedCount) <- S.uses valuationL \valuation ->
            foldlLin'
              valuation
              ( \valuation (Ur (hasTrue :!: unassignedCount)) clauseLit ->
                  LUA.unsafeGet (fromVarId $ litVar clauseLit) valuation
                    & \(Ur variable, valuation) ->
                      case variable of
                        Indefinite ->
                          (Ur (hasTrue :!: unassignedCount + 1), valuation)
                        Definite {..} ->
                          ( Ur
                              ( (hasTrue || value == isPositive clauseLit)
                                  :!: unassignedCount
                              )
                          , valuation
                          )
              )
              (False :!: (0 :: Int))
              (U.toList clauseLits)
          if hasTrue || unassignedCount > 1
            then checkClauses numClauses (index + 1)
            else S.do
              Ur watched <- S.zoom clausesL $ getWatchedLits $ ClauseId index
              Ur firstValue <- move C.<$> S.zoom valuationL (evalLit $ getLit1 watched)
              Ur secondValue <-
                move C.<$> case getLit2 watched of
                  Nothing -> S.pure Nothing
                  Just lit -> S.zoom valuationL $ evalLit lit
              Ur satisfiedLevel <- getSatisfiedLevel $ ClauseId index
              error $
                "BCP fixpoint contains unit/conflicting clause: "
                  P.<> show
                    ( ClauseId index
                    , U.toList clauseLits
                    , unassignedCount
                    , watched
                    , firstValue
                    , secondValue
                    , satisfiedLevel
                    )
#else
validateFixpoint :: S.State (CDCLState s) ()
{-# INLINE validateFixpoint #-}
validateFixpoint = S.pure ()
#endif

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

propagateUnit :: (HasCallStack) => Maybe (Lit, ClauseId) -> S.State (CDCLState s) PropResult
propagateUnit mlit = S.do
  mconflict <-
    case mlit of
      Just (lit, reason) -> enqueue reason lit
      Nothing -> seedRootUnits
  case mconflict of
    Just conflict -> S.pure conflict
    Nothing -> drainTrail
  where
    enqueue :: ClauseId -> Lit -> S.State (CDCLState s) (Maybe PropResult)
    enqueue reason lit = S.do
      result <- assertLit reason lit
      case result of
        ContradictingAssertion -> S.pure $ Just $ ConflictFound reason lit
        AlreadyAsserted -> S.do
          bumpDuplicateEnqueue
          S.pure Nothing
        NewlyAsserted -> S.do
          bumpAssignment
          S.pure Nothing

    seedRootUnits :: S.State (CDCLState s) (Maybe PropResult)
    seedRootUnits = S.do
      bumpSeedScan
      Ur numClauses <- getNumClauses
      fix
        ( \go !i ->
            if i == numClauses
              then S.pure Nothing
              else S.do
                let cid = ClauseId i
                Ur watched <- S.zoom clausesL $ getWatchedLits cid
                case watched of
                  WatchOne lit -> S.do
                    result <- enqueue cid lit
                    case result of
                      Just conflict -> S.pure $ Just conflict
                      Nothing -> go $ i + 1
                  WatchThese {} -> go $ i + 1
        )
        0

    drainTrail :: S.State (CDCLState s) PropResult
    drainTrail = S.do
      Ur qhead <- move C.<$> S.use qheadL
      Ur trailSize <- S.uses trailL LUV.size
      if qhead == trailSize
        then S.pure NoMorePropagation
        else S.do
          Ur lit <- S.uses trailL $ LUV.unsafeGet qhead
          bumpPropagationEvent
          qheadL S..= qhead + 1
          Ur !dest <-
            C.fmap
              (Ur.lift IS.toList)
              $ S.uses watchesL
              $ LA.unsafeGet (fromEnum $ litVar lit)
          loop lit dest
      where
        loop :: Lit -> [Int] -> S.State (CDCLState s) PropResult
        loop _ [] = drainTrail
        loop !lit (!i : !is) = S.do
          bumpWatchVisit
          let cid = ClauseId i
          resl <- propLit lit cid
          case resl of
            Nothing -> loop lit is
            Just (Conflict confLit) ->
              S.pure $ ConflictFound cid confLit
            Just (Satisfied m) ->
              case m of
                Just update -> S.do
                  bumpWatchMove
                  setSatisfied (Just update) cid
                  loop lit is
                Nothing -> S.do
                  setSatisfied Nothing cid
                  loop lit is
            Just (WatchChangedFromTo w old new newIdx) -> S.do
              bumpWatchMove
              updateWatchLit cid w old new newIdx
              loop lit is
            Just (Unit newLit) ->
              move newLit & \(Ur newLit) -> S.do
                result <- enqueue cid newLit
                case result of
                  Just conflict -> S.pure conflict
                  Nothing -> loop lit is

setSatisfied :: Maybe (Pair (Pair WatchVar VarId) (Pair VarId Index)) %1 -> ClauseId -> S.State (CDCLState s) ()
{-# INLINE setSatisfied #-}
setSatisfied m i = S.do
  Ur lvl <- currentDecideLevel
  setSatisfiedLevel i lvl
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
      trailL S.%= LUV.push lit
      bumpTrailAppend
      S.pure NewlyAsserted
    Ur Definite {..}
      | isPositive lit == value -> S.pure AlreadyAsserted
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
                P.fromMaybe (error $ "Impossible: propagated literal matched neither of lits! (prop, watcheds) = " <> show (trueLit, wlits)) $
                  getLit2 wlits
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

reportLastAddedAsConflict :: WatchedLits -> S.State Valuation UnitResult
reportLastAddedAsConflict (WatchOne l1) = S.pure $ Conflict l1
reportLastAddedAsConflict (WatchThese l1 l2) = S.do
  Ur v1 <- S.state $ LUA.unsafeGet (fromVarId $ litVar l1)
  Ur v2 <- S.state $ LUA.unsafeGet (fromVarId $ litVar l2)
  S.pure $
    Conflict $
      if introduced v1 > introduced v2 then l1 else l2

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
    S.zoom valuationL $
      runUrT $
        fmap (P.either P.id P.id) $
          runExceptT $
            U.ifoldM'
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
