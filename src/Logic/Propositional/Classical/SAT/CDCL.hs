{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiWayIf #-}
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

import Control.Functor.Linear qualified as C
import Control.Functor.Linear.State.Extra qualified as S
import Control.Lens hiding (Index, lens, (%=), (&), (.=))
import Control.Lens qualified as Lens
import Control.Monad qualified as P
import Control.Optics.Linear qualified as LinOpt
import Data.Array.Mutable.Linear.Unboxed qualified as LUA
import Data.Bifunctor.Linear qualified as BiL
import Data.Foldable qualified as Foldable
import Data.Function (fix)
import Data.Functor.Linear qualified as D
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Extra qualified as LHM
import Data.HashSet qualified as HS
import Data.Hashable
#ifdef HERBRAND_CDCL_INSTRUMENTED
import Data.IntSet qualified as IS
#endif
import Data.Proxy (Proxy (..))
import Data.Reflection (Reifies, reflect, reify)
import Data.Strict (Pair (..))
import Data.Tuple qualified as P
import Data.Unrestricted.Linear (UrT (..), liftUrT, runUrT)
import Data.Unrestricted.Linear qualified as Ur
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Data.Word (Word64)
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

data PropagationStart
  = SeedRootUnits
  | EnqueueLit {-# UNPACK #-} !Lit {-# UNPACK #-} !ClauseId
  | ResumePropagation
  deriving (Show, P.Eq, P.Ord, GHC.Generic)

data ClauseClassification
  = ClauseSatisfied
  | ClauseOpen
  | ClauseUnit {-# UNPACK #-} !Lit
  | ClauseConflict
  deriving (Show, P.Eq, P.Ord, GHC.Generic)

data ClauseScan = ClauseScan
  { scanSatisfied :: !Bool
  , scanUnassignedCount :: {-# UNPACK #-} !Int
  , scanUnassignedLit :: !(Maybe Lit)
  }

solve :: (LHM.Keyed a) => CNF a -> SatResult (Model a)
{-# INLINE solve #-}
solve = solveWith defaultOptions

solveWith :: (LHM.Keyed a) => CDCLOptions -> CNF a -> SatResult (Model a)
{-# INLINE [1] solveWith #-}
{-# ANN solveWith "HLint: ignore Avoid lambda" #-}
solveWith opts cnf =
  case solveSparseByPureLiterals cnf of
    Just model -> Satisfiable model
    Nothing -> reify opts \(_ :: Proxy s) -> unur $ LHM.empty 128 \dic ->
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

solveSparseByPureLiterals :: (Hashable a) => CNF a -> Maybe (Model a)
{-# INLINE solveSparseByPureLiterals #-}
solveSparseByPureLiterals (CNF clauses)
  | P.not $ hasWideFirstClause clauses = Nothing
  | P.not $ hasAtMost 64 clauses = Nothing
  | otherwise =
      let !clauseCount = P.length clauses
          !literalCount =
            Foldable.foldl'
              (\count (CNFClause clause) -> count P.+ P.length clause)
              0
              clauses
       in if literalCount P.< 8 P.* clauseCount
            then Nothing
            else go clauses P.mempty
  where
    hasAtMost :: Int -> [b] -> Bool
    hasAtMost _ [] = True
    hasAtMost 0 _ = False
    hasAtMost count (_ : rest) = hasAtMost (count P.- 1) rest

    hasWideFirstClause [] = True
    hasWideFirstClause (CNFClause clause : _) = hasAtLeast 8 clause

    hasAtLeast :: Int -> [b] -> Bool
    hasAtLeast 0 _ = True
    hasAtLeast _ [] = False
    hasAtLeast count (_ : rest) = hasAtLeast (count P.- 1) rest

    go [] model = Just model
    go active model =
      let (!positiveVars, !negativeVars) =
            Foldable.foldl' collectClause (HS.empty, HS.empty) active
          !purePositive = positiveVars `HS.difference` negativeVars
          !pureNegative = negativeVars `HS.difference` positiveVars
          !pureModel =
            Model
              { positive = purePositive
              , negative = pureNegative
              }
       in if HS.null purePositive P.&& HS.null pureNegative
            then Nothing
            else
              go
                (P.filter (P.not P.. isCovered purePositive pureNegative) active)
                (model P.<> pureModel)

    collectClause (!positiveVars, !negativeVars) (CNFClause clause) =
      Foldable.foldl' collectLit (positiveVars, negativeVars) clause

    collectLit (!positiveVars, !negativeVars) = \case
      Positive var -> (HS.insert var positiveVars, negativeVars)
      Negative var -> (positiveVars, HS.insert var negativeVars)

    isCovered purePositive pureNegative (CNFClause clause) =
      P.any
        ( \case
            Positive var -> HS.member var purePositive
            Negative var -> HS.member var pureNegative
        )
        clause

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
solveVarIdWith opts cnf =
  case solveSparseByPureLiterals cnf of
    Just model -> Satisfiable model
    Nothing -> reify opts \(_ :: Proxy s) ->
      unur PL.$ linearly \l ->
        toCDCLState @s cnf l PL.& \case
          Left (Ur resl) -> Ur (P.mempty P.<$ resl)
          Right stt -> solveState stt

solveVarIdWithStats :: CDCLOptions -> CNF VarId -> (SatResult (Model VarId), SolverStats)
solveVarIdWithStats opts cnf =
  case solveSparseByPureLiterals cnf of
    Just model -> (Satisfiable model, zeroSolverStats)
    Nothing -> reify opts \(_ :: Proxy s) ->
      unur PL.$ linearly \l ->
        toCDCLState @s cnf l PL.& \case
          Left (Ur resl) -> Ur (P.mempty P.<$ resl, zeroSolverStats)
          Right state -> solveStateWithStats state

solveStateWithStats ::
  (Reifies s CDCLOptions) =>
  CDCLState s %1 ->
  Ur (SatResult (Model VarId), SolverStats)
#ifdef HERBRAND_CDCL_INSTRUMENTED
solveStateWithStats = finalizeWithStats PL.. S.runState (solverLoop SeedRootUnits)

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
solveState = toSatResult PL.. S.runState (solverLoop SeedRootUnits)

solverLoop :: (Reifies s CDCLOptions, HasCallStack) => PropagationStart -> S.State (CDCLState s) FinalState
solverLoop = fix $ \go start -> S.do
  resl <- propagateFrom start
  case resl of
    ConflictFound cid ->
      move cid & \(Ur cid) -> backjump cid
    NoMorePropagation -> S.do
      validateFixpoint
      Ur mid <- S.zoom vsidsStateL findUnsatVar
      case mid of
        Nothing -> S.pure Ok
        Just vid -> S.do
          bumpDecision
          Ur trailSize <- S.uses trailL LUV.size
          levelStartsL S.%= LUV.push (fromIntegral trailSize)
          go (EnqueueLit (NegL vid) (-1))

backjump :: (Reifies s CDCLOptions) => ClauseId -> S.State (CDCLState s) FinalState
backjump confCls = S.do
  bumpConflict
  S.zoom vsidsStateL decayVarPriosM
  Ur analysis <- analyzeConflict confCls
  case analysis of
    RootConflict -> S.do
      recordRootAnalysis confCls
      S.pure Failed
    LearnedClause decLvl learnt truth metrics -> S.do
      recordLearnedAnalysis decLvl learnt metrics
      pushClause learnt
      Ur reason <- Ur.lift (fromIntegral . subtract 1) C.<$> getNumClauses
      backtrackTrail False decLvl
      restart <- tryRestart
      case restart of
        Continued -> S.do
          validateAssertingReason reason truth
          solverLoop $ EnqueueLit truth reason
        Restarted -> S.do
          backtrackTrail True 0
          Ur classification <- classifyClause reason
          validateRestartedLearnedClause truth classification
          case classification of
            ClauseConflict -> S.pure Failed
            ClauseUnit unitLit -> solverLoop $ EnqueueLit unitLit reason
            ClauseSatisfied -> solverLoop ResumePropagation
            ClauseOpen -> solverLoop ResumePropagation

backtrackTrail :: Bool -> DecideLevel -> S.State (CDCLState s) ()
backtrackTrail isRestart target = S.do
  Ur currentLevel <- currentDecideLevel
  Ur trailLength <- S.uses trailL LUV.size
  Ur (cutoff, boundaryReads) <-
    if target < currentLevel
      then S.do
        Ur levelStart <-
          S.uses levelStartsL $
            LUV.unsafeGet (unDecideLevel target + 1)
        S.pure $ Ur (fromIntegral levelStart, 1)
      else
        if target == currentLevel
          then S.pure $ Ur (trailLength, 0)
          else
            error $
              "backtrack target exceeds current level: "
                P.<> show (target, currentLevel)
  levelStartsL S.%= LUV.slice 0 (unDecideLevel target + 1)
  Ur oldQhead <- move C.<$> S.use qheadL
  Ur cleared <- clearTrailSuffix cutoff
  qheadL S..= P.min oldQhead cutoff
  recordBacktrack isRestart boundaryReads cleared cleared 0 0

data ConflictAnalysis
  = RootConflict
  | LearnedClause
      {-# UNPACK #-} !DecideLevel
      !Clause
      {-# UNPACK #-} !Lit
      !AnalysisMetrics

#ifdef HERBRAND_CDCL_INSTRUMENTED
data AnalysisMetrics = AnalysisMetrics
  { metricConflictClauseVisitCount :: {-# UNPACK #-} !Int
  , metricReasonClauseVisitCount :: {-# UNPACK #-} !Int
  , metricConflictLiteralVisitCount :: {-# UNPACK #-} !Int
  , metricReasonLiteralVisitCount :: {-# UNPACK #-} !Int
  , metricTrailReadCount :: {-# UNPACK #-} !Int
  , metricPivotCount :: {-# UNPACK #-} !Int
  , metricMarkCount :: {-# UNPACK #-} !Int
  , metricDuplicateMarkCount :: {-# UNPACK #-} !Int
  , metricEpochClearCount :: {-# UNPACK #-} !Int
  , metricPivotTraceRev :: ![Lit]
  }
#else
data AnalysisMetrics = AnalysisMetrics
#endif

data AnalysisAcc = AnalysisAcc
  { analysisPathCount :: {-# UNPACK #-} !Int
  , analysisScratchLength :: {-# UNPACK #-} !Int
  , analysisTargetLevel :: {-# UNPACK #-} !DecideLevel
  , analysisTargetIndex :: {-# UNPACK #-} !Int
  , analysisMetrics :: !AnalysisMetrics
  }

initialAnalysisAcc :: Int -> Bool -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
initialAnalysisAcc conflictLiteralCount epochCleared =
  AnalysisAcc
    { analysisPathCount = 0
    , analysisScratchLength = 0
    , analysisTargetLevel = -1
    , analysisTargetIndex = -1
    , analysisMetrics =
        AnalysisMetrics
          { metricConflictClauseVisitCount = 1
          , metricReasonClauseVisitCount = 0
          , metricConflictLiteralVisitCount = conflictLiteralCount
          , metricReasonLiteralVisitCount = 0
          , metricTrailReadCount = 0
          , metricPivotCount = 0
          , metricMarkCount = 0
          , metricDuplicateMarkCount = 0
          , metricEpochClearCount = if epochCleared then 1 else 0
          , metricPivotTraceRev = []
          }
    }
#else
initialAnalysisAcc _ _ =
  AnalysisAcc
    { analysisPathCount = 0
    , analysisScratchLength = 0
    , analysisTargetLevel = -1
    , analysisTargetIndex = -1
    , analysisMetrics = AnalysisMetrics
    }
#endif

noteAnalysisClauseScan :: Maybe (Lit, Step) -> Int -> AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisClauseScan Nothing _ acc = acc
noteAnalysisClauseScan Just {} literalCount acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics
          { metricReasonClauseVisitCount =
              metricReasonClauseVisitCount metrics + 1
          , metricReasonLiteralVisitCount =
              metricReasonLiteralVisitCount metrics + literalCount
          }
    }
#else
{-# INLINE noteAnalysisClauseScan #-}
noteAnalysisClauseScan _ _ acc = acc
#endif

noteAnalysisTrailRead :: AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisTrailRead acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics {metricTrailReadCount = metricTrailReadCount metrics + 1}
    }
#else
{-# INLINE noteAnalysisTrailRead #-}
noteAnalysisTrailRead acc = acc
#endif

noteAnalysisPivot :: Lit -> AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisPivot lit acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics
          { metricPivotCount = metricPivotCount metrics + 1
          , metricPivotTraceRev = lit : metricPivotTraceRev metrics
          }
    }
#else
{-# INLINE noteAnalysisPivot #-}
noteAnalysisPivot _ acc = acc
#endif

noteAnalysisMark :: AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisMark acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics {metricMarkCount = metricMarkCount metrics + 1}
    }
#else
{-# INLINE noteAnalysisMark #-}
noteAnalysisMark acc = acc
#endif

noteAnalysisDuplicateMark :: AnalysisAcc -> AnalysisAcc
#ifdef HERBRAND_CDCL_INSTRUMENTED
noteAnalysisDuplicateMark acc@AnalysisAcc {analysisMetrics = metrics} =
  acc
    { analysisMetrics =
        metrics
          { metricDuplicateMarkCount =
              metricDuplicateMarkCount metrics + 1
          }
    }
#else
{-# INLINE noteAnalysisDuplicateMark #-}
noteAnalysisDuplicateMark acc = acc
#endif

recordRootAnalysis :: ClauseId -> S.State (CDCLState s) ()
#ifdef HERBRAND_CDCL_INSTRUMENTED
recordRootAnalysis conflictClause = S.do
  Ur conflictLits <- S.zoom clausesL $ getClauseLits conflictClause
  solverStatsL S.%= \stats ->
    move stats & \(Ur stats) ->
      stats
        { analysisCount = analysisCount stats + 1
        , analysisRootConflictCount = analysisRootConflictCount stats + 1
        , analysisConflictClauseVisitCount =
            analysisConflictClauseVisitCount stats + 1
        , analysisConflictLiteralVisitCount =
            analysisConflictLiteralVisitCount stats + U.length conflictLits
        }
#else
{-# INLINE recordRootAnalysis #-}
recordRootAnalysis _ = S.pure ()
#endif

#ifdef HERBRAND_CDCL_INSTRUMENTED
recordLearnedAnalysis ::
  DecideLevel ->
  Clause ->
  AnalysisMetrics ->
  S.State (CDCLState s) ()
recordLearnedAnalysis target Clause {lits = learnedLits} AnalysisMetrics {..} =
  solverStatsL S.%= \stats ->
    move stats & \(Ur stats) ->
      stats
        { analysisCount = analysisCount stats + 1
        , analysisConflictClauseVisitCount =
            analysisConflictClauseVisitCount stats
              + metricConflictClauseVisitCount
        , analysisReasonClauseVisitCount =
            analysisReasonClauseVisitCount stats + metricReasonClauseVisitCount
        , analysisConflictLiteralVisitCount =
            analysisConflictLiteralVisitCount stats
              + metricConflictLiteralVisitCount
        , analysisReasonLiteralVisitCount =
            analysisReasonLiteralVisitCount stats
              + metricReasonLiteralVisitCount
        , analysisTrailReadCount =
            analysisTrailReadCount stats + metricTrailReadCount
        , analysisPivotCount = analysisPivotCount stats + metricPivotCount
        , analysisMarkCount = analysisMarkCount stats + metricMarkCount
        , analysisDuplicateMarkCount =
            analysisDuplicateMarkCount stats + metricDuplicateMarkCount
        , analysisLearnedLiteralCount =
            analysisLearnedLiteralCount stats + U.length learnedLits
        , analysisEpochClearCount =
            analysisEpochClearCount stats + metricEpochClearCount
        , analysisLastTargetLevel = unDecideLevel target
        , analysisLastPivotTrace =
            P.map (fmap (fromIntegral P.. fromVarId) P.. decodeLit) $
              P.reverse metricPivotTraceRev
        , analysisLastLearnedClause =
            P.map (fmap (fromIntegral P.. fromVarId) P.. decodeLit) $
              U.toList learnedLits
        , analysisLearnedTrace =
            ( P.map (fmap (fromIntegral P.. fromVarId) P.. decodeLit) $
                P.reverse metricPivotTraceRev
            , unDecideLevel target
            , P.map (fmap (fromIntegral P.. fromVarId) P.. decodeLit) $
                U.toList learnedLits
            )
              : analysisLearnedTrace stats
        }
#else
{-# INLINE recordLearnedAnalysis #-}
recordLearnedAnalysis ::
  DecideLevel ->
  Clause ->
  AnalysisMetrics ->
  S.State (CDCLState s) ()
recordLearnedAnalysis _ _ _ = S.pure ()
#endif

analyzeConflict ::
  forall s.
  (Reifies s CDCLOptions) =>
  ClauseId ->
  S.State (CDCLState s) (Ur ConflictAnalysis)
analyzeConflict conflictClause = S.do
  Ur currentLevel <- currentDecideLevel
  if currentLevel == 0
    then S.do
      validateConflictClause conflictClause
      S.pure $ Ur RootConflict
    else S.do
      Ur result <-
        S.uses analysisKernelL \(analysis, trail, clauses, valuation, vsids) ->
          analyzeConflictKernel
            (activateResolved $ reflect $ Proxy @s)
            currentLevel
            conflictClause
            analysis
            trail
            clauses
            valuation
            vsids
      case result of
        RootConflict ->
          error "positive-level analysis returned a root conflict"
        LearnedClause target learned assertingLit _ -> S.do
          validateLearnedAnalysis
            currentLevel
            target
            learned
            assertingLit
          S.pure $ Ur result

analyzeConflictKernel ::
  forall s.
  Bool ->
  DecideLevel ->
  ClauseId ->
  AnalysisScratch %1 ->
  LUV.Vector Lit %1 ->
  Clauses %1 ->
  Valuation %1 ->
  VSIDSState s %1 ->
  ( Ur ConflictAnalysis
  , (AnalysisScratch, LUV.Vector Lit, Clauses, Valuation, VSIDSState s)
  )
analyzeConflictKernel bumpResolved currentLevel conflictClause =
  \(AnalysisScratch oldEpoch stamps0 scratch) trail clauses valuation vsids ->
    advanceEpoch oldEpoch stamps0 & \(Ur epoch, stamps) ->
      S.runState (getClauseLits conflictClause) clauses & \(Ur conflictLits, clauses) ->
        scanAnalysisClause
          currentLevel
          epoch
          Nothing
          conflictLits
          (initialAnalysisAcc (U.length conflictLits) (oldEpoch == maxBound))
          stamps
          scratch
          valuation
          & \(Ur initialAcc, stamps, scratch, valuation) ->
            if analysisPathCount initialAcc P.<= 0
              then
                analysisFailure
                  ( "positive-level conflict has no current-level path: "
                      P.<> show (conflictClause, currentLevel)
                  )
                  epoch
                  stamps
                  scratch
                  trail
                  clauses
                  valuation
                  vsids
              else
                LUV.size trail & \(Ur trailLength, trail) ->
                  seek
                    (trailLength - 1)
                    initialAcc
                    epoch
                    stamps
                    scratch
                    trail
                    clauses
                    valuation
                    vsids
  where
    seek ::
      Int ->
      AnalysisAcc ->
      Word64 ->
      LUA.UArray Word64 %1 ->
      LUA.UArray Lit %1 ->
      LUV.Vector Lit %1 ->
      Clauses %1 ->
      Valuation %1 ->
      VSIDSState s %1 ->
      ( Ur ConflictAnalysis
      , (AnalysisScratch, LUV.Vector Lit, Clauses, Valuation, VSIDSState s)
      )
    seek !cursor !acc !epoch stamps scratch trail clauses valuation vsids
      | cursor < 0 =
          analysisFailure
            "first-UIP analysis exhausted the trail before finding a marked pivot"
            epoch
            stamps
            scratch
            trail
            clauses
            valuation
            vsids
      | otherwise =
          LUV.unsafeGet cursor trail & \(Ur assignedLit, trail) ->
            let accRead = noteAnalysisTrailRead acc
                variableIndex = fromVarId $ litVar assignedLit
             in LUA.unsafeGet variableIndex stamps & \(Ur stamp, stamps) ->
                  if stamp /= epoch
                    then
                      seek
                        (cursor - 1)
                        accRead
                        epoch
                        stamps
                        scratch
                        trail
                        clauses
                        valuation
                        vsids
                    else
                      let remainingPaths = analysisPathCount accRead - 1
                          acc' =
                            noteAnalysisPivot assignedLit $
                              accRead {analysisPathCount = remainingPaths}
                          stamps' = LUA.unsafeSet variableIndex 0 stamps
                       in if remainingPaths == 0
                            then
                              finishAnalysis
                                (negL assignedLit)
                                acc'
                                epoch
                                stamps'
                                scratch
                                trail
                                clauses
                                valuation
                                vsids
                            else
                              if remainingPaths < 0
                                then
                                  analysisFailure
                                    "first-UIP path counter became negative"
                                    epoch
                                    stamps'
                                    scratch
                                    trail
                                    clauses
                                    valuation
                                    vsids
                                else
                                  LUA.unsafeGet variableIndex valuation & \(Ur variable, valuation) ->
                                    case variable of
                                      Indefinite ->
                                        analysisFailure
                                          ("marked trail pivot is unassigned: " P.<> show assignedLit)
                                          epoch
                                          stamps'
                                          scratch
                                          trail
                                          clauses
                                          valuation
                                          vsids
                                      Definite {antecedent = Nothing} ->
                                        analysisFailure
                                          ( "reasonless decision selected before the final UIP: "
                                              P.<> show assignedLit
                                          )
                                          epoch
                                          stamps'
                                          scratch
                                          trail
                                          clauses
                                          valuation
                                          vsids
                                      Definite {antecedent = Just reason, decisionStep = pivotStep} ->
                                        let vsids' =
                                              if bumpResolved
                                                then
                                                  S.execState
                                                    (incrementVarM assignedLit)
                                                    vsids
                                                else vsids
                                         in S.runState (getClauseLits reason) clauses
                                              & \(Ur reasonLits, clauses) ->
                                                scanAnalysisClause
                                                  currentLevel
                                                  epoch
                                                  (Just (assignedLit, pivotStep))
                                                  reasonLits
                                                  acc'
                                                  stamps'
                                                  scratch
                                                  valuation
                                                  & \(Ur nextAcc, stamps, scratch, valuation) ->
                                                    seek
                                                      (cursor - 1)
                                                      nextAcc
                                                      epoch
                                                      stamps
                                                      scratch
                                                      trail
                                                      clauses
                                                      valuation
                                                      vsids'

advanceEpoch ::
  Word64 ->
  LUA.UArray Word64 %1 ->
  (Ur Word64, LUA.UArray Word64)
advanceEpoch oldEpoch stamps
  | oldEpoch == maxBound = (Ur 1, LUA.mapSame (P.const 0) stamps)
  | otherwise = (Ur (oldEpoch + 1), stamps)

scanAnalysisClause ::
  DecideLevel ->
  Word64 ->
  Maybe (Lit, Step) ->
  U.Vector Lit ->
  AnalysisAcc ->
  LUA.UArray Word64 %1 ->
  LUA.UArray Lit %1 ->
  Valuation %1 ->
  (Ur AnalysisAcc, LUA.UArray Word64, LUA.UArray Lit, Valuation)
scanAnalysisClause currentLevel epoch pivot lits initialAcc =
  \stamps scratch valuation ->
    go
      0
      (noteAnalysisClauseScan pivot literalCount initialAcc)
      0
      stamps
      scratch
      valuation
  where
    !literalCount = U.length lits

    go ::
      Int ->
      AnalysisAcc ->
      Int ->
      LUA.UArray Word64 %1 ->
      LUA.UArray Lit %1 ->
      Valuation %1 ->
      (Ur AnalysisAcc, LUA.UArray Word64, LUA.UArray Lit, Valuation)
    go !index !acc !pivotOccurrences stamps scratch valuation
      | index == literalCount =
          case pivot of
            Nothing -> (Ur acc, stamps, scratch, valuation)
            Just {}
              | pivotOccurrences == 1 ->
                  (Ur acc, stamps, scratch, valuation)
              | otherwise ->
                  analysisClauseFailure
                    ( "reason contains the pivot assignment an invalid number of times: "
                        P.<> show pivotOccurrences
                    )
                    stamps
                    scratch
                    valuation
      | otherwise =
          let lit = U.unsafeIndex lits index
           in case pivot of
                Just (assignedLit, _)
                  | litVar lit == litVar assignedLit ->
                      if lit == assignedLit
                        then
                          go
                            (index + 1)
                            acc
                            (pivotOccurrences + 1)
                            stamps
                            scratch
                            valuation
                        else
                          analysisClauseFailure
                            ( "reason contains the opposite pivot literal: "
                                P.<> show (assignedLit, lit)
                            )
                            stamps
                            scratch
                            valuation
                _ ->
                  let variableIndex = fromVarId $ litVar lit
                   in LUA.unsafeGet variableIndex valuation & \(Ur variable, valuation) ->
                        case variable of
                          Indefinite ->
                            analysisClauseFailure
                              ("analysis clause contains an unassigned literal: " P.<> show lit)
                              stamps
                              scratch
                              valuation
                          Definite {..}
                            | value == isPositive lit ->
                                analysisClauseFailure
                                  ("analysis clause contains a true literal: " P.<> show lit)
                                  stamps
                                  scratch
                                  valuation
                            | decideLevel > currentLevel ->
                                analysisClauseFailure
                                  ( "analysis clause literal exceeds the conflict level: "
                                      P.<> show (lit, decideLevel, currentLevel)
                                  )
                                  stamps
                                  scratch
                                  valuation
                            | otherwise ->
                                validateReasonPrecedence pivot lit decisionStep `lseq`
                                  LUA.unsafeGet variableIndex stamps
                                    & \(Ur stamp, stamps) ->
                                      if stamp == epoch
                                        then
                                          go
                                            (index + 1)
                                            (noteAnalysisDuplicateMark acc)
                                            pivotOccurrences
                                            stamps
                                            scratch
                                            valuation
                                        else
                                          let stamps' =
                                                LUA.unsafeSet variableIndex epoch stamps
                                              markedAcc = noteAnalysisMark acc
                                           in if decideLevel == currentLevel
                                                then
                                                  go
                                                    (index + 1)
                                                    markedAcc
                                                      { analysisPathCount =
                                                          analysisPathCount markedAcc + 1
                                                      }
                                                    pivotOccurrences
                                                    stamps'
                                                    scratch
                                                    valuation
                                                else
                                                  let scratchIndex =
                                                        analysisScratchLength markedAcc
                                                      scratch' =
                                                        LUA.unsafeSet scratchIndex lit scratch
                                                      (targetLevel, targetIndex)
                                                        | analysisTargetIndex markedAcc < 0
                                                            || decideLevel > analysisTargetLevel markedAcc =
                                                            (decideLevel, scratchIndex)
                                                        | otherwise =
                                                            ( analysisTargetLevel markedAcc
                                                            , analysisTargetIndex markedAcc
                                                            )
                                                   in go
                                                        (index + 1)
                                                        markedAcc
                                                          { analysisScratchLength =
                                                              scratchIndex + 1
                                                          , analysisTargetLevel = targetLevel
                                                          , analysisTargetIndex = targetIndex
                                                          }
                                                        pivotOccurrences
                                                        stamps'
                                                        scratch'
                                                        valuation

finishAnalysis ::
  Lit ->
  AnalysisAcc ->
  Word64 ->
  LUA.UArray Word64 %1 ->
  LUA.UArray Lit %1 ->
  LUV.Vector Lit %1 ->
  Clauses %1 ->
  Valuation %1 ->
  VSIDSState s %1 ->
  ( Ur ConflictAnalysis
  , (AnalysisScratch, LUV.Vector Lit, Clauses, Valuation, VSIDSState s)
  )
finishAnalysis assertingLit AnalysisAcc {..} epoch stamps scratch trail clauses valuation vsids =
  let learnedLength = analysisScratchLength + 1
   in LUA.unsafeAllocBeside learnedLength scratch & \(output0, scratch) ->
        let output = LUA.unsafeSet 0 assertingLit output0
         in copyLowerLiterals
              0
              analysisScratchLength
              analysisTargetIndex
              scratch
              output
              & \(scratch, output) ->
                LUA.freeze output & \(Ur learnedLits) ->
                  let target
                        | analysisScratchLength == 0 = 0
                        | analysisTargetIndex >= 0 = analysisTargetLevel
                        | otherwise =
                            P.error "non-unit learned clause has no backjump target"
                      clause =
                        Clause
                          { lits = learnedLits
                          , watched1 = 0
                          , watched2 = if learnedLength > 1 then 1 else -1
                          }
                   in ( Ur
                          ( LearnedClause
                              target
                              clause
                              assertingLit
                              analysisMetrics
                          )
                      ,
                        ( AnalysisScratch epoch stamps scratch
                        , trail
                        , clauses
                        , valuation
                        , vsids
                        )
                      )

copyLowerLiterals ::
  Int ->
  Int ->
  Int ->
  LUA.UArray Lit %1 ->
  LUA.UArray Lit %1 ->
  (LUA.UArray Lit, LUA.UArray Lit)
copyLowerLiterals !index !count !targetIndex scratch output
  | index == count = (scratch, output)
  | otherwise =
      let sourceIndex
            | index == 0 = targetIndex
            | index == targetIndex = 0
            | otherwise = index
       in LUA.unsafeGet sourceIndex scratch & \(Ur lit, scratch) ->
            copyLowerLiterals
              (index + 1)
              count
              targetIndex
              scratch
              (LUA.unsafeSet (index + 1) lit output)

analysisFailure ::
  String ->
  Word64 ->
  LUA.UArray Word64 %1 ->
  LUA.UArray Lit %1 ->
  LUV.Vector Lit %1 ->
  Clauses %1 ->
  Valuation %1 ->
  VSIDSState s %1 ->
  a
analysisFailure message epoch stamps scratch trail clauses valuation vsids =
  epoch `lseq`
    stamps `lseq`
      scratch `lseq`
        trail `lseq`
          clauses `lseq`
            valuation `lseq`
              vsids `lseq`
                P.error message

analysisClauseFailure ::
  String ->
  LUA.UArray Word64 %1 ->
  LUA.UArray Lit %1 ->
  Valuation %1 ->
  a
analysisClauseFailure message stamps scratch valuation =
  stamps `lseq` scratch `lseq` valuation `lseq` P.error message

#ifdef HERBRAND_CDCL_INSTRUMENTED
validateReasonPrecedence :: Maybe (Lit, Step) -> Lit -> Step -> ()
validateReasonPrecedence Nothing _ _ = ()
validateReasonPrecedence (Just (pivot, pivotStep)) lit introducedAt
  | introducedAt < pivotStep = ()
  | otherwise =
      P.error $
        "reason literal does not precede its pivot: "
          P.<> show (pivot, pivotStep, lit, introducedAt)
#else
validateReasonPrecedence :: Maybe (Lit, Step) -> Lit -> Step -> ()
{-# INLINE validateReasonPrecedence #-}
validateReasonPrecedence _ _ _ = ()
#endif

#ifdef HERBRAND_CDCL_INSTRUMENTED
validateConflictClause :: ClauseId -> S.State (CDCLState s) ()
validateConflictClause cid = S.do
  Ur classification <- classifyClause cid
  case classification of
    ClauseConflict -> S.pure ()
    _ ->
      error $
        "reported conflict clause is not fully false: "
          P.<> show (cid, classification)
#else
validateConflictClause :: ClauseId -> S.State (CDCLState s) ()
{-# INLINE validateConflictClause #-}
validateConflictClause cid = cid `lseq` S.pure ()
#endif

#ifdef HERBRAND_CDCL_INSTRUMENTED
validateLearnedAnalysis ::
  DecideLevel ->
  DecideLevel ->
  Clause ->
  Lit ->
  S.State (CDCLState s) ()
validateLearnedAnalysis currentLevel target Clause {..} assertingLit
  | currentLevel P.<= 0 =
      error $
        "learned analysis has a nonpositive conflict level: "
          P.<> show currentLevel
  | target < 0 || target >= currentLevel =
      error $
        "learned analysis has an invalid target level: "
          P.<> show (target, currentLevel)
  | U.null lits =
      error "learned analysis returned an empty clause"
  | U.unsafeIndex lits 0 /= assertingLit =
      error $
        "learned clause does not start with its asserting literal: "
          P.<> show (assertingLit, U.toList lits)
  | watched1 /= 0 =
      error $
        "learned clause does not watch its asserting literal first: "
          P.<> show (watched1, U.toList lits)
  | watched2 /= if U.length lits > 1 then 1 else -1 =
      error $
        "learned clause has an invalid second watch: "
          P.<> show (watched2, U.toList lits)
  | otherwise = S.do
      if U.length lits > 1
        then S.do
          let secondLit = U.unsafeIndex lits 1
          Ur secondVariable <-
            S.uses valuationL $
              LUA.unsafeGet (fromVarId $ litVar secondLit)
          case secondVariable of
            Indefinite ->
              error $
                "learned clause second watch is unassigned before backtracking: "
                  P.<> show (secondLit, U.toList lits)
            Definite {..}
              | value == isPositive secondLit ->
                  error $
                    "learned clause second watch is true before backtracking: "
                      P.<> show (secondLit, U.toList lits)
              | decideLevel /= target ->
                  error $
                    "learned clause second watch is not at the backjump level: "
                      P.<> show
                        (secondLit, decideLevel, target, U.toList lits)
              | otherwise -> S.pure ()
        else S.pure ()
      Ur (currentLevelLiterals, maximumLowerLevel, seenVariables) <-
        S.uses valuationL \valuation ->
          foldlLin'
            valuation
            ( \valuation (Ur (!currentCount, !maxLower, !seen)) lit ->
                let variableIndex = fromVarId $ litVar lit
                 in if IS.member variableIndex seen
                      then
                        learnedValidationFailure
                          ( "learned clause contains a duplicate variable: "
                              P.<> show (lit, U.toList lits)
                          )
                          valuation
                      else
                        LUA.unsafeGet variableIndex valuation
                          & \(Ur variable, valuation) ->
                            case variable of
                              Indefinite ->
                                learnedValidationFailure
                                  ( "learned clause contains an unassigned literal "
                                      P.<> "before backtracking: "
                                      P.<> show (lit, U.toList lits)
                                  )
                                  valuation
                              Definite {..}
                                | value == isPositive lit ->
                                    learnedValidationFailure
                                      ( "learned clause contains a true literal "
                                          P.<> "before backtracking: "
                                          P.<> show (lit, U.toList lits)
                                      )
                                      valuation
                                | decideLevel == currentLevel ->
                                    ( Ur
                                        ( currentCount + 1
                                        , maxLower
                                        , IS.insert variableIndex seen
                                        )
                                    , valuation
                                    )
                                | decideLevel < currentLevel ->
                                    ( Ur
                                        ( currentCount
                                        , P.max maxLower decideLevel
                                        , IS.insert variableIndex seen
                                        )
                                    , valuation
                                    )
                                | otherwise ->
                                    learnedValidationFailure
                                      ( "learned clause literal exceeds the conflict level: "
                                          P.<> show
                                            (lit, decideLevel, currentLevel)
                                      )
                                      valuation
            )
            (0, 0, IS.empty)
            (U.toList lits)
      if
        | currentLevelLiterals /= 1 ->
            error $
              "learned clause is not first-UIP asserting: "
                P.<> show (currentLevelLiterals, U.toList lits)
        | maximumLowerLevel /= target ->
            error $
              "learned clause target is not the maximum lower level: "
                P.<> show
                  ( target
                  , maximumLowerLevel
                  , U.toList lits
                  )
        | IS.size seenVariables /= U.length lits ->
            error "learned-clause variable accounting mismatch"
        | otherwise -> S.pure ()
  where
    learnedValidationFailure ::
      String ->
      Valuation %1 ->
      (Ur (Int, DecideLevel, IS.IntSet), Valuation)
    learnedValidationFailure message valuation =
      valuation `lseq` P.error message

validateRestartedLearnedClause ::
  Lit ->
  ClauseClassification ->
  S.State (CDCLState s) ()
validateRestartedLearnedClause assertingLit = \case
  ClauseUnit unitLit
    | unitLit == assertingLit -> S.pure ()
    | otherwise ->
        error $
          "restarted learned clause is unit on the wrong literal: "
            P.<> show (assertingLit, unitLit)
  ClauseOpen -> S.pure ()
  ClauseSatisfied ->
    error "restarted learned clause is unexpectedly satisfied"
  ClauseConflict ->
    error "restarted learned clause is unexpectedly conflicting"
#else
validateLearnedAnalysis ::
  DecideLevel ->
  DecideLevel ->
  Clause ->
  Lit ->
  S.State (CDCLState s) ()
{-# INLINE validateLearnedAnalysis #-}
validateLearnedAnalysis _ _ _ _ = S.pure ()

validateRestartedLearnedClause ::
  Lit ->
  ClauseClassification ->
  S.State (CDCLState s) ()
{-# INLINE validateRestartedLearnedClause #-}
validateRestartedLearnedClause _ _ = S.pure ()
#endif

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
    D.<$> S.uses levelStartsL LUV.size

#ifdef HERBRAND_CDCL_INSTRUMENTED
validateFixpoint :: S.State (CDCLState s) ()
validateFixpoint = S.do
  Ur qhead <- move C.<$> S.use qheadL
  Ur trailSize <- S.uses trailL LUV.size
  if qhead /= trailSize
    then error $ "BCP fixpoint has qhead/trail mismatch: " P.<> show (qhead, trailSize)
    else S.pure ()

  Ur currentLevel <- currentDecideLevel
  checkLevelStarts currentLevel trailSize
  Ur seen <- checkTrail currentLevel trailSize 0 IS.empty (-1)
  Ur numVars <- S.uses valuationL LUA.size
  checkValuation currentLevel seen numVars 0

  Ur numClauses <- getNumClauses
  Ur watchOccurrences <- checkWatchMap numVars numClauses
  checkActiveWatches numClauses watchOccurrences 0
  checkClauses numClauses 0
  where
    checkLevelStarts ::
      DecideLevel ->
      Int ->
      S.State (CDCLState s) ()
    checkLevelStarts currentLevel trailSize = S.do
      Ur levelCount <- S.uses levelStartsL LUV.size
      if levelCount == unDecideLevel currentLevel + 1
        then checkLevelStart levelCount trailSize 0 (-1)
        else
          error $
            "decision-level boundary count mismatch: "
              P.<> show (levelCount, currentLevel)

    checkLevelStart ::
      Int ->
      Int ->
      Int ->
      Int ->
      S.State (CDCLState s) ()
    checkLevelStart levelCount trailSize level previousStart
      | level == levelCount = S.pure ()
      | otherwise = S.do
          Ur boundaryStep <-
            S.uses levelStartsL $
              LUV.unsafeGet level
          let boundary = fromIntegral boundaryStep
          if
            | level == 0 && boundary /= 0 ->
                error $
                  "root trail boundary is not zero: "
                    P.<> show boundary
            | level > 0
                && ( boundary < previousStart
                      || (level > 1 && boundary == previousStart)
                      || boundary >= trailSize
                   ) ->
                error $
                  "invalid decision-level trail boundary: "
                    P.<> show
                      ( level
                      , boundary
                      , previousStart
                      , trailSize
                      )
            | boundary > trailSize ->
                error $
                  "decision-level trail boundary is out of bounds: "
                    P.<> show (level, boundary, trailSize)
            | otherwise -> S.pure ()
          if level == 0
            then S.pure ()
            else S.do
              Ur firstLit <- S.uses trailL $ LUV.unsafeGet boundary
              Ur firstVariable <-
                S.uses valuationL $
                  LUA.unsafeGet (fromVarId $ litVar firstLit)
              if boundary == 0
                then case firstVariable of
                  Definite {decideLevel = firstLevel}
                    | level == 1 && firstLevel == 1 -> S.pure ()
                  _ ->
                    error $
                      "first decision-level boundary has the wrong level: "
                        P.<> show
                          (level, boundary, firstLit, firstVariable)
                else S.do
                  Ur previousLit <-
                    S.uses trailL $
                      LUV.unsafeGet (boundary - 1)
                  Ur previousVariable <-
                    S.uses valuationL $
                      LUA.unsafeGet (fromVarId $ litVar previousLit)
                  case (firstVariable, previousVariable) of
                    ( Definite {decideLevel = firstLevel}
                      , Definite {decideLevel = previousLevel}
                      )
                        | firstLevel == fromIntegral level
                            && previousLevel < firstLevel ->
                            S.pure ()
                    _ ->
                      error $
                        "decision-level boundary does not bracket its level: "
                          P.<> show
                            ( level
                            , boundary
                            , firstLit
                            , firstVariable
                            , previousLit
                            , previousVariable
                            )
          checkLevelStart
            levelCount
            trailSize
            (level + 1)
            boundary

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
              | decisionStep /= fromIntegral index ->
                  error $
                    "trail/valuation assignment-step mismatch: "
                      P.<> show (lit, index, decisionStep)
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

    checkWatchMap ::
      Int ->
      Int ->
      S.State (CDCLState s) (Ur IS.IntSet)
    checkWatchMap numVars numClauses = S.do
      Ur (headCount, tailCount, nextCount) <-
        S.zoom watchesL getWatchMapSizes
      if
        headCount == 2 P.* numVars
          && tailCount == headCount
          && nextCount == 2 P.* numClauses
        then checkBuckets headCount nextCount 0 IS.empty
        else
          error $
            "watch storage size mismatch: "
              P.<> show
                ( headCount
                , 2 P.* numVars
                , tailCount
                , nextCount
                , 2 P.* numClauses
                )

    checkBuckets ::
      Int ->
      Int ->
      Int ->
      IS.IntSet ->
      S.State (CDCLState s) (Ur IS.IntSet)
    checkBuckets headCount nextCount bucket seen
      | bucket == headCount = S.pure $ Ur seen
      | otherwise = S.do
          Ur first <-
            S.zoom watchesL $
              getWatchHeadAt bucket
          Ur tailOccurrence <-
            S.zoom watchesL $
              getWatchTailAt bucket
          Ur (lastOccurrence :!: seen') <-
            checkWatchChain nextCount bucket first (-1) seen
          if tailOccurrence == lastOccurrence
            then S.pure ()
            else
              error $
                "watch bucket tail mismatch: "
                  P.<> show (bucket, first, tailOccurrence, lastOccurrence)
          checkBuckets headCount nextCount (bucket + 1) seen'

    checkWatchChain ::
      Int ->
      Int ->
      Int ->
      Int ->
      IS.IntSet ->
      S.State (CDCLState s) (Ur (Pair Int IS.IntSet))
    checkWatchChain _ _ (-1) previous seen =
      S.pure $ Ur (previous :!: seen)
    checkWatchChain nextCount bucket occurrence _ seen
      | occurrence < 0 || occurrence >= nextCount =
          error $
            "watch occurrence out of bounds: "
              P.<> show (bucket, occurrence, nextCount)
      | IS.member occurrence seen =
          error $
            "duplicate or cyclic watch occurrence: "
              P.<> show (bucket, occurrence)
      | otherwise = S.do
          let cid = watchOccurrenceClause occurrence
              watchSlot = watchOccurrenceSlot occurrence
          Ur watchedIndices <-
            S.zoom clausesL $
              getWatchedLitIndices cid
          case (watchSlot, watchedIndices) of
            (W1, _) -> S.pure ()
            (W2, WatchTheseI {}) -> S.pure ()
            (W2, WatchOneI {}) ->
              error $
                "inactive second watch occurrence is linked: "
                  P.<> show (bucket, occurrence, cid)
          Ur watched <-
            S.zoom clausesL $
              getWatchedLits cid
          let watchedLit = watchLitOf watchSlot watched
          if litBucketIndex watchedLit == bucket
            then S.pure ()
            else
              error $
                "watch occurrence bucket/literal mismatch: "
                  P.<> show
                    (bucket, occurrence, cid, watchSlot, watchedLit)
          Ur next <-
            S.zoom watchesL $
              getNextWatchOccurrence occurrence
          checkWatchChain
            nextCount
            bucket
            next
            occurrence
            (IS.insert occurrence seen)

    checkActiveWatches ::
      Int ->
      IS.IntSet ->
      Int ->
      S.State (CDCLState s) ()
    checkActiveWatches numClauses seen clauseIndex
      | clauseIndex == numClauses = S.pure ()
      | otherwise = S.do
          let cid = ClauseId clauseIndex
              first = watchOccurrence cid W1
              second = watchOccurrence cid W2
          Ur watchedIndices <-
            S.zoom clausesL $
              getWatchedLitIndices cid
          if IS.member first seen
            then S.pure ()
            else
              error $
                "active first watch occurrence is missing: "
                  P.<> show cid
          case watchedIndices of
            WatchOneI {} ->
              if IS.member second seen
                then
                  error $
                    "inactive second watch occurrence is present: "
                      P.<> show cid
                else S.pure ()
            WatchTheseI {} ->
              if IS.member second seen
                then S.pure ()
                else
                  error $
                    "active second watch occurrence is missing: "
                      P.<> show cid
          checkActiveWatches numClauses seen (clauseIndex + 1)

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
              error $
                "BCP fixpoint contains unit/conflicting clause: "
                  P.<> show
                    ( ClauseId index
                    , U.toList clauseLits
                    , unassignedCount
                    , watched
                    , firstValue
                    , secondValue
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
propagateUnit mlit =
  propagateFrom case mlit of
    Nothing -> SeedRootUnits
    Just (lit, reason) -> EnqueueLit lit reason

propagateFrom :: (HasCallStack) => PropagationStart -> S.State (CDCLState s) PropResult
propagateFrom start = S.do
  mconflict <-
    case start of
      SeedRootUnits -> seedRootUnits
      EnqueueLit lit reason -> enqueue reason lit
      ResumePropagation -> S.pure Nothing
  case mconflict of
    Just conflict -> S.pure conflict
    Nothing -> drainTrail
  where
    enqueue :: ClauseId -> Lit -> S.State (CDCLState s) (Maybe PropResult)
    enqueue reason lit = S.do
      result <- assertLit reason lit
      case result of
        ContradictingAssertion
          | reason < 0 ->
              error $
                "reasonless decision enqueue contradicted an existing assignment: "
                  P.<> show lit
          | otherwise -> S.pure $ Just $ ConflictFound reason
        AlreadyAsserted
          | reason < 0 ->
              error $
                "reasonless decision enqueue duplicated an existing assignment: "
                  P.<> show lit
          | otherwise -> S.do
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
          let falseLit = negL lit
          Ur firstOccurrence <- S.zoom watchesL $ detachWatchBucket falseLit
          loop falseLit firstOccurrence
      where
        loop :: Lit -> Int -> S.State (CDCLState s) PropResult
        loop _ (-1) = drainTrail
        loop !falseLit !occurrence = S.do
          Ur nextOccurrence <-
            S.zoom watchesL $
              getNextWatchOccurrence occurrence
          bumpWatchVisit
          let cid = watchOccurrenceClause occurrence
              watchSlot = watchOccurrenceSlot occurrence
          resl <- propLit falseLit watchSlot cid
          case resl of
            Nothing -> S.do
              keepWatch falseLit occurrence
              loop falseLit nextOccurrence
            Just Conflict -> S.do
              keepWatch falseLit occurrence
              restoreWatchChain falseLit nextOccurrence
              S.pure $ ConflictFound cid
            Just (Satisfied m) ->
              case m of
                Just ((w :!: old) :!: (new :!: newIdx)) -> S.do
                  bumpWatchMove
                  updateWatchLit cid w old new newIdx
                  loop falseLit nextOccurrence
                Nothing -> S.do
                  keepWatch falseLit occurrence
                  loop falseLit nextOccurrence
            Just (WatchChangedFromTo w old new newIdx) -> S.do
              bumpWatchMove
              updateWatchLit cid w old new newIdx
              loop falseLit nextOccurrence
            Just (Unit newLit) ->
              move newLit & \(Ur newLit) -> S.do
                keepWatch falseLit occurrence
                result <- enqueue cid newLit
                case result of
                  Just conflict -> S.do
                    restoreWatchChain falseLit nextOccurrence
                    S.pure conflict
                  Nothing -> loop falseLit nextOccurrence

        keepWatch :: Lit -> Int -> S.State (CDCLState s) ()
        keepWatch lit occurrence =
          S.zoom watchesL $
            appendWatchOccurrence lit occurrence

        restoreWatchChain :: Lit -> Int -> S.State (CDCLState s) ()
        restoreWatchChain _ (-1) = S.pure ()
        restoreWatchChain lit occurrence = S.do
          Ur nextOccurrence <-
            S.zoom watchesL $
              getNextWatchOccurrence occurrence
          keepWatch lit occurrence
          restoreWatchChain lit nextOccurrence

classifyClause :: ClauseId -> S.State (CDCLState s) (Ur ClauseClassification)
classifyClause cid = S.do
  Ur clauseLits <- S.zoom clausesL $ getClauseLits cid
  Ur ClauseScan {..} <- S.uses valuationL \valuation ->
    foldlLin'
      valuation
      ( \valuation (Ur scan) lit ->
          LUA.unsafeGet (fromVarId $ litVar lit) valuation
            & \(Ur variable, valuation) ->
              let scan' =
                    case variable of
                      Indefinite ->
                        scan
                          { scanUnassignedCount = scanUnassignedCount scan + 1
                          , scanUnassignedLit = Just lit
                          }
                      Definite {..}
                        | value == isPositive lit ->
                            scan {scanSatisfied = True}
                        | otherwise -> scan
               in (Ur scan', valuation)
      )
      (ClauseScan False 0 Nothing)
      (U.toList clauseLits)
  S.pure $
    Ur $
      if scanSatisfied
        then ClauseSatisfied
        else case scanUnassignedCount of
          0 -> ClauseConflict
          1 -> case scanUnassignedLit of
            Just unitLit -> ClauseUnit unitLit
            Nothing ->
              error $ "classifyClause: missing unit literal " P.<> show cid
          _ -> ClauseOpen

#ifdef HERBRAND_CDCL_INSTRUMENTED
validateAssertingReason :: ClauseId -> Lit -> S.State (CDCLState s) ()
validateAssertingReason reason expected = S.do
  Ur classification <- classifyClause reason
  case classification of
    ClauseUnit actual
      | actual == expected -> S.pure ()
    _ ->
      error $
        "non-asserting reason after backtrack: "
          P.<> show (reason, expected, classification)
#else
validateAssertingReason :: ClauseId -> Lit -> S.State (CDCLState s) ()
{-# INLINE validateAssertingReason #-}
validateAssertingReason reason truth =
  reason `lseq` truth `lseq` S.pure ()
#endif

updateWatchLit :: ClauseId -> WatchVar %1 -> Lit %1 -> Lit %1 -> Index %1 -> S.State (CDCLState s) ()
{-# INLINE updateWatchLit #-}
updateWatchLit cid w old new idx =
  old `lseq`
    PL.move (w, new)
      & \(Ur (w, new)) -> S.do
        setWatchVar cid w idx
        S.zoom watchesL PL.$
          linkWatchOccurrence new PL.$
            watchOccurrence cid w

assertLit :: ClauseId -> Lit -> S.State (CDCLState s) AssertionResult
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
      Ur decideLevel <- currentDecideLevel
      Ur trailSize <- S.uses trailL LUV.size
      let decisionStep = fromIntegral trailSize
      valuationL
        S.%= LUA.unsafeSet vid Definite {value = isPositive lit, ..}
      trailL S.%= LUV.push lit
      bumpTrailAppend
      S.pure NewlyAsserted
    Ur Definite {..}
      | isPositive lit == value -> S.pure AlreadyAsserted
      | otherwise -> S.pure ContradictingAssertion

-- | Propagate Literal.
propLit :: Lit -> WatchVar -> ClauseId -> S.State (CDCLState s) (Maybe UnitResult)
propLit falseLit watchSlot cid = S.do
  Ur wlits <- S.zoom clausesL (getWatchedLits cid)
  let !l1 = getLit1 wlits
      watchedLit = watchLitOf watchSlot wlits
      otherLit = case watchSlot of
        W1 -> getLit2 wlits
        W2 -> Just l1
  if watchedLit /= falseLit
    then
      error $
        "watch occurrence is in the wrong literal bucket: "
          <> show (cid, watchSlot, falseLit, watchedLit)
    else case otherLit of
      Nothing -> findReplacement Nothing
      Just other -> S.do
        Ur otherValue <- move C.<$> S.zoom valuationL (evalLit other)
        case otherValue of
          Just True -> S.pure $ Just $ Satisfied Nothing
          _ -> findReplacement $ Just (other, otherValue)
  where
    findReplacement other = S.do
      mnext <- findNextAvailable watchSlot cid
      case mnext of
        Just next -> S.pure $ Just $ fromNextSlot next
        Nothing -> case other of
          Nothing -> S.pure $ Just Conflict
          Just (otherLit, Nothing) -> S.pure $ Just $ Unit otherLit
          Just (otherLit, Just False) ->
            otherLit `lseq` S.pure (Just Conflict)
          Just (otherLit, Just True) ->
            otherLit `lseq`
              error "propLit: satisfied blocker reached replacement search"

fromNextSlot :: NextSlot %1 -> UnitResult
fromNextSlot (NextSlot True w old new lid) = Satisfied $ Just $ (w :!: old) :!: (new :!: lid)
fromNextSlot (NextSlot False w old new lid) = WatchChangedFromTo w old new lid

data NextSlot = NextSlot
  { satisfied :: !Bool
  , target :: !WatchVar
  , oldLit, newLit :: {-# UNPACK #-} !Lit
  , litIndexInClause :: {-# UNPACK #-} !Index
  }
  deriving (Show, P.Eq, P.Ord, GHC.Generic)

findNextAvailable :: WatchVar -> ClauseId -> S.State (CDCLState s) (Maybe NextSlot)
findNextAvailable w cid = S.do
  Ur (lits, watchedIndices) <-
    S.zoom clausesL $
      getClauseSearch cid
  Ur numInitialClauses <-
    move C.<$> S.use numInitialClausesL
  let !watchedIndex = watchIndexOf w watchedIndices
      !origLit = U.unsafeIndex lits watchedIndex
      !clauseLength = U.length lits
      !isLearnt = unClauseId cid P.>= numInitialClauses
      !cursor
        | isLearnt || clauseLength P.<= 8 = 0
        | watchedIndex + 1 == clauseLength = 0
        | otherwise = watchedIndex + 1
      -- Retain the incumbent satisfying-literal preference for learnt clauses:
      -- it materially reduces future watch traffic in this solver's learning
      -- scheme. Long original clauses stop at the first non-false literal so
      -- a moving watch does not repeatedly scan the whole clause.
      !preferSatisfied =
        clauseLength P.<= 8
          || isLearnt
  Ur (mnext :!: inspections) <-
    S.uses valuationL $
      search
        lits
        watchedIndices
        origLit
        clauseLength
        cursor
        preferSatisfied
        0
        0
        Nothing
  bumpLiteralInspections inspections
  S.pure mnext
  where
    search ::
      U.Vector Lit ->
      WatchedLitIndices ->
      Lit ->
      Int ->
      Index ->
      Bool ->
      Int ->
      Int ->
      Maybe (Index, Lit) ->
      Valuation %1 ->
      (Ur (Pair (Maybe NextSlot) Int), Valuation)
    search lits watchedIndices origLit clauseLength cursor preferSatisfied !offset !inspections undetermined valuation
      | offset == clauseLength = case undetermined of
          Nothing -> (Ur (Nothing :!: inspections), valuation)
          Just (index, candidate) ->
            selectReplacement
              origLit
              index
              candidate
              False
              inspections
              valuation
      | otherwise =
          let rawIndex = cursor + offset
              index
                | rawIndex < clauseLength = rawIndex
                | otherwise = rawIndex - clauseLength
           in if index `elemWatchLitIdx` watchedIndices
                then
                  search
                    lits
                    watchedIndices
                    origLit
                    clauseLength
                    cursor
                    preferSatisfied
                    (offset + 1)
                    inspections
                    undetermined
                    valuation
                else
                  let candidate = U.unsafeIndex lits index
                   in LUA.unsafeGet (fromVarId $ litVar candidate) valuation
                        & \(Ur variable, valuation) ->
                          let !inspections' = inspections + 1
                              value = case variable of
                                Definite {..} -> Just $ isPositive candidate == value
                                Indefinite -> Nothing
                           in case value of
                                Just False ->
                                  search
                                    lits
                                    watchedIndices
                                    origLit
                                    clauseLength
                                    cursor
                                    preferSatisfied
                                    (offset + 1)
                                    inspections'
                                    undetermined
                                    valuation
                                Just True ->
                                  selectReplacement
                                    origLit
                                    index
                                    candidate
                                    True
                                    inspections'
                                    valuation
                                Nothing
                                  | preferSatisfied ->
                                      search
                                        lits
                                        watchedIndices
                                        origLit
                                        clauseLength
                                        cursor
                                        preferSatisfied
                                        (offset + 1)
                                        inspections'
                                        case undetermined of
                                          Nothing -> Just (index, candidate)
                                          Just {} -> undetermined
                                        valuation
                                  | otherwise ->
                                      selectReplacement
                                        origLit
                                        index
                                        candidate
                                        False
                                        inspections'
                                        valuation

    selectReplacement ::
      Lit ->
      Index ->
      Lit ->
      Bool ->
      Int ->
      Valuation %1 ->
      (Ur (Pair (Maybe NextSlot) Int), Valuation)
    selectReplacement origLit index candidate isSatisfied inspections valuation =
      ( Ur
          ( Just
              NextSlot
                { satisfied = isSatisfied
                , target = w
                , oldLit = origLit
                , newLit = candidate
                , litIndexInClause = index
                }
              :!: inspections
          )
      , valuation
      )

    watchIndexOf :: WatchVar -> WatchedLitIndices -> Index
    watchIndexOf W1 (WatchOneI first) = first
    watchIndexOf W1 (WatchTheseI first _) = first
    watchIndexOf W2 (WatchTheseI _ second) = second
    watchIndexOf W2 WatchOneI {} =
      error "findNextAvailable: inactive second watch"

evalLit :: Lit -> S.State Valuation (Maybe Bool)
evalLit l = S.do
  Ur m <- S.state $ LUA.unsafeGet (fromVarId $ litVar l)
  S.pure case m of
    Definite {..} -> Just $ isPositive l == value
    Indefinite -> Nothing
