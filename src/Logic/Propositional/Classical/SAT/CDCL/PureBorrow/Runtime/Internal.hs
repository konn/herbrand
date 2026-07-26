{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE NoImplicitPrelude #-}

{- |
Production ownership topology for the Pure Borrow CDCL solver.

The aggregate is an ordinary strict record.  It is never placed behind a
single reference: each array/vector is an independent owner and only VSIDS,
whose persistent root is replaced as a value, uses 'Ref.Ref'.
-}
module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Runtime.Internal (
  CDCLStore,
  ClauseArena,
  WatchMap,
  AnalysisWorkspace,
  PreparedCDCL,
  SolverMeta (..),
  prepareCDCL,
  preparedMeta,
  newCDCLStore,
  finishValuation,
  disposeCDCLStore,
  valuationField,
  trailField,
  levelStartsField,
  clausesField,
  watchesField,
  vsidsField,
  analysisField,
  analysisEpochField,
  analysisStampsField,
  analysisLiteralsField,
  clauseLiteralsField,
  clauseBodiesField,
  watchHeadsField,
  watchTailsField,
  watchNextsField,
) where

import Control.Monad.Borrow.Pure (Linearly)
import Control.Monad.ST (runST)
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.IntPSQ qualified as PSQ
import Data.List qualified as List
import Data.Ord (Down (..))
import Data.Record.Linear.Borrow.Experimental.PatternMatch (RecordLabel)
import Data.Ref.Linear qualified as Ref
import Data.Vector qualified as V
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal qualified as Grow
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import Data.Word (Word64)
import GHC.Exts qualified as GHC
import Logic.Propositional.Classical.SAT.CDCL.Types hiding (WatchMap)
import Logic.Propositional.Classical.SAT.Types (SatResult (..))
import Logic.Propositional.Syntax.General (Literal (..))
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive (
  CNF (..),
  CNFClause (..),
 )
import Prelude.Linear
import Prelude qualified as NonLinear

data ClauseArena = ClauseArena
  { clauseLiterals :: !(Boxed.Vector (Ur (U.Vector Lit)))
  , clauseBodies :: !(Grow.Vector ClauseBody)
  }

data WatchMap = WatchMap
  { watchHeads :: !(Fixed.UArray Int)
  , watchTails :: !(Fixed.UArray Int)
  , watchNexts :: !(Grow.Vector Int)
  }

data AnalysisWorkspace = AnalysisWorkspace
  { analysisEpoch :: !(Fixed.UArray Word64)
  , analysisStamps :: !(Fixed.UArray Word64)
  , analysisLiterals :: !(Fixed.UArray Lit)
  }

data CDCLStore s = CDCLStore
  { valuation :: !(Fixed.UArray Variable)
  , trail :: !(Fixed.UArray Lit)
  , levelStarts :: !(Fixed.UArray Step)
  , clauses :: !ClauseArena
  , watches :: !WatchMap
  , vsids :: !(Ref.Ref (VSIDSState s))
  , analysis :: !AnalysisWorkspace
  }

type role CDCLStore nominal

data SolverMeta = SolverMeta
  { numInitialClauses :: {-# UNPACK #-} !Int
  , numVariables :: {-# UNPACK #-} !Int
  }
  deriving (NonLinear.Show, NonLinear.Eq)

data PreparedCDCL = PreparedCDCL
  { preparedMeta :: !SolverMeta
  , preparedClauseLiterals :: !(V.Vector (Ur (U.Vector Lit)))
  , preparedClauseBodies :: !(U.Vector ClauseBody)
  , preparedWatchHeads :: !(U.Vector Int)
  , preparedWatchTails :: !(U.Vector Int)
  , preparedWatchNexts :: !(U.Vector Int)
  }

prepareCDCL :: CNF VarId -> Either (Ur (SatResult ())) PreparedCDCL
prepareCDCL (CNF rawClauses)
  | NonLinear.null rawClauses =
      Left (Ur (Satisfiable ()))
  | NonLinear.any
      (\clause -> NonLinear.null (clauseLits clause))
      rawClauses =
      Left (Ur Unsat)
  | otherwise =
      let !normalized =
            List.nub
              ( NonLinear.fmap
                  ( \clause ->
                      List.nub
                        (NonLinear.fmap encodeLit (clauseLits clause))
                  )
                  rawClauses
              )
          !clauses = NonLinear.fmap buildClause normalized
          !maximumVariable =
            NonLinear.maximum
              ( NonLinear.fmap
                  (\literal -> fromVarId (literalVariable literal))
                  (NonLinear.concatMap clauseLits rawClauses)
              )
          !variableCount = maximumVariable + 1
          !clauseCount = NonLinear.length clauses
          (!heads, !tails, !nexts) =
            buildWatchVectors variableCount clauses
       in Right
            PreparedCDCL
              { preparedMeta =
                  SolverMeta
                    { numInitialClauses = clauseCount
                    , numVariables = variableCount
                    }
              , preparedClauseLiterals =
                  V.fromList
                    ( NonLinear.fmap
                        (\clause -> Ur (lits clause))
                        clauses
                    )
              , preparedClauseBodies =
                  U.fromList
                    ( NonLinear.fmap
                        ( \Clause {watched1, watched2} ->
                            ClauseBody
                              { wat1 = watched1
                              , wat2 = watched2
                              }
                        )
                        clauses
                    )
              , preparedWatchHeads = heads
              , preparedWatchTails = tails
              , preparedWatchNexts = nexts
              }

literalVariable :: Literal VarId -> VarId
literalVariable (Positive variable) = variable
literalVariable (Negative variable) = variable

buildClause :: [Lit] -> Clause
buildClause [] =
  Clause
    { lits = U.empty
    , watched1 = -1
    , watched2 = -1
    }
buildClause [literal] =
  Clause
    { lits = U.singleton literal
    , watched1 = 0
    , watched2 = -1
    }
buildClause literals =
  Clause
    { lits = U.fromList literals
    , watched1 = 0
    , watched2 = 1
    }

buildWatchVectors ::
  Int ->
  [Clause] ->
  (U.Vector Int, U.Vector Int, U.Vector Int)
buildWatchVectors variableCount initialClauses = runST do
  heads <- UM.replicate (2 * variableCount) (-1)
  tails <- UM.replicate (2 * variableCount) (-1)
  nexts <- UM.replicate (2 * NonLinear.length initialClauses) (-1)
  let add occurrence literal = do
        let !bucket = litBucketIndex literal
        oldTail <- UM.unsafeRead tails bucket
        if oldTail < 0
          then UM.unsafeWrite heads bucket occurrence
          else UM.unsafeWrite nexts oldTail occurrence
        UM.unsafeWrite tails bucket occurrence
  NonLinear.mapM_
    ( \(clauseIndex, Clause {lits, watched1, watched2}) -> do
        let !clauseId = ClauseId clauseIndex
        if watched1 >= 0
          then
            add
              (watchOccurrence clauseId W1)
              (U.unsafeIndex lits watched1)
          else NonLinear.pure ()
        if watched2 >= 0
          then
            add
              (watchOccurrence clauseId W2)
              (U.unsafeIndex lits watched2)
          else NonLinear.pure ()
    )
    (NonLinear.zip [0 ..] initialClauses)
  (,,)
    NonLinear.<$> U.unsafeFreeze heads
    NonLinear.<*> U.unsafeFreeze tails
    NonLinear.<*> U.unsafeFreeze nexts

newCDCLStore :: PreparedCDCL -> Linearly %1 -> CDCLStore s
{-# NOINLINE newCDCLStore #-}
newCDCLStore = GHC.noinline \prepared linear ->
  dup linear & \(valuationLinear, rest1) ->
    dup rest1 & \(trailLinear, rest2) ->
      dup rest2 & \(levelsLinear, rest3) ->
        dup rest3 & \(literalsLinear, rest4) ->
          dup rest4 & \(bodiesLinear, rest5) ->
            dup rest5 & \(headsLinear, rest6) ->
              dup rest6 & \(tailsLinear, rest7) ->
                dup rest7 & \(nextsLinear, rest8) ->
                  dup rest8 & \(epochLinear, rest9) ->
                    dup rest9 & \(stampsLinear, rest10) ->
                      dup rest10 & \(scratchLinear, vsidsLinear) ->
                        let !meta = preparedMeta prepared
                            !variableCount = numVariables meta
                            !valuationOwner =
                              Fixed.constant
                                variableCount
                                Indefinite
                                valuationLinear
                            !trailOwner =
                              Fixed.fromVector
                                (U.replicate variableCount (PosL 0))
                                trailLinear
                            !levelStartsOwner =
                              Fixed.fromVector
                                (U.replicate (variableCount + 1) 0)
                                levelsLinear
                            !literalOwner =
                              Boxed.fromVector
                                (preparedClauseLiterals prepared)
                                literalsLinear
                            !bodyOwner =
                              Grow.fromVector
                                (preparedClauseBodies prepared)
                                bodiesLinear
                            !headOwner =
                              Fixed.fromVector
                                (preparedWatchHeads prepared)
                                headsLinear
                            !tailOwner =
                              Fixed.fromVector
                                (preparedWatchTails prepared)
                                tailsLinear
                            !nextOwner =
                              Grow.fromVector
                                (preparedWatchNexts prepared)
                                nextsLinear
                            !vsidsOwner =
                              Ref.new
                                ( VSIDSState
                                    ( PSQ.fromList
                                        [ (variable, Down 0, ())
                                        | variable <-
                                            [0 .. variableCount - 1]
                                        ]
                                    )
                                    PSQ.empty
                                    0
                                    True
                                    1
                                )
                                vsidsLinear
                            !epochOwner =
                              Fixed.constant
                                1
                                initialAnalysisEpoch
                                epochLinear
                            !stampsOwner =
                              Fixed.constant
                                variableCount
                                initialAnalysisStamp
                                stampsLinear
                            !scratchOwner =
                              Fixed.fromVector
                                (U.replicate variableCount (PosL 0))
                                scratchLinear
                         in CDCLStore
                              { valuation = valuationOwner
                              , trail = trailOwner
                              , levelStarts = levelStartsOwner
                              , clauses =
                                  ClauseArena
                                    { clauseLiterals = literalOwner
                                    , clauseBodies = bodyOwner
                                    }
                              , watches =
                                  WatchMap
                                    { watchHeads = headOwner
                                    , watchTails = tailOwner
                                    , watchNexts = nextOwner
                                    }
                              , vsids = vsidsOwner
                              , analysis =
                                  AnalysisWorkspace
                                    { analysisEpoch = epochOwner
                                    , analysisStamps = stampsOwner
                                    , analysisLiterals = scratchOwner
                                    }
                              }

finishValuation ::
  CDCLStore s %1 ->
  Ur (U.Vector Variable)
{-# NOINLINE finishValuation #-}
finishValuation
  ( CDCLStore
      valuationOwner
      trailOwner
      levelStartsOwner
      (ClauseArena literalOwner bodyOwner)
      (WatchMap headOwner tailOwner nextOwner)
      vsidsOwner
      (AnalysisWorkspace epochOwner stampsOwner scratchOwner)
    ) =
    case Fixed.toVector valuationOwner of
      Ur frozenValuation ->
        Fixed.dispose trailOwner `lseq`
          Fixed.dispose levelStartsOwner `lseq`
            Boxed.dispose literalOwner `lseq`
              Grow.dispose bodyOwner `lseq`
                Fixed.dispose headOwner `lseq`
                  Fixed.dispose tailOwner `lseq`
                    Grow.dispose nextOwner `lseq`
                      consume (Ref.free vsidsOwner) `lseq`
                        Fixed.dispose epochOwner `lseq`
                          Fixed.dispose stampsOwner `lseq`
                            Fixed.dispose scratchOwner `lseq`
                              Ur frozenValuation

disposeCDCLStore :: CDCLStore s %1 -> ()
{-# INLINE disposeCDCLStore #-}
disposeCDCLStore
  ( CDCLStore
      valuationOwner
      trailOwner
      levelStartsOwner
      (ClauseArena literalOwner bodyOwner)
      (WatchMap headOwner tailOwner nextOwner)
      vsidsOwner
      (AnalysisWorkspace epochOwner stampsOwner scratchOwner)
    ) =
    Fixed.dispose valuationOwner `lseq`
      Fixed.dispose trailOwner `lseq`
        Fixed.dispose levelStartsOwner `lseq`
          Boxed.dispose literalOwner `lseq`
            Grow.dispose bodyOwner `lseq`
              Fixed.dispose headOwner `lseq`
                Fixed.dispose tailOwner `lseq`
                  Grow.dispose nextOwner `lseq`
                    consume (Ref.free vsidsOwner) `lseq`
                      Fixed.dispose epochOwner `lseq`
                        Fixed.dispose stampsOwner `lseq`
                          Fixed.dispose scratchOwner

valuationField ::
  RecordLabel
    (CDCLStore s)
    "valuation"
    (Fixed.UArray Variable)
valuationField = #valuation

trailField ::
  RecordLabel (CDCLStore s) "trail" (Fixed.UArray Lit)
trailField = #trail

levelStartsField ::
  RecordLabel
    (CDCLStore s)
    "levelStarts"
    (Fixed.UArray Step)
levelStartsField = #levelStarts

clausesField ::
  RecordLabel (CDCLStore s) "clauses" ClauseArena
clausesField = #clauses

watchesField ::
  RecordLabel (CDCLStore s) "watches" WatchMap
watchesField = #watches

vsidsField ::
  RecordLabel
    (CDCLStore s)
    "vsids"
    (Ref.Ref (VSIDSState s))
vsidsField = #vsids

analysisField ::
  RecordLabel (CDCLStore s) "analysis" AnalysisWorkspace
analysisField = #analysis

analysisEpochField ::
  RecordLabel AnalysisWorkspace "analysisEpoch" (Fixed.UArray Word64)
analysisEpochField = #analysisEpoch

analysisStampsField ::
  RecordLabel
    AnalysisWorkspace
    "analysisStamps"
    (Fixed.UArray Word64)
analysisStampsField = #analysisStamps

analysisLiteralsField ::
  RecordLabel
    AnalysisWorkspace
    "analysisLiterals"
    (Fixed.UArray Lit)
analysisLiteralsField = #analysisLiterals

clauseLiteralsField ::
  RecordLabel
    ClauseArena
    "clauseLiterals"
    (Boxed.Vector (Ur (U.Vector Lit)))
clauseLiteralsField = #clauseLiterals

clauseBodiesField ::
  RecordLabel
    ClauseArena
    "clauseBodies"
    (Grow.Vector ClauseBody)
clauseBodiesField = #clauseBodies

watchHeadsField ::
  RecordLabel WatchMap "watchHeads" (Fixed.UArray Int)
watchHeadsField = #watchHeads

watchTailsField ::
  RecordLabel WatchMap "watchTails" (Fixed.UArray Int)
watchTailsField = #watchTails

watchNextsField ::
  RecordLabel WatchMap "watchNexts" (Grow.Vector Int)
watchNextsField = #watchNexts
