{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE NoImplicitPrelude #-}

{- |
The record topology exercised by the Phase 1 Pure Borrow propagation spike.

This is deliberately an owner record, not a reference to an aggregate state.
Each field owns an independently borrowable store. The algorithm only receives
typed labels, so constructors and ordinary owner selectors stay confined here.
-}
module Logic.Propositional.Classical.SAT.CDCL.PureBorrow.Store.Internal (
  CDCLStore,
  ClauseArena,
  WatchMap,
  VSIDSState,
  CDCLSeed (..),
  CDCLSnapshot (..),
  newCDCLStore,
  freezeCDCLStore,
  bumpVSIDS,
  valuationField,
  trailField,
  levelStartsField,
  clausesField,
  watchesField,
  vsidsField,
  clauseLiteralsField,
  clauseBodiesField,
  watchHeadsField,
  watchTailsField,
  watchNextsField,
) where

import Control.Monad.Borrow.Pure (Linearly, Ur (..), dup)
import Data.Array.Mutable.Linear.Unboxed.Borrow.Internal qualified as Fixed
import Data.Record.Linear.Borrow.Experimental.PatternMatch (RecordLabel)
import Data.Ref.Linear qualified as Ref
import Data.Vector qualified as V
import Data.Vector.Mutable.Linear.Boxed.Borrow.Internal qualified as Boxed
import Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal qualified as Grow
import Data.Vector.Unboxed qualified as U
import GHC.Exts qualified as GHC
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as NonLinear

-- | Mutable clause storage split into immutable literal vectors and bodies.
data ClauseArena = ClauseArena
  { clauseLiterals :: !(Boxed.Vector (Ur (U.Vector Int)))
  , clauseBodies :: !(Grow.Vector Int)
  }

-- | Watch buckets and occurrence links are independently owned stores.
data WatchMap = WatchMap
  { watchHeads :: !(Fixed.UArray Int)
  , watchTails :: !(Fixed.UArray Int)
  , watchNexts :: !(Grow.Vector Int)
  }

{- | A deliberately tiny VSIDS root for the architecture spike.

The full port replaces the counter payload with the existing pair of
priority queues and activity scalars without changing its ownership shape.
-}
data VSIDSState s = VSIDSState
  { vsidsVisitCount :: {-# UNPACK #-} !Int
  }

-- | The aggregate owner. No aggregate 'Ref' exists.
data CDCLStore s = CDCLStore
  { valuation :: !(Fixed.UArray Int)
  , trail :: !(Fixed.UArray Int)
  , levelStarts :: !(Fixed.UArray Int)
  , clauses :: !ClauseArena
  , watches :: !WatchMap
  , vsids :: !(Ref.Ref (VSIDSState s))
  }

type role VSIDSState nominal

type role CDCLStore nominal

-- | Immutable allocation input used by the spike and later preparation code.
data CDCLSeed = CDCLSeed
  { seedValuation :: !(U.Vector Int)
  , seedTrail :: !(U.Vector Int)
  , seedLevelStarts :: !(U.Vector Int)
  , seedClauseLiterals :: !(V.Vector (Ur (U.Vector Int)))
  , seedClauseBodies :: !(U.Vector Int)
  , seedWatchHeads :: !(U.Vector Int)
  , seedWatchTails :: !(U.Vector Int)
  , seedWatchNexts :: !(U.Vector Int)
  , seedVSIDSVisits :: {-# UNPACK #-} !Int
  }

-- | Frozen evidence that every independently borrowed owner was reclaimed.
data CDCLSnapshot = CDCLSnapshot
  { snapshotValuation :: !(U.Vector Int)
  , snapshotTrail :: !(U.Vector Int)
  , snapshotLevelStarts :: !(U.Vector Int)
  , snapshotClauseLiterals :: !(V.Vector (U.Vector Int))
  , snapshotClauseBodies :: !(U.Vector Int)
  , snapshotWatchHeads :: !(U.Vector Int)
  , snapshotWatchTails :: !(U.Vector Int)
  , snapshotWatchNexts :: !(U.Vector Int)
  , snapshotVSIDSVisits :: {-# UNPACK #-} !Int
  }
  deriving (NonLinear.Show, NonLinear.Eq)

-- | Allocate every owner field independently from one linear witness.
newCDCLStore :: CDCLSeed -> Linearly %1 -> CDCLStore s
{-# NOINLINE newCDCLStore #-}
newCDCLStore = GHC.noinline \seed linear ->
  dup linear & \(valuationLinear, rest1) ->
    dup rest1 & \(trailLinear, rest2) ->
      dup rest2 & \(levelsLinear, rest3) ->
        dup rest3 & \(clauseLiteralsLinear, rest4) ->
          dup rest4 & \(clauseBodiesLinear, rest5) ->
            dup rest5 & \(watchHeadsLinear, rest6) ->
              dup rest6 & \(watchTailsLinear, rest7) ->
                dup rest7 & \(watchNextsLinear, vsidsLinear) ->
                  let !valuationOwner =
                        Fixed.fromVector
                          (seedValuation seed)
                          valuationLinear
                      !trailOwner =
                        Fixed.fromVector
                          (seedTrail seed)
                          trailLinear
                      !levelStartsOwner =
                        Fixed.fromVector
                          (seedLevelStarts seed)
                          levelsLinear
                      !clauseLiteralsOwner =
                        Boxed.fromVector
                          (seedClauseLiterals seed)
                          clauseLiteralsLinear
                      !clauseBodiesOwner =
                        Grow.fromVector
                          (seedClauseBodies seed)
                          clauseBodiesLinear
                      !watchHeadsOwner =
                        Fixed.fromVector
                          (seedWatchHeads seed)
                          watchHeadsLinear
                      !watchTailsOwner =
                        Fixed.fromVector
                          (seedWatchTails seed)
                          watchTailsLinear
                      !watchNextsOwner =
                        Grow.fromVector
                          (seedWatchNexts seed)
                          watchNextsLinear
                      !vsidsOwner =
                        Ref.new
                          (VSIDSState (seedVSIDSVisits seed))
                          vsidsLinear
                   in CDCLStore
                        { valuation = valuationOwner
                        , trail = trailOwner
                        , levelStarts = levelStartsOwner
                        , clauses =
                            ClauseArena
                              { clauseLiterals = clauseLiteralsOwner
                              , clauseBodies = clauseBodiesOwner
                              }
                        , watches =
                            WatchMap
                              { watchHeads = watchHeadsOwner
                              , watchTails = watchTailsOwner
                              , watchNexts = watchNextsOwner
                              }
                        , vsids = vsidsOwner
                        }

-- | Consume the reclaimed owner and freeze every store independently.
freezeCDCLStore :: CDCLStore s %1 -> Ur CDCLSnapshot
{-# NOINLINE freezeCDCLStore #-}
freezeCDCLStore =
  GHC.noinline $
    Unsafe.toLinear
      \( CDCLStore
           valuationOwner
           trailOwner
           levelStartsOwner
           (ClauseArena clauseLiteralsOwner clauseBodiesOwner)
           (WatchMap watchHeadsOwner watchTailsOwner watchNextsOwner)
           vsidsOwner
         ) ->
          case Fixed.toVector valuationOwner of
            Ur valuationVector ->
              case Fixed.toVector trailOwner of
                Ur trailVector ->
                  case Fixed.toVector levelStartsOwner of
                    Ur levelStartsVector ->
                      case Boxed.toVector clauseLiteralsOwner of
                        Ur clauseLiteralsVector ->
                          case Grow.toVector clauseBodiesOwner of
                            Ur clauseBodiesVector ->
                              case Fixed.toVector watchHeadsOwner of
                                Ur watchHeadsVector ->
                                  case Fixed.toVector watchTailsOwner of
                                    Ur watchTailsVector ->
                                      case Grow.toVector watchNextsOwner of
                                        Ur watchNextsVector ->
                                          case Ref.free vsidsOwner of
                                            VSIDSState visits ->
                                              Ur
                                                CDCLSnapshot
                                                  { snapshotValuation =
                                                      valuationVector
                                                  , snapshotTrail =
                                                      trailVector
                                                  , snapshotLevelStarts =
                                                      levelStartsVector
                                                  , snapshotClauseLiterals =
                                                      NonLinear.fmap
                                                        (\(Ur literals) -> literals)
                                                        clauseLiteralsVector
                                                  , snapshotClauseBodies =
                                                      clauseBodiesVector
                                                  , snapshotWatchHeads =
                                                      watchHeadsVector
                                                  , snapshotWatchTails =
                                                      watchTailsVector
                                                  , snapshotWatchNexts =
                                                      watchNextsVector
                                                  , snapshotVSIDSVisits =
                                                      visits
                                                  }

-- | Record one occurrence visit while the VSIDS root is open.
bumpVSIDS :: VSIDSState s %1 -> VSIDSState s
{-# INLINE bumpVSIDS #-}
bumpVSIDS (VSIDSState visits) = VSIDSState (visits + 1)

valuationField ::
  RecordLabel (CDCLStore s) "valuation" (Fixed.UArray Int)
valuationField = #valuation

trailField ::
  RecordLabel (CDCLStore s) "trail" (Fixed.UArray Int)
trailField = #trail

levelStartsField ::
  RecordLabel (CDCLStore s) "levelStarts" (Fixed.UArray Int)
levelStartsField = #levelStarts

clausesField ::
  RecordLabel (CDCLStore s) "clauses" ClauseArena
clausesField = #clauses

watchesField ::
  RecordLabel (CDCLStore s) "watches" WatchMap
watchesField = #watches

vsidsField ::
  RecordLabel (CDCLStore s) "vsids" (Ref.Ref (VSIDSState s))
vsidsField = #vsids

clauseLiteralsField ::
  RecordLabel
    ClauseArena
    "clauseLiterals"
    (Boxed.Vector (Ur (U.Vector Int)))
clauseLiteralsField = #clauseLiterals

clauseBodiesField ::
  RecordLabel ClauseArena "clauseBodies" (Grow.Vector Int)
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
