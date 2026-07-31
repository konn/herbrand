{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}

module CdfMultiStoreScan (
  MultiStoreInput (..),
  MultiStoreEvidence (..),
  MultiStoreOutput (..),
  directEvidenceRoot,
  directHeaderMatchedRoot,
  directHeaderMatchedRootWithVisits,
  directRoot,
  outputVectorDigest,
  pureBorrowDirectRoot,
  pureBorrowDirectEvidenceRoot,
  pureBorrowMixedDirectRoot,
  pureBorrowMixedDirectEvidenceRoot,
  pureBorrowMixedNestedRoot,
  pureBorrowMixedNestedEvidenceRoot,
  pureBorrowNestedRoot,
  pureBorrowNestedEvidenceRoot,
  pureBorrowUnrestrictedDirectRoot,
  pureBorrowUnrestrictedDirectEvidenceRoot,
  pureBorrowUnrestrictedDirectRootWithVisits,
  pureBorrowUnrestrictedNestedRoot,
  pureBorrowUnrestrictedNestedEvidenceRoot,
  pureBorrowUnrestrictedNestedRootWithVisits,
  standardInput,
) where

import Control.DeepSeq (NFData)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Experimental.Borrows (
  Aliases (..),
  reborrowings,
 )
import Control.Syntax.DataFlow qualified as DataFlow
import Data.IORef (IORef, newIORef, readIORef)
import Data.List qualified as List
import Data.Record.Linear.Borrow.Experimental.PatternMatch (
  RecordLabel,
  (.@),
 )
import Data.Vector qualified as V
import Data.Vector.Generic.Mutable.Growable.Linear.Borrow.Unrestricted qualified as UnrestrictedGrow
import Data.Vector.Generic.Mutable.Linear.Borrow.Unrestricted qualified as Unrestricted
import Data.Vector.Mutable qualified as MV
import Data.Vector.Mutable.Growable.Linear.Borrow qualified as BoxedGrow
import Data.Vector.Mutable.Linear.Borrow qualified as BoxedFixed
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import Data.Vector.Unboxed.Mutable.Growable.Linear.Borrow qualified as Grow
import Data.Vector.Unboxed.Mutable.Linear.Borrow qualified as Fixed
import GHC.Exts qualified as GHC
import GHC.Generics (Generic)
import GHC.IO (unsafePerformIO)
import GHC.Int (Int64 (I64#))
import Prelude.Linear
import Prelude qualified as NonLinear

data MultiStoreInput = MultiStoreInput
  { inputNext :: !(U.Vector Int)
  , inputWeight :: !(U.Vector Int)
  , inputMark :: !(U.Vector Int)
  , inputPayload :: !(V.Vector (Int, Int))
  , inputScore :: !(U.Vector Int)
  , inputLink :: !(U.Vector Int)
  }
  deriving stock (Generic)
  deriving anyclass (NFData)

data MultiStoreOutput = MultiStoreOutput
  { outputDigest :: {-# UNPACK #-} !Int64
  , outputMarks :: !(U.Vector Int)
  , outputScores :: !(U.Vector Int)
  }
  deriving stock (Generic, NonLinear.Show, NonLinear.Eq)
  deriving anyclass (NFData)

data MultiStoreEvidence = MultiStoreEvidence
  { evidenceVisitedIndices :: !(U.Vector Int)
  , evidenceEvents :: !(V.Vector TraceEvent)
  , evidenceEventDigest :: {-# UNPACK #-} !Int64
  , evidenceElementReads :: {-# UNPACK #-} !Int
  , evidenceElementWrites :: {-# UNPACK #-} !Int
  , evidenceHeaderReads :: {-# UNPACK #-} !Int
  , evidenceValidationReads :: {-# UNPACK #-} !Int
  , evidenceOutput :: !MultiStoreOutput
  }
  deriving stock (Generic, NonLinear.Show, NonLinear.Eq)
  deriving anyclass (NFData)

data TraceStore
  = NextStore
  | WeightStore
  | MarkStore
  | ScoreStore
  | LinkStore
  deriving stock (Generic, NonLinear.Show, NonLinear.Eq)
  deriving anyclass (NFData)

data TraceEvent
  = ReadIntEvent !TraceStore {-# UNPACK #-} !Int {-# UNPACK #-} !Int
  | ReadPayloadEvent
      {-# UNPACK #-} !Int
      {-# UNPACK #-} !Int
      {-# UNPACK #-} !Int
  | WriteIntEvent !TraceStore {-# UNPACK #-} !Int {-# UNPACK #-} !Int
  deriving stock (Generic, NonLinear.Show, NonLinear.Eq)
  deriving anyclass (NFData)

data FixedRoots = FixedRoots
  { next :: !(Fixed.Vector Int)
  , weight :: !(Fixed.Vector Int)
  , mark :: !(Fixed.Vector Int)
  }

data GrowableRoots = GrowableRoots
  { payload :: !(BoxedGrow.GrowableVector (Int, Int))
  , score :: !(Grow.GrowableVector Int)
  , link :: !(Grow.GrowableVector Int)
  }

data MultiStore = MultiStore
  { fixedRoots :: !FixedRoots
  , growableRoots :: !GrowableRoots
  }

data MixedFixedRoots = MixedFixedRoots
  { mixedNext :: !(Unrestricted.Vector U.Vector Int)
  , mixedWeight :: !(Unrestricted.Vector U.Vector Int)
  , mixedMark :: !(Unrestricted.Vector U.Vector Int)
  }

data MixedStore = MixedStore
  { mixedFixedRoots :: !MixedFixedRoots
  , mixedGrowableRoots :: !MixedGrowableRoots
  }

data MixedGrowableRoots = MixedGrowableRoots
  { mixedPayload :: !(UnrestrictedGrow.GrowableVector V.Vector (Int, Int))
  , mixedScore :: !(UnrestrictedGrow.GrowableVector U.Vector Int)
  , mixedLink :: !(UnrestrictedGrow.GrowableVector U.Vector Int)
  }

nodeCount :: Int
nodeCount = 4096

standardInput :: MultiStoreInput
standardInput =
  MultiStoreInput
    { inputNext =
        U.generate nodeCount \index ->
          (index + 1) `NonLinear.rem` nodeCount
    , inputWeight =
        U.generate nodeCount \index ->
          (index * 17 + 3) `NonLinear.rem` 101
    , inputMark = U.replicate nodeCount 0
    , inputPayload =
        V.generate nodeCount \index ->
          (index `NonLinear.rem` 7, index `NonLinear.rem` 13)
    , inputScore =
        U.generate nodeCount \index ->
          (index * 5 + 11) `NonLinear.rem` 97
    , inputLink = U.replicate nodeCount 0
    }

validateInput :: MultiStoreInput -> Int
{-# NOINLINE validateInput #-}
validateInput input
  | U.length (inputNext input)
      == nodeCount
      && U.length (inputWeight input)
      == nodeCount
      && U.length (inputMark input)
      == nodeCount
      && V.length (inputPayload input)
      == nodeCount
      && U.length (inputScore input)
      == nodeCount
      && U.length (inputLink input)
      == nodeCount
      && nextReads
      == nodeCount
      && linkReads
      == nodeCount =
      6 + nextReads + linkReads
  | otherwise =
      NonLinear.error
        "multi-store scan requires six 4096-element vectors, in-range next indices, and zero links"
  where
    !nextReads =
      U.foldl'
        ( \count value ->
            if value >= 0 && value < nodeCount
              then count + 1
              else -nodeCount
        )
        0
        (inputNext input)
    !linkReads =
      U.foldl'
        ( \count value ->
            if value NonLinear.== 0
              then count + 1
              else -nodeCount
        )
        0
        (inputLink input)

directRoot :: MultiStoreInput -> MultiStoreOutput
{-# NOINLINE directRoot #-}
directRoot input =
  validateInput input `NonLinear.seq` unsafePerformIO do
    next <- U.thaw (inputNext input)
    weight <- U.thaw (inputWeight input)
    mark <- U.thaw (inputMark input)
    payloadBuffer <- V.thaw (inputPayload input)
    scoreBuffer <- U.thaw (inputScore input)
    linkBuffer <- U.thaw (inputLink input)
    payloadHeader <- newIORef (nodeCount, payloadBuffer)
    scoreHeader <- newIORef (nodeCount, scoreBuffer)
    linkHeader <- newIORef (nodeCount, linkBuffer)
    (_, payload) <- readIORef payloadHeader
    (_, score) <- readIORef scoreHeader
    (_, link) <- readIORef linkHeader
    digest <-
      directWorker
        nodeCount
        0
        0
        0
        next
        weight
        mark
        payload
        score
        link
    frozenMarks <- U.unsafeFreeze mark
    frozenScores <- U.unsafeFreeze score
    NonLinear.pure
      MultiStoreOutput
        { outputDigest = digestVectors digest frozenMarks frozenScores
        , outputMarks = frozenMarks
        , outputScores = frozenScores
        }

directHeaderMatchedRoot :: MultiStoreInput -> MultiStoreOutput
{-# NOINLINE directHeaderMatchedRoot #-}
directHeaderMatchedRoot = directHeaderMatchedRootWithVisits nodeCount

directHeaderMatchedRootWithVisits ::
  Int ->
  MultiStoreInput ->
  MultiStoreOutput
{-# NOINLINE directHeaderMatchedRootWithVisits #-}
directHeaderMatchedRootWithVisits visits input =
  validateVisitCount visits `NonLinear.seq`
    validateInput input `NonLinear.seq` unsafePerformIO do
      next <- U.thaw (inputNext input)
      weight <- U.thaw (inputWeight input)
      mark <- U.thaw (inputMark input)
      payloadBuffer <- V.thaw (inputPayload input)
      scoreBuffer <- U.thaw (inputScore input)
      linkBuffer <- U.thaw (inputLink input)
      payloadHeader <- newIORef (nodeCount, payloadBuffer)
      scoreHeader <- newIORef (nodeCount, scoreBuffer)
      linkHeader <- newIORef (nodeCount, linkBuffer)
      payload <- readHeaderOpaque payloadHeader
      score <- readHeaderOpaque scoreHeader
      link <- readHeaderOpaque linkHeader
      digest <-
        directWorker
          visits
          0
          0
          0
          next
          weight
          mark
          payload
          score
          link
      frozenMarks <- U.unsafeFreeze mark
      frozenScores <- U.unsafeFreeze score
      NonLinear.pure
        MultiStoreOutput
          { outputDigest = digestVectors digest frozenMarks frozenScores
          , outputMarks = frozenMarks
          , outputScores = frozenScores
          }

readHeaderOpaque :: IORef (Int, vector) -> NonLinear.IO vector
{-# NOINLINE readHeaderOpaque #-}
readHeaderOpaque header = do
  (_, vector) <- readIORef header
  NonLinear.pure vector

validateVisitCount :: Int -> ()
validateVisitCount visits
  | visits >= 0 && visits <= 4 * nodeCount = ()
  | otherwise =
      NonLinear.error "multi-store visit count must be between 0 and 16384"

data DirectTrace = DirectTrace
  { directVisitedIndicesRev :: ![Int]
  , directEventsRev :: ![TraceEvent]
  , directEventDigest :: {-# UNPACK #-} !Int64
  , directElementReads :: {-# UNPACK #-} !Int
  , directElementWrites :: {-# UNPACK #-} !Int
  , directReadDigest :: {-# UNPACK #-} !Int64
  }

emptyDirectTrace :: DirectTrace
emptyDirectTrace =
  DirectTrace
    { directVisitedIndicesRev = []
    , directEventsRev = []
    , directEventDigest = 1469598103934665603
    , directElementReads = 0
    , directElementWrites = 0
    , directReadDigest = 0
    }

directEvidenceRoot :: MultiStoreInput -> MultiStoreEvidence
{-# NOINLINE directEvidenceRoot #-}
directEvidenceRoot input =
  let !validationReads = validateInput input
   in unsafePerformIO do
        next <- U.thaw (inputNext input)
        weight <- U.thaw (inputWeight input)
        mark <- U.thaw (inputMark input)
        payloadBuffer <- V.thaw (inputPayload input)
        scoreBuffer <- U.thaw (inputScore input)
        linkBuffer <- U.thaw (inputLink input)
        payloadHeader <- newIORef (nodeCount, payloadBuffer)
        scoreHeader <- newIORef (nodeCount, scoreBuffer)
        linkHeader <- newIORef (nodeCount, linkBuffer)
        (_, payload) <- readIORef payloadHeader
        (_, score) <- readIORef scoreHeader
        (_, link) <- readIORef linkHeader
        trace <-
          directTraceWorker
            nodeCount
            0
            0
            emptyDirectTrace
            next
            weight
            mark
            payload
            score
            link
        frozenMarks <- U.unsafeFreeze mark
        frozenScores <- U.unsafeFreeze score
        let !output =
              MultiStoreOutput
                { outputDigest =
                    digestVectors
                      (directReadDigest trace)
                      frozenMarks
                      frozenScores
                , outputMarks = frozenMarks
                , outputScores = frozenScores
                }
        NonLinear.pure
          MultiStoreEvidence
            { evidenceVisitedIndices =
                U.fromListN
                  nodeCount
                  (NonLinear.reverse (directVisitedIndicesRev trace))
            , evidenceEvents =
                V.fromListN
                  (directElementReads trace + directElementWrites trace)
                  (NonLinear.reverse (directEventsRev trace))
            , evidenceEventDigest = directEventDigest trace
            , evidenceElementReads = directElementReads trace
            , evidenceElementWrites = directElementWrites trace
            , evidenceHeaderReads = 3
            , evidenceValidationReads = validationReads
            , evidenceOutput = output
            }

directTraceWorker ::
  Int ->
  Int ->
  Int ->
  DirectTrace ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  MV.IOVector (Int, Int) ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  NonLinear.IO DirectTrace
directTraceWorker !remaining !index !visits !trace next weight mark payload score link
  | remaining <= 0 = NonLinear.pure trace
  | otherwise = do
      nextIndex <- UM.unsafeRead next index
      weightValue <- UM.unsafeRead weight index
      markValue <- UM.unsafeRead mark index
      (payloadTag, payloadDelta) <- MV.unsafeRead payload index
      scoreValue <- UM.unsafeRead score index
      linkValue <- UM.unsafeRead link index
      let !shouldWrite =
            (weightValue + scoreValue + payloadTag + visits)
              `NonLinear.rem` 5
                == 0
          !nextTrace =
            recordTraceVisit
              index
              nextIndex
              weightValue
              markValue
              payloadTag
              payloadDelta
              scoreValue
              linkValue
              shouldWrite
              trace
      if shouldWrite
        then do
          UM.unsafeWrite mark index (markValue + 1)
          UM.unsafeWrite score index (scoreValue + payloadDelta + 1)
        else NonLinear.pure ()
      directTraceWorker
        (remaining - 1)
        ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
        (visits + 1)
        nextTrace
        next
        weight
        mark
        payload
        score
        link

directWorker ::
  Int ->
  Int ->
  Int ->
  Int64 ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  MV.IOVector (Int, Int) ->
  UM.IOVector Int ->
  UM.IOVector Int ->
  NonLinear.IO Int64
{-# NOINLINE directWorker #-}
directWorker !remaining !index !visits !digest next weight mark payload score link
  | remaining <= 0 = NonLinear.pure digest
  | otherwise = do
      nextIndex <- UM.unsafeRead next index
      weightValue <- UM.unsafeRead weight index
      markValue <- UM.unsafeRead mark index
      (payloadTag, payloadDelta) <- MV.unsafeRead payload index
      scoreValue <- UM.unsafeRead score index
      linkValue <- UM.unsafeRead link index
      let !shouldWrite =
            (weightValue + scoreValue + payloadTag + visits)
              `NonLinear.rem` 5
                == 0
          !nextDigest =
            digest
              + NonLinear.fromIntegral
                ( nextIndex
                    + weightValue
                    + markValue
                    + payloadTag
                    + payloadDelta
                    + scoreValue
                    + linkValue
                )
      if shouldWrite
        then do
          UM.unsafeWrite mark index (markValue + 1)
          UM.unsafeWrite score index (scoreValue + payloadDelta + 1)
        else NonLinear.pure ()
      directWorker
        (remaining - 1)
        ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
        (visits + 1)
        nextDigest
        next
        weight
        mark
        payload
        score
        link

pureBorrowDirectRoot :: MultiStoreInput -> MultiStoreOutput
{-# NOINLINE pureBorrowDirectRoot #-}
pureBorrowDirectRoot input =
  validateInput input `NonLinear.seq`
    unur
      ( linearly \linear -> DataFlow.do
          (allocationLinear, borrowLinear) <- dup linear
          store <- newMultiStore input allocationLinear
          runBO borrowLinear Control.do
            (storeBorrow, lender) <- borrowM store
            (Ur digest, storeBorrow) <-
              reborrowing storeBorrow \local -> Control.do
                let %1 !(fixedRoots, growableRoots) =
                      local .@ (fixedRootsField, growableRootsField)
                let %1 !(next, weight, mark) =
                      fixedRoots .@ (nextField, weightField, markField)
                let %1 !(payload, score, link) =
                      growableRoots .@ (payloadField, scoreField, linkField)
                let %1 !payloadContent = BoxedGrow.getContents payload
                let %1 !scoreContent = Grow.getContents score
                let %1 !linkContent = Grow.getContents link
                ( Ur digest
                  , next
                  , weight
                  , mark
                  , payloadContent
                  , scoreContent
                  , linkContent
                  ) <-
                  pureBorrowWorker
                    nodeCount
                    0
                    0
                    0
                    next
                    weight
                    mark
                    payloadContent
                    scoreContent
                    linkContent
                let !(Ur _) = share next
                let !(Ur _) = share weight
                let !(Ur _) = share mark
                let !(Ur _) = share payloadContent
                let !(Ur _) = share scoreContent
                let !(Ur _) = share linkContent
                Control.pure (Ur digest)
            let !(Ur _) = share storeBorrow
            pureAfter (finishMultiStore digest (reclaim lender))
      )

pureBorrowNestedRoot :: MultiStoreInput -> MultiStoreOutput
{-# NOINLINE pureBorrowNestedRoot #-}
pureBorrowNestedRoot input =
  validateInput input `NonLinear.seq`
    unur
      ( linearly \linear -> DataFlow.do
          (allocationLinear, borrowLinear) <- dup linear
          store <- newMultiStore input allocationLinear
          runBO borrowLinear Control.do
            (storeBorrow, lender) <- borrowM store
            (Ur digest, storeBorrow) <-
              reborrowing storeBorrow \local -> Control.do
                let %1 !(fixedRoots, growableRoots) =
                      local .@ (fixedRootsField, growableRootsField)
                let %1 !(next, weight, mark) =
                      fixedRoots .@ (nextField, weightField, markField)
                let %1 !(payload, score, link) =
                      growableRoots .@ (payloadField, scoreField, linkField)
                (Ur digest, fields) <-
                  reborrowings
                    ( next
                        :- weight
                        :- mark
                        :- payload
                        :- score
                        :- link
                        :- BNil
                    )
                    \case
                      next
                        :- weight
                        :- mark
                        :- payload
                        :- score
                        :- link
                        :- BNil -> Control.do
                          let %1 !payloadContent =
                                BoxedGrow.getContents payload
                          let %1 !scoreContent = Grow.getContents score
                          let %1 !linkContent = Grow.getContents link
                          ( Ur digest
                            , next
                            , weight
                            , mark
                            , payloadContent
                            , scoreContent
                            , linkContent
                            ) <-
                            pureBorrowWorker
                              nodeCount
                              0
                              0
                              0
                              next
                              weight
                              mark
                              payloadContent
                              scoreContent
                              linkContent
                          let !(Ur _) = share next
                          let !(Ur _) = share weight
                          let !(Ur _) = share mark
                          let !(Ur _) = share payloadContent
                          let !(Ur _) = share scoreContent
                          let !(Ur _) = share linkContent
                          Control.pure (Ur digest)
                let !() = consume fields
                Control.pure (Ur digest)
            let !(Ur _) = share storeBorrow
            pureAfter (finishMultiStore digest (reclaim lender))
      )

pureBorrowMixedDirectRoot :: MultiStoreInput -> MultiStoreOutput
{-# NOINLINE pureBorrowMixedDirectRoot #-}
pureBorrowMixedDirectRoot = pureBorrowUnrestrictedDirectRootWithVisits nodeCount

pureBorrowUnrestrictedDirectRootWithVisits ::
  Int ->
  MultiStoreInput ->
  MultiStoreOutput
{-# NOINLINE pureBorrowUnrestrictedDirectRootWithVisits #-}
pureBorrowUnrestrictedDirectRootWithVisits visits input =
  validateVisitCount visits `NonLinear.seq`
    validateInput input `NonLinear.seq`
      unur
        ( linearly \linear -> DataFlow.do
            (allocationLinear, borrowLinear) <- dup linear
            store <- newMixedStore input allocationLinear
            runBO borrowLinear Control.do
              (storeBorrow, lender) <- borrowM store
              (Ur digest, storeBorrow) <-
                reborrowing storeBorrow \local -> Control.do
                  let %1 !(fixedRoots, growableRoots) =
                        local
                          .@ (mixedFixedRootsField, mixedGrowableRootsField)
                  let %1 !(next, weight, mark) =
                        fixedRoots
                          .@ (mixedNextField, mixedWeightField, mixedMarkField)
                  let %1 !(payload, score, link) =
                        growableRoots
                          .@ (mixedPayloadField, mixedScoreField, mixedLinkField)
                  let %1 !payloadContent =
                        UnrestrictedGrow.getContents payload
                  let %1 !scoreContent = UnrestrictedGrow.getContents score
                  let %1 !linkContent = UnrestrictedGrow.getContents link
                  ( Ur digest
                    , next
                    , weight
                    , mark
                    , payloadContent
                    , scoreContent
                    , linkContent
                    ) <-
                    pureBorrowMixedWorker
                      visits
                      0
                      0
                      0
                      next
                      weight
                      mark
                      payloadContent
                      scoreContent
                      linkContent
                  let !(Ur _) = share next
                  let !(Ur _) = share weight
                  let !(Ur _) = share mark
                  let !(Ur _) = share payloadContent
                  let !(Ur _) = share scoreContent
                  let !(Ur _) = share linkContent
                  Control.pure (Ur digest)
              let !(Ur _) = share storeBorrow
              pureAfter (finishMixedStore digest (reclaim lender))
        )

pureBorrowMixedNestedRoot :: MultiStoreInput -> MultiStoreOutput
{-# NOINLINE pureBorrowMixedNestedRoot #-}
pureBorrowMixedNestedRoot =
  pureBorrowUnrestrictedNestedRootWithVisits nodeCount

pureBorrowUnrestrictedNestedRootWithVisits ::
  Int ->
  MultiStoreInput ->
  MultiStoreOutput
{-# NOINLINE pureBorrowUnrestrictedNestedRootWithVisits #-}
pureBorrowUnrestrictedNestedRootWithVisits visits input =
  validateVisitCount visits `NonLinear.seq`
    validateInput input `NonLinear.seq`
      unur
        ( linearly \linear -> DataFlow.do
            (allocationLinear, borrowLinear) <- dup linear
            store <- newMixedStore input allocationLinear
            runBO borrowLinear Control.do
              (storeBorrow, lender) <- borrowM store
              (Ur digest, storeBorrow) <-
                reborrowing storeBorrow \local -> Control.do
                  let %1 !(fixedRoots, growableRoots) =
                        local
                          .@ (mixedFixedRootsField, mixedGrowableRootsField)
                  let %1 !(next, weight, mark) =
                        fixedRoots
                          .@ (mixedNextField, mixedWeightField, mixedMarkField)
                  let %1 !(payload, score, link) =
                        growableRoots
                          .@ (mixedPayloadField, mixedScoreField, mixedLinkField)
                  (Ur digest, fields) <-
                    reborrowings
                      ( next
                          :- weight
                          :- mark
                          :- payload
                          :- score
                          :- link
                          :- BNil
                      )
                      \case
                        next
                          :- weight
                          :- mark
                          :- payload
                          :- score
                          :- link
                          :- BNil -> Control.do
                            let %1 !payloadContent =
                                  UnrestrictedGrow.getContents payload
                            let %1 !scoreContent =
                                  UnrestrictedGrow.getContents score
                            let %1 !linkContent =
                                  UnrestrictedGrow.getContents link
                            ( Ur digest
                              , next
                              , weight
                              , mark
                              , payloadContent
                              , scoreContent
                              , linkContent
                              ) <-
                              pureBorrowMixedWorker
                                visits
                                0
                                0
                                0
                                next
                                weight
                                mark
                                payloadContent
                                scoreContent
                                linkContent
                            let !(Ur _) = share next
                            let !(Ur _) = share weight
                            let !(Ur _) = share mark
                            let !(Ur _) = share payloadContent
                            let !(Ur _) = share scoreContent
                            let !(Ur _) = share linkContent
                            Control.pure (Ur digest)
                  let !() = consume fields
                  Control.pure (Ur digest)
              let !(Ur _) = share storeBorrow
              pureAfter (finishMixedStore digest (reclaim lender))
        )

pureBorrowDirectEvidenceRoot :: MultiStoreInput -> MultiStoreEvidence
{-# NOINLINE pureBorrowDirectEvidenceRoot #-}
pureBorrowDirectEvidenceRoot input =
  let !validationReads = validateInput input
   in unur
        ( linearly \linear -> DataFlow.do
            (allocationLinear, borrowLinear) <- dup linear
            store <- newMultiStore input allocationLinear
            runBO borrowLinear Control.do
              (storeBorrow, lender) <- borrowM store
              (Ur trace, storeBorrow) <-
                reborrowing storeBorrow \local -> Control.do
                  let %1 !(fixedRoots, growableRoots) =
                        local .@ (fixedRootsField, growableRootsField)
                  let %1 !(next, weight, mark) =
                        fixedRoots .@ (nextField, weightField, markField)
                  let %1 !(payload, score, link) =
                        growableRoots .@ (payloadField, scoreField, linkField)
                  let %1 !payloadContent = BoxedGrow.getContents payload
                  let %1 !scoreContent = Grow.getContents score
                  let %1 !linkContent = Grow.getContents link
                  ( Ur trace
                    , next
                    , weight
                    , mark
                    , payloadContent
                    , scoreContent
                    , linkContent
                    ) <-
                    pureBorrowTraceWorker
                      nodeCount
                      0
                      0
                      emptyDirectTrace
                      next
                      weight
                      mark
                      payloadContent
                      scoreContent
                      linkContent
                  let !(Ur _) = share next
                  let !(Ur _) = share weight
                  let !(Ur _) = share mark
                  let !(Ur _) = share payloadContent
                  let !(Ur _) = share scoreContent
                  let !(Ur _) = share linkContent
                  Control.pure (Ur trace)
              let !(Ur _) = share storeBorrow
              pureAfter
                ( finishMultiStoreEvidence
                    validationReads
                    trace
                    (reclaim lender)
                )
        )

pureBorrowNestedEvidenceRoot :: MultiStoreInput -> MultiStoreEvidence
{-# NOINLINE pureBorrowNestedEvidenceRoot #-}
pureBorrowNestedEvidenceRoot input =
  let !validationReads = validateInput input
   in unur
        ( linearly \linear -> DataFlow.do
            (allocationLinear, borrowLinear) <- dup linear
            store <- newMultiStore input allocationLinear
            runBO borrowLinear Control.do
              (storeBorrow, lender) <- borrowM store
              (Ur trace, storeBorrow) <-
                reborrowing storeBorrow \local -> Control.do
                  let %1 !(fixedRoots, growableRoots) =
                        local .@ (fixedRootsField, growableRootsField)
                  let %1 !(next, weight, mark) =
                        fixedRoots .@ (nextField, weightField, markField)
                  let %1 !(payload, score, link) =
                        growableRoots .@ (payloadField, scoreField, linkField)
                  (Ur trace, fields) <-
                    reborrowings
                      ( next
                          :- weight
                          :- mark
                          :- payload
                          :- score
                          :- link
                          :- BNil
                      )
                      \case
                        next
                          :- weight
                          :- mark
                          :- payload
                          :- score
                          :- link
                          :- BNil -> Control.do
                            let %1 !payloadContent =
                                  BoxedGrow.getContents payload
                            let %1 !scoreContent = Grow.getContents score
                            let %1 !linkContent = Grow.getContents link
                            ( Ur trace
                              , next
                              , weight
                              , mark
                              , payloadContent
                              , scoreContent
                              , linkContent
                              ) <-
                              pureBorrowTraceWorker
                                nodeCount
                                0
                                0
                                emptyDirectTrace
                                next
                                weight
                                mark
                                payloadContent
                                scoreContent
                                linkContent
                            let !(Ur _) = share next
                            let !(Ur _) = share weight
                            let !(Ur _) = share mark
                            let !(Ur _) = share payloadContent
                            let !(Ur _) = share scoreContent
                            let !(Ur _) = share linkContent
                            Control.pure (Ur trace)
                  let !() = consume fields
                  Control.pure (Ur trace)
              let !(Ur _) = share storeBorrow
              pureAfter
                ( finishMultiStoreEvidence
                    validationReads
                    trace
                    (reclaim lender)
                )
        )

pureBorrowMixedDirectEvidenceRoot :: MultiStoreInput -> MultiStoreEvidence
{-# NOINLINE pureBorrowMixedDirectEvidenceRoot #-}
pureBorrowMixedDirectEvidenceRoot input =
  let !validationReads = validateInput input
   in unur
        ( linearly \linear -> DataFlow.do
            (allocationLinear, borrowLinear) <- dup linear
            store <- newMixedStore input allocationLinear
            runBO borrowLinear Control.do
              (storeBorrow, lender) <- borrowM store
              (Ur trace, storeBorrow) <-
                reborrowing storeBorrow \local -> Control.do
                  let %1 !(fixedRoots, growableRoots) =
                        local
                          .@ (mixedFixedRootsField, mixedGrowableRootsField)
                  let %1 !(next, weight, mark) =
                        fixedRoots
                          .@ (mixedNextField, mixedWeightField, mixedMarkField)
                  let %1 !(payload, score, link) =
                        growableRoots
                          .@ (mixedPayloadField, mixedScoreField, mixedLinkField)
                  let %1 !payloadContent =
                        UnrestrictedGrow.getContents payload
                  let %1 !scoreContent = UnrestrictedGrow.getContents score
                  let %1 !linkContent = UnrestrictedGrow.getContents link
                  ( Ur trace
                    , next
                    , weight
                    , mark
                    , payloadContent
                    , scoreContent
                    , linkContent
                    ) <-
                    pureBorrowMixedTraceWorker
                      nodeCount
                      0
                      0
                      emptyDirectTrace
                      next
                      weight
                      mark
                      payloadContent
                      scoreContent
                      linkContent
                  let !(Ur _) = share next
                  let !(Ur _) = share weight
                  let !(Ur _) = share mark
                  let !(Ur _) = share payloadContent
                  let !(Ur _) = share scoreContent
                  let !(Ur _) = share linkContent
                  Control.pure (Ur trace)
              let !(Ur _) = share storeBorrow
              pureAfter
                ( finishMixedStoreEvidence
                    validationReads
                    trace
                    (reclaim lender)
                )
        )

pureBorrowMixedNestedEvidenceRoot :: MultiStoreInput -> MultiStoreEvidence
{-# NOINLINE pureBorrowMixedNestedEvidenceRoot #-}
pureBorrowMixedNestedEvidenceRoot input =
  let !validationReads = validateInput input
   in unur
        ( linearly \linear -> DataFlow.do
            (allocationLinear, borrowLinear) <- dup linear
            store <- newMixedStore input allocationLinear
            runBO borrowLinear Control.do
              (storeBorrow, lender) <- borrowM store
              (Ur trace, storeBorrow) <-
                reborrowing storeBorrow \local -> Control.do
                  let %1 !(fixedRoots, growableRoots) =
                        local
                          .@ (mixedFixedRootsField, mixedGrowableRootsField)
                  let %1 !(next, weight, mark) =
                        fixedRoots
                          .@ (mixedNextField, mixedWeightField, mixedMarkField)
                  let %1 !(payload, score, link) =
                        growableRoots
                          .@ (mixedPayloadField, mixedScoreField, mixedLinkField)
                  (Ur trace, fields) <-
                    reborrowings
                      ( next
                          :- weight
                          :- mark
                          :- payload
                          :- score
                          :- link
                          :- BNil
                      )
                      \case
                        next
                          :- weight
                          :- mark
                          :- payload
                          :- score
                          :- link
                          :- BNil -> Control.do
                            let %1 !payloadContent =
                                  UnrestrictedGrow.getContents payload
                            let %1 !scoreContent =
                                  UnrestrictedGrow.getContents score
                            let %1 !linkContent =
                                  UnrestrictedGrow.getContents link
                            ( Ur trace
                              , next
                              , weight
                              , mark
                              , payloadContent
                              , scoreContent
                              , linkContent
                              ) <-
                              pureBorrowMixedTraceWorker
                                nodeCount
                                0
                                0
                                emptyDirectTrace
                                next
                                weight
                                mark
                                payloadContent
                                scoreContent
                                linkContent
                            let !(Ur _) = share next
                            let !(Ur _) = share weight
                            let !(Ur _) = share mark
                            let !(Ur _) = share payloadContent
                            let !(Ur _) = share scoreContent
                            let !(Ur _) = share linkContent
                            Control.pure (Ur trace)
                  let !() = consume fields
                  Control.pure (Ur trace)
              let !(Ur _) = share storeBorrow
              pureAfter
                ( finishMixedStoreEvidence
                    validationReads
                    trace
                    (reclaim lender)
                )
        )

pureBorrowUnrestrictedDirectRoot :: MultiStoreInput -> MultiStoreOutput
{-# NOINLINE pureBorrowUnrestrictedDirectRoot #-}
pureBorrowUnrestrictedDirectRoot = pureBorrowMixedDirectRoot

pureBorrowUnrestrictedNestedRoot :: MultiStoreInput -> MultiStoreOutput
{-# NOINLINE pureBorrowUnrestrictedNestedRoot #-}
pureBorrowUnrestrictedNestedRoot = pureBorrowMixedNestedRoot

pureBorrowUnrestrictedDirectEvidenceRoot ::
  MultiStoreInput ->
  MultiStoreEvidence
{-# NOINLINE pureBorrowUnrestrictedDirectEvidenceRoot #-}
pureBorrowUnrestrictedDirectEvidenceRoot =
  pureBorrowMixedDirectEvidenceRoot

pureBorrowUnrestrictedNestedEvidenceRoot ::
  MultiStoreInput ->
  MultiStoreEvidence
{-# NOINLINE pureBorrowUnrestrictedNestedEvidenceRoot #-}
pureBorrowUnrestrictedNestedEvidenceRoot =
  pureBorrowMixedNestedEvidenceRoot

pureBorrowWorker ::
  Int ->
  Int ->
  Int ->
  Int64 ->
  Mut α (Fixed.Vector Int) %1 ->
  Mut α (Fixed.Vector Int) %1 ->
  Mut α (Fixed.Vector Int) %1 ->
  Mut α (BoxedFixed.Vector (Int, Int)) %1 ->
  Mut α (Fixed.Vector Int) %1 ->
  Mut α (Fixed.Vector Int) %1 ->
  BO
    α
    ( Ur Int64
    , Mut α (Fixed.Vector Int)
    , Mut α (Fixed.Vector Int)
    , Mut α (Fixed.Vector Int)
    , Mut α (BoxedFixed.Vector (Int, Int))
    , Mut α (Fixed.Vector Int)
    , Mut α (Fixed.Vector Int)
    )
{-# NOINLINE pureBorrowWorker #-}
pureBorrowWorker !remaining !index !visits !digest next weight mark payload score link
  | remaining <= 0 =
      Control.pure
        (Ur digest, next, weight, mark, payload, score, link)
  | otherwise = Control.do
      (Ur nextIndex, next) <- Fixed.copyAtMut index next
      (Ur weightValue, weight) <- Fixed.copyAtMut index weight
      (Ur markValue, mark) <- Fixed.copyAtMut index mark
      (Ur (payloadTag, payloadDelta), payload) <-
        BoxedFixed.copyAtMut index payload
      (Ur scoreValue, score) <- Fixed.copyAtMut index score
      (Ur linkValue, link) <- Fixed.copyAtMut index link
      let !shouldWrite =
            (weightValue + scoreValue + payloadTag + visits)
              `NonLinear.rem` 5
                == 0
          !nextDigest =
            digest
              + NonLinear.fromIntegral
                ( nextIndex
                    + weightValue
                    + markValue
                    + payloadTag
                    + payloadDelta
                    + scoreValue
                    + linkValue
                )
      if shouldWrite
        then Control.do
          (oldMark, mark) <- Fixed.unsafeSet index (markValue + 1) mark
          (oldScore, score) <-
            Fixed.unsafeSet index (scoreValue + payloadDelta + 1) score
          pureBorrowWorker
            (remaining - 1)
            ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
            (visits + 1)
            nextDigest
            next
            weight
            (consume oldMark `lseq` mark)
            payload
            (consume oldScore `lseq` score)
            link
        else
          pureBorrowWorker
            (remaining - 1)
            ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
            (visits + 1)
            nextDigest
            next
            weight
            mark
            payload
            score
            link

pureBorrowTraceWorker ::
  Int ->
  Int ->
  Int ->
  DirectTrace ->
  Mut α (Fixed.Vector Int) %1 ->
  Mut α (Fixed.Vector Int) %1 ->
  Mut α (Fixed.Vector Int) %1 ->
  Mut α (BoxedFixed.Vector (Int, Int)) %1 ->
  Mut α (Fixed.Vector Int) %1 ->
  Mut α (Fixed.Vector Int) %1 ->
  BO
    α
    ( Ur DirectTrace
    , Mut α (Fixed.Vector Int)
    , Mut α (Fixed.Vector Int)
    , Mut α (Fixed.Vector Int)
    , Mut α (BoxedFixed.Vector (Int, Int))
    , Mut α (Fixed.Vector Int)
    , Mut α (Fixed.Vector Int)
    )
{-# NOINLINE pureBorrowTraceWorker #-}
pureBorrowTraceWorker !remaining !index !visits !trace next weight mark payload score link
  | remaining <= 0 =
      Control.pure
        (Ur trace, next, weight, mark, payload, score, link)
  | otherwise = Control.do
      (Ur nextIndex, next) <- Fixed.copyAtMut index next
      (Ur weightValue, weight) <- Fixed.copyAtMut index weight
      (Ur markValue, mark) <- Fixed.copyAtMut index mark
      (Ur (payloadTag, payloadDelta), payload) <-
        BoxedFixed.copyAtMut index payload
      (Ur scoreValue, score) <- Fixed.copyAtMut index score
      (Ur linkValue, link) <- Fixed.copyAtMut index link
      let !shouldWrite =
            (weightValue + scoreValue + payloadTag + visits)
              `NonLinear.rem` 5
                == 0
          !nextTrace =
            recordTraceVisit
              index
              nextIndex
              weightValue
              markValue
              payloadTag
              payloadDelta
              scoreValue
              linkValue
              shouldWrite
              trace
      if shouldWrite
        then Control.do
          (oldMark, mark) <- Fixed.unsafeSet index (markValue + 1) mark
          (oldScore, score) <-
            Fixed.unsafeSet index (scoreValue + payloadDelta + 1) score
          pureBorrowTraceWorker
            (remaining - 1)
            ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
            (visits + 1)
            nextTrace
            next
            weight
            (consume oldMark `lseq` mark)
            payload
            (consume oldScore `lseq` score)
            link
        else
          pureBorrowTraceWorker
            (remaining - 1)
            ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
            (visits + 1)
            nextTrace
            next
            weight
            mark
            payload
            score
            link

pureBorrowMixedWorker ::
  Int ->
  Int ->
  Int ->
  Int64 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  Mut α (Unrestricted.Vector V.Vector (Int, Int)) %1 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  BO
    α
    ( Ur Int64
    , Mut α (Unrestricted.Vector U.Vector Int)
    , Mut α (Unrestricted.Vector U.Vector Int)
    , Mut α (Unrestricted.Vector U.Vector Int)
    , Mut α (Unrestricted.Vector V.Vector (Int, Int))
    , Mut α (Unrestricted.Vector U.Vector Int)
    , Mut α (Unrestricted.Vector U.Vector Int)
    )
{-# INLINEABLE pureBorrowMixedWorker #-}
pureBorrowMixedWorker !remaining !index !visits !digest next weight mark payload score link =
  case digest of
    I64# digest# ->
      go
        remaining
        index
        visits
        digest#
        next
        weight
        mark
        payload
        score
        link
  where
    go ::
      Int ->
      Int ->
      Int ->
      GHC.Int64# ->
      Mut α (Unrestricted.Vector U.Vector Int) %1 ->
      Mut α (Unrestricted.Vector U.Vector Int) %1 ->
      Mut α (Unrestricted.Vector U.Vector Int) %1 ->
      Mut α (Unrestricted.Vector V.Vector (Int, Int)) %1 ->
      Mut α (Unrestricted.Vector U.Vector Int) %1 ->
      Mut α (Unrestricted.Vector U.Vector Int) %1 ->
      BO
        α
        ( Ur Int64
        , Mut α (Unrestricted.Vector U.Vector Int)
        , Mut α (Unrestricted.Vector U.Vector Int)
        , Mut α (Unrestricted.Vector U.Vector Int)
        , Mut α (Unrestricted.Vector V.Vector (Int, Int))
        , Mut α (Unrestricted.Vector U.Vector Int)
        , Mut α (Unrestricted.Vector U.Vector Int)
        )
    go !remaining !index !visits digest# next weight mark payload score link
      | remaining <= 0 =
          Control.pure
            ( Ur (I64# digest#)
            , next
            , weight
            , mark
            , payload
            , score
            , link
            )
      | otherwise = Control.do
          (Ur nextIndex, next) <- Unrestricted.unsafeGet index next
          (Ur weightValue, weight) <- Unrestricted.unsafeGet index weight
          (Ur markValue, mark) <- Unrestricted.unsafeGet index mark
          (Ur (payloadTag, payloadDelta), payload) <-
            Unrestricted.unsafeGet index payload
          (Ur scoreValue, score) <- Unrestricted.unsafeGet index score
          (Ur linkValue, link) <- Unrestricted.unsafeGet index link
          let !shouldWrite =
                (weightValue + scoreValue + payloadTag + visits)
                  `NonLinear.rem` 5
                    == 0
              !nextDigest =
                I64# digest#
                  + NonLinear.fromIntegral
                    ( nextIndex
                        + weightValue
                        + markValue
                        + payloadTag
                        + payloadDelta
                        + scoreValue
                        + linkValue
                    )
          case nextDigest of
            I64# nextDigest# ->
              if shouldWrite
                then Control.do
                  mark <-
                    Unrestricted.unsafeWrite index (markValue + 1) mark
                  score <-
                    Unrestricted.unsafeWrite
                      index
                      (scoreValue + payloadDelta + 1)
                      score
                  go
                    (remaining - 1)
                    ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
                    (visits + 1)
                    nextDigest#
                    next
                    weight
                    mark
                    payload
                    score
                    link
                else
                  go
                    (remaining - 1)
                    ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
                    (visits + 1)
                    nextDigest#
                    next
                    weight
                    mark
                    payload
                    score
                    link

pureBorrowMixedTraceWorker ::
  Int ->
  Int ->
  Int ->
  DirectTrace ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  Mut α (Unrestricted.Vector V.Vector (Int, Int)) %1 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  Mut α (Unrestricted.Vector U.Vector Int) %1 ->
  BO
    α
    ( Ur DirectTrace
    , Mut α (Unrestricted.Vector U.Vector Int)
    , Mut α (Unrestricted.Vector U.Vector Int)
    , Mut α (Unrestricted.Vector U.Vector Int)
    , Mut α (Unrestricted.Vector V.Vector (Int, Int))
    , Mut α (Unrestricted.Vector U.Vector Int)
    , Mut α (Unrestricted.Vector U.Vector Int)
    )
{-# NOINLINE pureBorrowMixedTraceWorker #-}
pureBorrowMixedTraceWorker !remaining !index !visits !trace next weight mark payload score link
  | remaining <= 0 =
      Control.pure
        (Ur trace, next, weight, mark, payload, score, link)
  | otherwise = Control.do
      (Ur nextIndex, next) <- Unrestricted.unsafeGet index next
      (Ur weightValue, weight) <- Unrestricted.unsafeGet index weight
      (Ur markValue, mark) <- Unrestricted.unsafeGet index mark
      (Ur (payloadTag, payloadDelta), payload) <-
        Unrestricted.unsafeGet index payload
      (Ur scoreValue, score) <- Unrestricted.unsafeGet index score
      (Ur linkValue, link) <- Unrestricted.unsafeGet index link
      let !shouldWrite =
            (weightValue + scoreValue + payloadTag + visits)
              `NonLinear.rem` 5
                == 0
          !nextTrace =
            recordTraceVisit
              index
              nextIndex
              weightValue
              markValue
              payloadTag
              payloadDelta
              scoreValue
              linkValue
              shouldWrite
              trace
      if shouldWrite
        then Control.do
          mark <- Unrestricted.unsafeWrite index (markValue + 1) mark
          score <-
            Unrestricted.unsafeWrite
              index
              (scoreValue + payloadDelta + 1)
              score
          pureBorrowMixedTraceWorker
            (remaining - 1)
            ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
            (visits + 1)
            nextTrace
            next
            weight
            mark
            payload
            score
            link
        else
          pureBorrowMixedTraceWorker
            (remaining - 1)
            ((nextIndex + linkValue) `NonLinear.rem` nodeCount)
            (visits + 1)
            nextTrace
            next
            weight
            mark
            payload
            score
            link

newMultiStore :: MultiStoreInput -> Linearly %1 -> MultiStore
{-# NOINLINE newMultiStore #-}
newMultiStore =
  GHC.noinline \input linear ->
    dup linear & \(nextLinear, rest1) ->
      dup rest1 & \(weightLinear, rest2) ->
        dup rest2 & \(markLinear, rest3) ->
          dup rest3 & \(payloadLinear, rest4) ->
            dup rest4 & \(scoreLinear, linkLinear) ->
              MultiStore
                { fixedRoots =
                    FixedRoots
                      { next =
                          Fixed.fromVector (inputNext input) nextLinear
                      , weight =
                          Fixed.fromVector
                            (inputWeight input)
                            weightLinear
                      , mark =
                          Fixed.fromVector (inputMark input) markLinear
                      }
                , growableRoots =
                    GrowableRoots
                      { payload =
                          BoxedGrow.fromVector
                            (inputPayload input)
                            payloadLinear
                      , score =
                          Grow.fromVector (inputScore input) scoreLinear
                      , link =
                          Grow.fromVector (inputLink input) linkLinear
                      }
                }

newMixedStore :: MultiStoreInput -> Linearly %1 -> MixedStore
{-# NOINLINE newMixedStore #-}
newMixedStore =
  GHC.noinline \input linear ->
    dup linear & \(nextLinear, rest1) ->
      dup rest1 & \(weightLinear, rest2) ->
        dup rest2 & \(markLinear, rest3) ->
          dup rest3 & \(payloadLinear, rest4) ->
            dup rest4 & \(scoreLinear, linkLinear) ->
              MixedStore
                { mixedFixedRoots =
                    MixedFixedRoots
                      { mixedNext =
                          Unrestricted.fromVector
                            (inputNext input)
                            nextLinear
                      , mixedWeight =
                          Unrestricted.fromVector
                            (inputWeight input)
                            weightLinear
                      , mixedMark =
                          Unrestricted.fromVector
                            (inputMark input)
                            markLinear
                      }
                , mixedGrowableRoots =
                    MixedGrowableRoots
                      { mixedPayload =
                          UnrestrictedGrow.fromVector
                            (inputPayload input)
                            payloadLinear
                      , mixedScore =
                          UnrestrictedGrow.fromVector
                            (inputScore input)
                            scoreLinear
                      , mixedLink =
                          UnrestrictedGrow.fromVector
                            (inputLink input)
                            linkLinear
                      }
                }

finishMultiStore :: Int64 -> MultiStore %1 -> Ur MultiStoreOutput
{-# NOINLINE finishMultiStore #-}
finishMultiStore
  digest
  ( MultiStore
      (FixedRoots next weight mark)
      (GrowableRoots payload score link)
    ) =
    case Fixed.toVector next of
      Ur nextVector ->
        case Fixed.toVector weight of
          Ur weightVector ->
            case Fixed.toVector mark of
              Ur markVector ->
                case BoxedGrow.toVector payload of
                  Ur payloadVector ->
                    case Grow.toVector score of
                      Ur scoreVector ->
                        case Grow.toVector link of
                          Ur linkVector ->
                            U.length nextVector `lseq`
                              U.length weightVector `lseq`
                                V.length payloadVector `lseq`
                                  U.length linkVector `lseq`
                                    Ur
                                      MultiStoreOutput
                                        { outputDigest =
                                            digestVectors
                                              digest
                                              markVector
                                              scoreVector
                                        , outputMarks = markVector
                                        , outputScores = scoreVector
                                        }

finishMixedStore :: Int64 -> MixedStore %1 -> Ur MultiStoreOutput
{-# NOINLINE finishMixedStore #-}
finishMixedStore
  digest
  ( MixedStore
      (MixedFixedRoots next weight mark)
      (MixedGrowableRoots payload score link)
    ) =
    case Unrestricted.toVector next of
      Ur nextVector ->
        case Unrestricted.toVector weight of
          Ur weightVector ->
            case Unrestricted.toVector mark of
              Ur markVector ->
                case UnrestrictedGrow.toVector payload of
                  Ur payloadVector ->
                    case UnrestrictedGrow.toVector score of
                      Ur scoreVector ->
                        case UnrestrictedGrow.toVector link of
                          Ur linkVector ->
                            U.length nextVector `lseq`
                              U.length weightVector `lseq`
                                V.length payloadVector `lseq`
                                  U.length linkVector `lseq`
                                    Ur
                                      MultiStoreOutput
                                        { outputDigest =
                                            digestVectors
                                              digest
                                              markVector
                                              scoreVector
                                        , outputMarks = markVector
                                        , outputScores = scoreVector
                                        }

finishMultiStoreEvidence ::
  Int ->
  DirectTrace ->
  MultiStore %1 ->
  Ur MultiStoreEvidence
finishMultiStoreEvidence validationReads trace store =
  case finishMultiStore (directReadDigest trace) store of
    Ur output ->
      Ur (traceEvidence validationReads trace output)

finishMixedStoreEvidence ::
  Int ->
  DirectTrace ->
  MixedStore %1 ->
  Ur MultiStoreEvidence
finishMixedStoreEvidence validationReads trace store =
  case finishMixedStore (directReadDigest trace) store of
    Ur output ->
      Ur (traceEvidence validationReads trace output)

traceEvidence ::
  Int ->
  DirectTrace ->
  MultiStoreOutput ->
  MultiStoreEvidence
traceEvidence validationReads trace output =
  MultiStoreEvidence
    { evidenceVisitedIndices =
        U.fromListN
          nodeCount
          (NonLinear.reverse (directVisitedIndicesRev trace))
    , evidenceEvents =
        V.fromListN
          (directElementReads trace + directElementWrites trace)
          (NonLinear.reverse (directEventsRev trace))
    , evidenceEventDigest = directEventDigest trace
    , evidenceElementReads = directElementReads trace
    , evidenceElementWrites = directElementWrites trace
    , evidenceHeaderReads = 3
    , evidenceValidationReads = validationReads
    , evidenceOutput = output
    }

recordTraceVisit ::
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  Bool ->
  DirectTrace ->
  DirectTrace
recordTraceVisit index nextIndex weightValue markValue payloadTag payloadDelta scoreValue linkValue shouldWrite trace =
  let !readEvents =
        [ ReadIntEvent NextStore index nextIndex
        , ReadIntEvent WeightStore index weightValue
        , ReadIntEvent MarkStore index markValue
        , ReadPayloadEvent index payloadTag payloadDelta
        , ReadIntEvent ScoreStore index scoreValue
        , ReadIntEvent LinkStore index linkValue
        ]
      !writeEvents =
        if shouldWrite
          then
            [ WriteIntEvent MarkStore index (markValue + 1)
            , WriteIntEvent
                ScoreStore
                index
                (scoreValue + payloadDelta + 1)
            ]
          else []
      !events = readEvents <> writeEvents
   in DirectTrace
        { directVisitedIndicesRev =
            index : directVisitedIndicesRev trace
        , directEventsRev =
            List.foldl'
              (NonLinear.flip (:))
              (directEventsRev trace)
              events
        , directEventDigest =
            List.foldl' hashTraceEvent (directEventDigest trace) events
        , directElementReads = directElementReads trace + 6
        , directElementWrites =
            directElementWrites trace + if shouldWrite then 2 else 0
        , directReadDigest =
            directReadDigest trace
              + NonLinear.fromIntegral
                ( nextIndex
                    + weightValue
                    + markValue
                    + payloadTag
                    + payloadDelta
                    + scoreValue
                    + linkValue
                )
        }

hashTraceEvent :: Int64 -> TraceEvent -> Int64
hashTraceEvent digest event =
  List.foldl' hashTraceWord digest case event of
    ReadIntEvent store index value ->
      [1, traceStoreCode store, index, value]
    ReadPayloadEvent index tag delta ->
      [2, index, tag, delta]
    WriteIntEvent store index value ->
      [3, traceStoreCode store, index, value]

hashTraceWord :: Int64 -> Int -> Int64
hashTraceWord digest value =
  digest * 1099511628211 + NonLinear.fromIntegral value

traceStoreCode :: TraceStore -> Int
traceStoreCode = \case
  NextStore -> 1
  WeightStore -> 2
  MarkStore -> 3
  ScoreStore -> 4
  LinkStore -> 5

fixedRootsField ::
  RecordLabel MultiStore "fixedRoots" FixedRoots
fixedRootsField = #fixedRoots

growableRootsField ::
  RecordLabel MultiStore "growableRoots" GrowableRoots
growableRootsField = #growableRoots

nextField :: RecordLabel FixedRoots "next" (Fixed.Vector Int)
nextField = #next

weightField :: RecordLabel FixedRoots "weight" (Fixed.Vector Int)
weightField = #weight

markField :: RecordLabel FixedRoots "mark" (Fixed.Vector Int)
markField = #mark

mixedFixedRootsField ::
  RecordLabel MixedStore "mixedFixedRoots" MixedFixedRoots
mixedFixedRootsField = #mixedFixedRoots

mixedGrowableRootsField ::
  RecordLabel MixedStore "mixedGrowableRoots" MixedGrowableRoots
mixedGrowableRootsField = #mixedGrowableRoots

mixedNextField ::
  RecordLabel
    MixedFixedRoots
    "mixedNext"
    (Unrestricted.Vector U.Vector Int)
mixedNextField = #mixedNext

mixedWeightField ::
  RecordLabel
    MixedFixedRoots
    "mixedWeight"
    (Unrestricted.Vector U.Vector Int)
mixedWeightField = #mixedWeight

mixedMarkField ::
  RecordLabel
    MixedFixedRoots
    "mixedMark"
    (Unrestricted.Vector U.Vector Int)
mixedMarkField = #mixedMark

mixedPayloadField ::
  RecordLabel
    MixedGrowableRoots
    "mixedPayload"
    (UnrestrictedGrow.GrowableVector V.Vector (Int, Int))
mixedPayloadField = #mixedPayload

mixedScoreField ::
  RecordLabel
    MixedGrowableRoots
    "mixedScore"
    (UnrestrictedGrow.GrowableVector U.Vector Int)
mixedScoreField = #mixedScore

mixedLinkField ::
  RecordLabel
    MixedGrowableRoots
    "mixedLink"
    (UnrestrictedGrow.GrowableVector U.Vector Int)
mixedLinkField = #mixedLink

payloadField ::
  RecordLabel
    GrowableRoots
    "payload"
    (BoxedGrow.GrowableVector (Int, Int))
payloadField = #payload

scoreField ::
  RecordLabel GrowableRoots "score" (Grow.GrowableVector Int)
scoreField = #score

linkField ::
  RecordLabel GrowableRoots "link" (Grow.GrowableVector Int)
linkField = #link

digestVectors :: Int64 -> U.Vector Int -> U.Vector Int -> Int64
digestVectors initial marks scores =
  let !marksDigest =
        U.ifoldl'
          (\digest index value -> mixDigest digest (index * 17 + value))
          initial
          marks
   in U.ifoldl'
        (\digest index value -> mixDigest digest (index * 31 + value))
        marksDigest
        scores

outputVectorDigest :: U.Vector Int -> Int64
outputVectorDigest =
  U.ifoldl'
    (\digest index value -> mixDigest digest (index * 37 + value))
    1_469_598_103_934_665_603

mixDigest :: Int64 -> Int -> Int64
mixDigest digest value =
  digest * 1_099_511_628_211 + NonLinear.fromIntegral value
