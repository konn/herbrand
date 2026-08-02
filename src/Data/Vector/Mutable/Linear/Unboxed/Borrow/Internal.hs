{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Data.Vector.Mutable.Linear.Unboxed.Borrow.Internal (
  Vector,
  Pinned,
  PinnedBuffer (..),
  empty,
  fromVector,
  toVector,
  dispose,
  size,
  capacity,
  copyAt,
  unsafeCopyAt,
  copyAtMut,
  unsafeCopyAtMut,
  write,
  unsafeWrite,
  modify,
  unsafeModify,
  push,
  extend,
  withPinned,
  withPinnedBuffer,
  getContents,
  pinnedSize,
  pinnedCapacity,
  pinnedCopyAt,
  pinnedUnsafeCopyAt,
  pinnedWrite,
  pinnedUnsafeWrite,
  pinnedModify,
  pinnedUnsafeModify,
  pinnedBufferUnsafeCopyAt,
  pinnedBufferUnsafeWrite,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Vector.Generic.Mutable.Growable.Linear.Borrow.Unrestricted qualified as Growable
import Data.Vector.Generic.Mutable.Linear.Borrow.Unrestricted qualified as Fixed
import Data.Vector.Unboxed qualified as U
import GHC.Stack (HasCallStack)
import Prelude.Linear hiding (getContents)

type Vector = Growable.GrowableVector U.Vector

newtype Pinned α a = Pinned (Mut α (Fixed.Vector U.Vector a))

newtype PinnedBuffer α a = PinnedBuffer (Mut α (Fixed.Vector U.Vector a))

type role Pinned nominal nominal

type role PinnedBuffer nominal nominal

empty ::
  (U.Unbox a) =>
  Linearly %1 ->
  Vector a
empty = Growable.empty

fromVector ::
  (U.Unbox a) =>
  U.Vector a ->
  Linearly %1 ->
  Vector a
fromVector = Growable.fromVector

toVector ::
  (U.Unbox a) =>
  Vector a %1 ->
  Ur (U.Vector a)
toVector = Growable.toVector

dispose :: Vector a %1 -> ()
dispose = consume

size ::
  (α >= γ) =>
  Borrow bk α (Vector a) %1 ->
  BO γ (Ur Int)
size vector =
  case Growable.size vector of
    (result, vector) ->
      Control.pure (consume vector `lseq` result)

capacity ::
  (U.Unbox a) =>
  Borrow bk α (Vector a) %1 ->
  (Ur Int, Borrow bk α (Vector a))
capacity = Growable.capacity

copyAt ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  Int ->
  Share α (Vector a) ->
  BO γ (Ur a)
copyAt = Growable.copyAt

unsafeCopyAt ::
  (U.Unbox a, α >= γ) =>
  Int ->
  Share α (Vector a) ->
  BO γ (Ur a)
unsafeCopyAt = Growable.unsafeCopyAt

copyAtMut ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  Int ->
  Mut α (Vector a) %1 ->
  BO γ (Ur a, Mut α (Vector a))
copyAtMut = Growable.copyAtMut

unsafeCopyAtMut ::
  (U.Unbox a, α >= γ) =>
  Int ->
  Mut α (Vector a) %1 ->
  BO γ (Ur a, Mut α (Vector a))
unsafeCopyAtMut = Growable.unsafeCopyAtMut

write ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  Int ->
  a ->
  Mut α (Vector a) %1 ->
  BO γ (Mut α (Vector a))
write = Growable.write

unsafeWrite ::
  (U.Unbox a, α >= γ) =>
  Int ->
  a ->
  Mut α (Vector a) %1 ->
  BO γ (Mut α (Vector a))
unsafeWrite = Growable.unsafeWrite

modify ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  (a -> (a, result)) ->
  Int ->
  Mut α (Vector a) %1 ->
  BO γ (Ur result, Mut α (Vector a))
modify function index =
  Growable.update index \value ->
    case function value of
      (updatedValue, result) ->
        Control.pure (Ur result, Ur updatedValue)

unsafeModify ::
  (U.Unbox a, α >= γ) =>
  (a -> (a, result)) ->
  Int ->
  Mut α (Vector a) %1 ->
  BO γ (Ur result, Mut α (Vector a))
unsafeModify function index =
  Growable.unsafeUpdate index \value ->
    case function value of
      (updatedValue, result) ->
        Control.pure (Ur result, Ur updatedValue)

push ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  a ->
  Mut α (Vector a) %1 ->
  BO γ (Mut α (Vector a))
push = Growable.push

extend ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  U.Vector a ->
  Mut α (Vector a) %1 ->
  BO γ (Mut α (Vector a))
extend = Growable.extend

getContents ::
  (U.Unbox a) =>
  Borrow bk α (Vector a) %1 ->
  Borrow bk α (Fixed.Vector U.Vector a)
getContents = Growable.getContents

withPinned ::
  forall a α γ result.
  (U.Unbox a, α >= γ) =>
  ( forall β.
    Pinned (β /\ α) a %1 ->
    BO (β /\ γ) (result, Pinned (β /\ α) a)
  ) %1 ->
  Mut α (Vector a) %1 ->
  BO γ (result, Mut α (Vector a))
withPinned action vector = Control.do
  (result, vector) <-
    reborrowing vector \shortened -> Control.do
      let %1 !contents = Growable.getContents shortened
      (result, Pinned contents) <- action (Pinned contents)
      let !(Ur _) = share contents
      Control.pure result
  Control.pure (result, vector)

withPinnedBuffer ::
  forall a α γ result.
  (U.Unbox a, α >= γ) =>
  ( forall β.
    Int ->
    PinnedBuffer (β /\ α) a %1 ->
    BO (β /\ γ) (result, PinnedBuffer (β /\ α) a)
  ) %1 ->
  Mut α (Vector a) %1 ->
  BO γ (result, Mut α (Vector a))
withPinnedBuffer action vector = Control.do
  (result, vector) <-
    reborrowing vector \shortened -> Control.do
      Growable.getContents shortened & \contents ->
        case Fixed.size contents of
          (Ur length_, contents) -> Control.do
            (result, PinnedBuffer contents) <-
              action length_ (PinnedBuffer contents)
            let !(Ur _) = share contents
            Control.pure result
  Control.pure (result, vector)

pinnedSize ::
  (U.Unbox a) =>
  Pinned α a %1 ->
  (Ur Int, Pinned α a)
pinnedSize (Pinned vector) =
  case Fixed.size vector of
    (result, vector) -> (result, Pinned vector)

pinnedCapacity ::
  (U.Unbox a) =>
  Pinned α a %1 ->
  (Ur Int, Pinned α a)
pinnedCapacity = pinnedSize

pinnedCopyAt ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  Int ->
  Pinned α a %1 ->
  BO γ (Ur a, Pinned α a)
pinnedCopyAt index (Pinned vector) = Control.do
  (result, vector) <- Fixed.get index vector
  Control.pure (result, Pinned vector)

pinnedUnsafeCopyAt ::
  (U.Unbox a, α >= γ) =>
  Int ->
  Pinned α a %1 ->
  BO γ (Ur a, Pinned α a)
pinnedUnsafeCopyAt index (Pinned vector) = Control.do
  (result, vector) <- Fixed.unsafeGet index vector
  Control.pure (result, Pinned vector)

pinnedWrite ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  Int ->
  a ->
  Pinned α a %1 ->
  BO γ (Pinned α a)
pinnedWrite index value (Pinned vector) = Control.do
  vector <- Fixed.write index value vector
  Control.pure (Pinned vector)

pinnedUnsafeWrite ::
  (U.Unbox a, α >= γ) =>
  Int ->
  a ->
  Pinned α a %1 ->
  BO γ (Pinned α a)
pinnedUnsafeWrite index value (Pinned vector) = Control.do
  vector <- Fixed.unsafeWrite index value vector
  Control.pure (Pinned vector)

pinnedModify ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  (a -> (a, result)) ->
  Int ->
  Pinned α a %1 ->
  BO γ (Ur result, Pinned α a)
pinnedModify function index (Pinned vector) = Control.do
  (result, vector) <-
    Fixed.update
      index
      ( \value ->
          case function value of
            (updatedValue, auxiliary) ->
              Control.pure (Ur auxiliary, Ur updatedValue)
      )
      vector
  Control.pure (result, Pinned vector)

pinnedUnsafeModify ::
  (U.Unbox a, α >= γ) =>
  (a -> (a, result)) ->
  Int ->
  Pinned α a %1 ->
  BO γ (Ur result, Pinned α a)
pinnedUnsafeModify function index (Pinned vector) = Control.do
  (result, vector) <-
    Fixed.unsafeUpdate
      index
      ( \value ->
          case function value of
            (updatedValue, auxiliary) ->
              Control.pure (Ur auxiliary, Ur updatedValue)
      )
      vector
  Control.pure (result, Pinned vector)

pinnedBufferUnsafeCopyAt ::
  (U.Unbox a, α >= γ) =>
  Int ->
  PinnedBuffer α a %1 ->
  BO γ (Ur a, PinnedBuffer α a)
pinnedBufferUnsafeCopyAt index (PinnedBuffer vector) = Control.do
  (result, vector) <- Fixed.unsafeGet index vector
  Control.pure (result, PinnedBuffer vector)

pinnedBufferUnsafeWrite ::
  (U.Unbox a, α >= γ) =>
  Int ->
  a ->
  PinnedBuffer α a %1 ->
  BO γ (PinnedBuffer α a)
pinnedBufferUnsafeWrite index value (PinnedBuffer vector) = Control.do
  vector <- Fixed.unsafeWrite index value vector
  Control.pure (PinnedBuffer vector)
