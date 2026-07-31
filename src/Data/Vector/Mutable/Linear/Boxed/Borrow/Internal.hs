{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Data.Vector.Mutable.Linear.Boxed.Borrow.Internal (
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
  push,
  withPinned,
  withPinnedBuffer,
  getContents,
  pinnedSize,
  pinnedCapacity,
  pinnedCopyAt,
  pinnedUnsafeCopyAt,
  pinnedBufferUnsafeCopyAt,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Vector qualified as V
import Data.Vector.Generic.Mutable.Growable.Linear.Borrow.Unrestricted qualified as Growable
import Data.Vector.Generic.Mutable.Linear.Borrow.Unrestricted qualified as Fixed
import GHC.Stack (HasCallStack)
import Prelude.Linear hiding (getContents)

type Vector = Growable.GrowableVector V.Vector

newtype Pinned α a = Pinned (Mut α (Fixed.Vector V.Vector a))

newtype PinnedBuffer α a = PinnedBuffer (Mut α (Fixed.Vector V.Vector a))

type role Pinned nominal nominal

type role PinnedBuffer nominal nominal

empty :: Linearly %1 -> Vector a
empty = Growable.empty

fromVector ::
  V.Vector a ->
  Linearly %1 ->
  Vector a
fromVector = Growable.fromVector

toVector ::
  Vector a %1 ->
  Ur (V.Vector a)
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
  Borrow bk α (Vector a) %1 ->
  (Ur Int, Borrow bk α (Vector a))
capacity = Growable.capacity

copyAt ::
  (HasCallStack, α >= γ) =>
  Int ->
  Share α (Vector a) ->
  BO γ (Ur a)
copyAt = Growable.copyAt

unsafeCopyAt ::
  (α >= γ) =>
  Int ->
  Share α (Vector a) ->
  BO γ (Ur a)
unsafeCopyAt = Growable.unsafeCopyAt

copyAtMut ::
  (HasCallStack, α >= γ) =>
  Int ->
  Mut α (Vector a) %1 ->
  BO γ (Ur a, Mut α (Vector a))
copyAtMut = Growable.copyAtMut

unsafeCopyAtMut ::
  (α >= γ) =>
  Int ->
  Mut α (Vector a) %1 ->
  BO γ (Ur a, Mut α (Vector a))
unsafeCopyAtMut = Growable.unsafeCopyAtMut

push ::
  (HasCallStack, α >= γ) =>
  a ->
  Mut α (Vector a) %1 ->
  BO γ (Mut α (Vector a))
push = Growable.push

getContents ::
  Borrow bk α (Vector a) %1 ->
  Borrow bk α (Fixed.Vector V.Vector a)
getContents = Growable.getContents

withPinned ::
  forall a α γ result.
  (α >= γ) =>
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
  (α >= γ) =>
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
  Pinned α a %1 ->
  (Ur Int, Pinned α a)
pinnedSize (Pinned vector) =
  case Fixed.size vector of
    (result, vector) -> (result, Pinned vector)

pinnedCapacity ::
  Pinned α a %1 ->
  (Ur Int, Pinned α a)
pinnedCapacity = pinnedSize

pinnedCopyAt ::
  (HasCallStack, α >= γ) =>
  Int ->
  Pinned α a %1 ->
  BO γ (Ur a, Pinned α a)
pinnedCopyAt index (Pinned vector) = Control.do
  (result, vector) <- Fixed.get index vector
  Control.pure (result, Pinned vector)

pinnedUnsafeCopyAt ::
  (α >= γ) =>
  Int ->
  Pinned α a %1 ->
  BO γ (Ur a, Pinned α a)
pinnedUnsafeCopyAt index (Pinned vector) = Control.do
  (result, vector) <- Fixed.unsafeGet index vector
  Control.pure (result, Pinned vector)

pinnedBufferUnsafeCopyAt ::
  (α >= γ) =>
  Int ->
  PinnedBuffer α a %1 ->
  BO γ (Ur a, PinnedBuffer α a)
pinnedBufferUnsafeCopyAt index (PinnedBuffer vector) = Control.do
  (result, vector) <- Fixed.unsafeGet index vector
  Control.pure (result, PinnedBuffer vector)
