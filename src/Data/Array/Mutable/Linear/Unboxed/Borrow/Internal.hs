{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Data.Array.Mutable.Linear.Unboxed.Borrow.Internal (
  UArray,
  Pinned (..),
  constant,
  fromVector,
  toVector,
  dispose,
  withPinned,
  size,
  copyAt,
  unsafeCopyAt,
  copyAtMut,
  unsafeCopyAtMut,
  write,
  unsafeWrite,
  modify,
  unsafeModify,
  pinnedSize,
  pinnedUnsafeCopyAt,
  pinnedUnsafeWrite,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Vector.Generic.Mutable.Linear.Borrow.Unrestricted qualified as Upstream
import Data.Vector.Unboxed qualified as U
import GHC.Stack (HasCallStack)
import Prelude.Linear

type UArray = Upstream.Vector U.Vector

newtype Pinned α a = Pinned (Mut α (UArray a))

type role Pinned nominal nominal

constant ::
  (U.Unbox a) =>
  Int ->
  a ->
  Linearly %1 ->
  UArray a
constant = Upstream.constant

fromVector ::
  (U.Unbox a) =>
  U.Vector a ->
  Linearly %1 ->
  UArray a
fromVector = Upstream.fromVector

toVector ::
  (U.Unbox a) =>
  UArray a %1 ->
  Ur (U.Vector a)
toVector = Upstream.toVector

dispose :: UArray a %1 -> ()
dispose = consume

withPinned ::
  (U.Unbox a, α >= γ) =>
  (Pinned α a %1 -> BO γ (result, Pinned α a)) %1 ->
  Mut α (UArray a) %1 ->
  BO γ (result, Mut α (UArray a))
withPinned action array = Control.do
  (result, Pinned array) <- action (Pinned array)
  Control.pure (result, array)

size ::
  (U.Unbox a) =>
  Borrow bk α (UArray a) %1 ->
  (Ur Int, Borrow bk α (UArray a))
size = Upstream.size

copyAt ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  Int ->
  Share α (UArray a) ->
  BO γ (Ur a)
copyAt = Upstream.copyAt

unsafeCopyAt ::
  (U.Unbox a, α >= γ) =>
  Int ->
  Share α (UArray a) ->
  BO γ (Ur a)
unsafeCopyAt index array = Control.do
  (value, array) <- Upstream.unsafeGet index array
  Control.pure (consume array `lseq` value)

copyAtMut ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  Int ->
  Mut α (UArray a) %1 ->
  BO γ (Ur a, Mut α (UArray a))
copyAtMut = Upstream.copyAtMut

unsafeCopyAtMut ::
  (U.Unbox a, α >= γ) =>
  Int ->
  Mut α (UArray a) %1 ->
  BO γ (Ur a, Mut α (UArray a))
unsafeCopyAtMut = Upstream.unsafeGet

write ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  Int ->
  a ->
  Mut α (UArray a) %1 ->
  BO γ (Mut α (UArray a))
write = Upstream.write

unsafeWrite ::
  (U.Unbox a, α >= γ) =>
  Int ->
  a ->
  Mut α (UArray a) %1 ->
  BO γ (Mut α (UArray a))
unsafeWrite = Upstream.unsafeWrite

modify ::
  (HasCallStack, U.Unbox a, α >= γ) =>
  (a -> (a, result)) ->
  Int ->
  Mut α (UArray a) %1 ->
  BO γ (Ur result, Mut α (UArray a))
modify function index =
  Upstream.update index \value ->
    case function value of
      (updatedValue, result) ->
        Control.pure (Ur result, Ur updatedValue)

unsafeModify ::
  (U.Unbox a, α >= γ) =>
  (a -> (a, result)) ->
  Int ->
  Mut α (UArray a) %1 ->
  BO γ (Ur result, Mut α (UArray a))
unsafeModify function index =
  Upstream.unsafeUpdate index \value ->
    case function value of
      (updatedValue, result) ->
        Control.pure (Ur result, Ur updatedValue)

pinnedSize ::
  (U.Unbox a) =>
  Pinned α a %1 ->
  (Ur Int, Pinned α a)
pinnedSize (Pinned array) =
  case Upstream.size array of
    (size_, array) -> (size_, Pinned array)

pinnedUnsafeCopyAt ::
  (U.Unbox a, α >= γ) =>
  Int ->
  Pinned α a %1 ->
  BO γ (Ur a, Pinned α a)
pinnedUnsafeCopyAt index (Pinned array) = Control.do
  (value, array) <- Upstream.unsafeGet index array
  Control.pure (value, Pinned array)

pinnedUnsafeWrite ::
  (U.Unbox a, α >= γ) =>
  Int ->
  a ->
  Pinned α a %1 ->
  BO γ (Pinned α a)
pinnedUnsafeWrite index value (Pinned array) = Control.do
  array <- Upstream.unsafeWrite index value array
  Control.pure (Pinned array)
