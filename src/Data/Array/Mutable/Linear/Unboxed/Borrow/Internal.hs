{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

{- |
Fixed-size unboxed storage whose backing object remains stable for an entire
Pure Borrow lifetime.

The constructor is private. Reads copy primitive cells into 'Ur'; writes are
restricted to values whose Pure Borrow contracts permit copying and disposal.
-}
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
  pinnedUnsafeCopyAt,
  pinnedUnsafeWrite,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.BO.Unsafe (
  Alias (UnsafeAlias),
  unsafeSystemIOToBO,
 )
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import GHC.Exts qualified as GHC
import GHC.IO (unsafePerformIO)
import GHC.Stack (HasCallStack)
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as NonLinear

-- | A fixed-size linearly owned unboxed array.
newtype UArray a = UArray (UM.IOVector a)

type role UArray nominal

-- | A rank-2 view of a fixed store's backing buffer.
newtype Pinned pin a where
  Pinned :: UM.IOVector a %1 -> Pinned pin a

type role Pinned nominal nominal

-- | Allocate an initialized array.
constant ::
  (U.Unbox a, Copyable a) =>
  Int ->
  a ->
  Linearly %1 ->
  UArray a
{-# NOINLINE constant #-}
constant = GHC.noinline \count !value linear ->
  linear `lseq`
    UArray
      (unsafePerformIO (UM.replicate count value))

-- | Clone immutable input before mutation.
fromVector ::
  (U.Unbox a, Copyable a) =>
  U.Vector a ->
  Linearly %1 ->
  UArray a
{-# NOINLINE fromVector #-}
fromVector = GHC.noinline \source linear ->
  linear `lseq`
    UArray
      (unsafePerformIO (U.thaw source))

-- | Freeze the owner after every borrow has ended.
toVector ::
  (U.Unbox a, Copyable a) =>
  UArray a %1 ->
  Ur (U.Vector a)
{-# NOINLINE toVector #-}
toVector =
  GHC.noinline $
    Unsafe.toLinear \(UArray vector) ->
      Ur (unsafePerformIO (U.unsafeFreeze vector))

-- | Dispose of an array that does not need to be frozen.
dispose :: UArray a %1 -> ()
{-# INLINE dispose #-}
dispose = Unsafe.toLinear \ !_ -> ()

-- | Open a fixed store once for a scoped transaction.
withPinned ::
  forall a lifetime scope result.
  (lifetime >= scope) =>
  (forall pin. Pinned pin a %1 -> BO scope (result, Pinned pin a)) %1 ->
  Mut lifetime (UArray a) %1 ->
  BO scope (result, Mut lifetime (UArray a))
{-# INLINE withPinned #-}
withPinned action =
  Unsafe.toLinear \(UnsafeAlias (UArray vector)) -> Control.do
    (result, Pinned finalVector) <- action (Pinned vector)
    Control.pure (result, UnsafeAlias (UArray finalVector))

-- | Return the physical size while preserving a borrow.
size ::
  (U.Unbox a) =>
  Borrow borrowKind lifetime (UArray a) %1 ->
  (Ur Int, Borrow borrowKind lifetime (UArray a))
{-# INLINE size #-}
size =
  Unsafe.toLinear \(UnsafeAlias (UArray vector)) ->
    (Ur (UM.length vector), UnsafeAlias (UArray vector))

-- | Copy a shared cell after checking its index.
copyAt ::
  (HasCallStack, U.Unbox a, Copyable a, lifetime >= scope) =>
  Int ->
  Share lifetime (UArray a) ->
  BO scope (Ur a)
{-# INLINE copyAt #-}
copyAt index array =
  case size array of
    (Ur arraySize, updatedArray) ->
      if index < 0 || index >= arraySize
        then
          error
            ( "copyAt: index "
                <> show index
                <> " out of bounds for length "
                <> show arraySize
            )
            updatedArray
        else unsafeCopyAt index updatedArray

-- | Copy a shared cell without checking its index.
unsafeCopyAt ::
  (U.Unbox a, Copyable a, lifetime >= scope) =>
  Int ->
  Share lifetime (UArray a) ->
  BO scope (Ur a)
{-# INLINE unsafeCopyAt #-}
unsafeCopyAt =
  Unsafe.toLinear2 \index (UnsafeAlias (UArray vector)) ->
    unsafeSystemIOToBO do
      !value <- UM.unsafeRead vector index
      NonLinear.pure (Ur value)

-- | Copy a cell after checking its index.
copyAtMut ::
  forall a lifetime scope.
  (HasCallStack, U.Unbox a, Copyable a, lifetime >= scope) =>
  Int ->
  Mut lifetime (UArray a) %1 ->
  BO scope (Ur a, Mut lifetime (UArray a))
{-# INLINE copyAtMut #-}
copyAtMut index array =
  upcast $ sharing @_ @lifetime array $ copyAt index

-- | Copy a cell without checking its index.
unsafeCopyAtMut ::
  forall a lifetime scope.
  (U.Unbox a, Copyable a, lifetime >= scope) =>
  Int ->
  Mut lifetime (UArray a) %1 ->
  BO scope (Ur a, Mut lifetime (UArray a))
{-# INLINE unsafeCopyAtMut #-}
unsafeCopyAtMut index array =
  upcast $ sharing @_ @lifetime array $ unsafeCopyAt index

-- | Overwrite a disposable copyable cell after checking its index.
write ::
  ( HasCallStack
  , U.Unbox a
  , Copyable a
  , Consumable a
  , lifetime >= scope
  ) =>
  Int ->
  a ->
  Mut lifetime (UArray a) %1 ->
  BO scope (Mut lifetime (UArray a))
{-# INLINE write #-}
write index value array = DataFlow.do
  (Ur arraySize, updatedArray) <- size array
  if index < 0 || index >= arraySize
    then
      error
        ( "write: index "
            <> show index
            <> " out of bounds for length "
            <> show arraySize
        )
        updatedArray
    else unsafeWrite index value updatedArray

-- | Overwrite a disposable copyable cell without checking its index.
unsafeWrite ::
  (U.Unbox a, Copyable a, Consumable a, lifetime >= scope) =>
  Int ->
  a ->
  Mut lifetime (UArray a) %1 ->
  BO scope (Mut lifetime (UArray a))
{-# INLINE unsafeWrite #-}
unsafeWrite =
  Unsafe.toLinear3 \index !value array@(UnsafeAlias (UArray vector)) ->
    unsafeSystemIOToBO do
      UM.unsafeWrite vector index value
      NonLinear.pure array

-- | Modify a cell and return an unrestricted auxiliary result.
modify ::
  ( HasCallStack
  , U.Unbox a
  , Copyable a
  , Consumable a
  , lifetime >= scope
  ) =>
  (a -> (a, result)) ->
  Int ->
  Mut lifetime (UArray a) %1 ->
  BO scope (Ur result, Mut lifetime (UArray a))
{-# INLINE modify #-}
modify function index array = DataFlow.do
  (Ur arraySize, updatedArray) <- size array
  if index < 0 || index >= arraySize
    then
      error
        ( "modify: index "
            <> show index
            <> " out of bounds for length "
            <> show arraySize
        )
        updatedArray
    else unsafeModify function index updatedArray

-- | Modify a cell without checking its index.
unsafeModify ::
  (U.Unbox a, Copyable a, Consumable a, lifetime >= scope) =>
  (a -> (a, result)) ->
  Int ->
  Mut lifetime (UArray a) %1 ->
  BO scope (Ur result, Mut lifetime (UArray a))
{-# INLINE unsafeModify #-}
unsafeModify =
  Unsafe.toLinear3 \function index array@(UnsafeAlias (UArray vector)) ->
    unsafeSystemIOToBO do
      !old <- UM.unsafeRead vector index
      case function old of
        (!new, !result) -> do
          UM.unsafeWrite vector index new
          NonLinear.pure (Ur result, array)

-- | Copy an unchecked cell through a rank-2 fixed-store pin.
pinnedUnsafeCopyAt ::
  (U.Unbox a, Copyable a) =>
  Int ->
  Pinned pin a %1 ->
  BO scope (Ur a, Pinned pin a)
{-# INLINE pinnedUnsafeCopyAt #-}
pinnedUnsafeCopyAt =
  Unsafe.toLinear2 \index pinned@(Pinned vector) ->
    unsafeSystemIOToBO do
      !value <- UM.unsafeRead vector index
      NonLinear.pure (Ur value, pinned)

-- | Overwrite an unchecked cell through a rank-2 fixed-store pin.
pinnedUnsafeWrite ::
  (U.Unbox a, Copyable a, Consumable a) =>
  Int ->
  a ->
  Pinned pin a %1 ->
  BO scope (Pinned pin a)
{-# INLINE pinnedUnsafeWrite #-}
pinnedUnsafeWrite =
  Unsafe.toLinear3 \index !value pinned@(Pinned vector) ->
    unsafeSystemIOToBO do
      UM.unsafeWrite vector index value
      NonLinear.pure pinned
