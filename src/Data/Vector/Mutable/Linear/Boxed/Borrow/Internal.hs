{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

{- |
Growable boxed storage with stable outer identity.

The replaceable buffer and logical length live in a linear header behind one
Pure Borrow reference. Shared observations use 'RefBorrow.readShare'. Mutation
can open the header once with 'withPinned' and then perform an arbitrary scoped
sequence of reads, appends, and growth without another reference update.
-}
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
  pinnedSize,
  pinnedCapacity,
  pinnedCopyAt,
  pinnedUnsafeCopyAt,
  pinnedBufferUnsafeCopyAt,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.BO.Unsafe (
  Alias (UnsafeAlias),
  unsafeMapAlias,
  unsafeSystemIOToBO,
 )
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow qualified as RefBorrow
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as MV
import GHC.Exts qualified as GHC
import GHC.IO (unsafePerformIO)
import GHC.Stack (HasCallStack)
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as NonLinear

data Header a where
  Header ::
    {-# UNPACK #-} !Int ->
    !(MV.IOVector a) %1 ->
    Header a

data Vector a where
  Vector :: !(Ref.Ref (Header a)) %1 -> Vector a

-- | A header removed from its stable reference for one scoped transaction.
data Pinned pin a where
  Pinned ::
    {-# UNPACK #-} !Int ->
    !(MV.IOVector a) %1 ->
    Pinned pin a

-- | A zero-cost pin of only the active boxed buffer.
newtype PinnedBuffer pin a where
  PinnedBuffer :: MV.IOVector a %1 -> PinnedBuffer pin a

type role Header nominal

type role Vector nominal

type role Pinned nominal nominal

type role PinnedBuffer nominal nominal

-- | Allocate an empty vector.
empty :: Linearly %1 -> Vector a
{-# NOINLINE empty #-}
empty = GHC.noinline \linear ->
  dup linear & \(bufferLinear, refLinear) ->
    Vector (Ref.new (Header 0 (allocateBuffer 0 bufferLinear)) refLinear)

-- | Clone immutable input before mutation.
fromVector ::
  (Copyable a) =>
  V.Vector a ->
  Linearly %1 ->
  Vector a
{-# NOINLINE fromVector #-}
fromVector = GHC.noinline \source linear ->
  dup linear & \(bufferLinear, refLinear) ->
    Vector
      ( Ref.new
          (Header (V.length source) (cloneBuffer source bufferLinear))
          refLinear
      )

allocateBuffer :: Int -> Linearly %1 -> MV.IOVector a
{-# NOINLINE allocateBuffer #-}
allocateBuffer =
  GHC.noinline \count linear ->
    linear `lseq` unsafePerformIO (MV.unsafeNew count)

cloneBuffer :: V.Vector a -> Linearly %1 -> MV.IOVector a
{-# NOINLINE cloneBuffer #-}
cloneBuffer =
  GHC.noinline \source linear ->
    linear `lseq` unsafePerformIO (V.thaw source)

-- | Freeze exactly the logical prefix after all borrows have ended.
toVector ::
  (Copyable a) =>
  Vector a %1 ->
  Ur (V.Vector a)
{-# NOINLINE toVector #-}
toVector =
  GHC.noinline $
    Unsafe.toLinear \(Vector ref) ->
      case Ref.free ref of
        Header logicalSize buffer ->
          Ur
            ( unsafePerformIO
                (V.unsafeFreeze (MV.unsafeTake logicalSize buffer))
            )

-- | Dispose of a vector that does not need to be frozen.
dispose :: Vector a %1 -> ()
{-# INLINE dispose #-}
dispose =
  Unsafe.toLinear \(Vector ref) ->
    Unsafe.toLinear (\ !_ -> ()) (Ref.free ref)

toRefAlias ::
  Alias aliasKind lifetime (Vector a) %1 ->
  Alias aliasKind lifetime (Ref.Ref (Header a))
{-# INLINE toRefAlias #-}
toRefAlias =
  unsafeMapAlias
    (Unsafe.toLinear \(Vector ref) -> ref)

fromRefAlias ::
  Alias aliasKind lifetime (Ref.Ref (Header a)) %1 ->
  Alias aliasKind lifetime (Vector a)
{-# INLINE fromRefAlias #-}
fromRefAlias =
  unsafeMapAlias
    (Unsafe.toLinear Vector)

leakSharedHeader :: Header a %1 -> ()
{-# INLINE leakSharedHeader #-}
leakSharedHeader = Unsafe.toLinear \ !_ -> ()

inspectHeader ::
  (lifetime >= scope) =>
  (Header a %1 -> BO scope (result, Header a)) %1 ->
  Borrow borrowKind lifetime (Vector a) %1 ->
  BO scope result
{-# INLINE inspectHeader #-}
inspectHeader action vector =
  case share vector of
    Ur sharedVector -> Control.do
      Ur (UnsafeAlias header) <-
        RefBorrow.readShare (toRefAlias sharedVector)
      (result, retainedHeader) <- action header
      Control.pure (leakSharedHeader retainedHeader `lseq` result)

-- | Open the replaceable header once for a scoped transaction.
withPinned ::
  forall a lifetime scope result.
  (lifetime >= scope) =>
  (forall pin. Pinned pin a %1 -> BO scope (result, Pinned pin a)) %1 ->
  Mut lifetime (Vector a) %1 ->
  BO scope (result, Mut lifetime (Vector a))
{-# INLINE withPinned #-}
withPinned action vector = Control.do
  (result, ref) <-
    RefBorrow.update
      ( \(Header logicalSize buffer) -> Control.do
          (transactionResult, Pinned finalSize finalBuffer) <-
            action (Pinned logicalSize buffer)
          Control.pure
            ( transactionResult
            , Header finalSize finalBuffer
            )
      )
      (toRefAlias vector)
  Control.pure (result, fromRefAlias ref)

-- | Pin only the current active buffer and keep its logical length fixed.
withPinnedBuffer ::
  forall a lifetime scope result.
  (lifetime >= scope) =>
  ( forall pin.
    Int ->
    PinnedBuffer pin a %1 ->
    BO scope (result, PinnedBuffer pin a)
  ) %1 ->
  Mut lifetime (Vector a) %1 ->
  BO scope (result, Mut lifetime (Vector a))
{-# INLINE withPinnedBuffer #-}
withPinnedBuffer action vector = Control.do
  (result, ref) <-
    RefBorrow.update
      ( \(Header logicalSize buffer) -> Control.do
          (transactionResult, PinnedBuffer finalBuffer) <-
            action logicalSize (PinnedBuffer buffer)
          Control.pure
            ( transactionResult
            , Header logicalSize finalBuffer
            )
      )
      (toRefAlias vector)
  Control.pure (result, fromRefAlias ref)

-- | Return the logical length through a shared observation.
size ::
  (lifetime >= scope) =>
  Borrow borrowKind lifetime (Vector a) %1 ->
  BO scope (Ur Int)
{-# INLINE size #-}
size =
  inspectHeader \(Header logicalSize buffer) ->
    Control.pure (Ur logicalSize, Header logicalSize buffer)

-- | Return the current backing capacity through a shared observation.
capacity ::
  (lifetime >= scope) =>
  Borrow borrowKind lifetime (Vector a) %1 ->
  BO scope (Ur Int)
{-# INLINE capacity #-}
capacity =
  inspectHeader $
    Unsafe.toLinear \(Header logicalSize buffer) ->
      Control.pure (Ur (MV.length buffer), Header logicalSize buffer)

-- | Copy a logical element after checking its index.
copyAt ::
  (HasCallStack, Copyable a, lifetime >= scope) =>
  Int ->
  Share lifetime (Vector a) ->
  BO scope (Ur a)
{-# INLINE copyAt #-}
copyAt index vector =
  inspectHeader
    ( Unsafe.toLinear \(Header logicalSize buffer) ->
        if index < 0 || index >= logicalSize
          then
            error
              ( "copyAt: index "
                  <> show index
                  <> " out of bounds for length "
                  <> show logicalSize
              )
              buffer
          else unsafeSystemIOToBO do
            !value <- MV.unsafeRead buffer index
            NonLinear.pure (Ur value, Header logicalSize buffer)
    )
    vector

-- | Copy a logical element without checking its index.
unsafeCopyAt ::
  (Copyable a, lifetime >= scope) =>
  Int ->
  Share lifetime (Vector a) ->
  BO scope (Ur a)
{-# INLINE unsafeCopyAt #-}
unsafeCopyAt index vector =
  inspectHeader
    ( Unsafe.toLinear \(Header logicalSize buffer) ->
        unsafeSystemIOToBO do
          !value <- MV.unsafeRead buffer index
          NonLinear.pure (Ur value, Header logicalSize buffer)
    )
    vector

-- | Temporarily share a mutable vector and copy a checked element.
copyAtMut ::
  forall a lifetime scope.
  (HasCallStack, Copyable a, lifetime >= scope) =>
  Int ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Ur a, Mut lifetime (Vector a))
{-# INLINE copyAtMut #-}
copyAtMut index vector =
  upcast $ sharing @_ @lifetime vector $ copyAt index

-- | Temporarily share a mutable vector and copy an unchecked element.
unsafeCopyAtMut ::
  forall a lifetime scope.
  (Copyable a, lifetime >= scope) =>
  Int ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Ur a, Mut lifetime (Vector a))
{-# INLINE unsafeCopyAtMut #-}
unsafeCopyAtMut index vector =
  upcast $ sharing @_ @lifetime vector $ unsafeCopyAt index

-- | Append one copyable element in a one-operation transaction.
push ::
  (Copyable a, lifetime >= scope) =>
  a ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Mut lifetime (Vector a))
{-# INLINE push #-}
push value vector = Control.do
  ((), updatedVector) <-
    withPinned
      ( \pinned -> Control.do
          updatedPinned <- growAndPush value pinned
          Control.pure ((), updatedPinned)
      )
      vector
  Control.pure updatedVector

-- | Return a pinned header's logical length.
pinnedSize :: Pinned pin a %1 -> (Ur Int, Pinned pin a)
{-# INLINE pinnedSize #-}
pinnedSize (Pinned logicalSize buffer) =
  (Ur logicalSize, Pinned logicalSize buffer)

-- | Return a pinned header's backing capacity.
pinnedCapacity :: Pinned pin a %1 -> (Ur Int, Pinned pin a)
{-# INLINE pinnedCapacity #-}
pinnedCapacity =
  Unsafe.toLinear \(Pinned logicalSize buffer) ->
    (Ur (MV.length buffer), Pinned logicalSize buffer)

-- | Copy a pinned logical element after checking its index.
pinnedCopyAt ::
  (HasCallStack, Copyable a) =>
  Int ->
  Pinned pin a %1 ->
  BO scope (Ur a, Pinned pin a)
{-# INLINE pinnedCopyAt #-}
pinnedCopyAt index pinned =
  case pinnedSize pinned of
    (Ur logicalSize, sizedPinned) ->
      if index < 0 || index >= logicalSize
        then
          error
            ( "pinnedCopyAt: index "
                <> show index
                <> " out of bounds for length "
                <> show logicalSize
            )
            sizedPinned
        else pinnedUnsafeCopyAt index sizedPinned

-- | Copy a pinned logical element without checking its index.
pinnedUnsafeCopyAt ::
  (Copyable a) =>
  Int ->
  Pinned pin a %1 ->
  BO scope (Ur a, Pinned pin a)
{-# INLINE pinnedUnsafeCopyAt #-}
pinnedUnsafeCopyAt =
  Unsafe.toLinear2 \index (Pinned logicalSize buffer) ->
    unsafeSystemIOToBO do
      !value <- MV.unsafeRead buffer index
      NonLinear.pure (Ur value, Pinned logicalSize buffer)

-- | Copy from a buffer pin without checking against the supplied logical size.
pinnedBufferUnsafeCopyAt ::
  (Copyable a) =>
  Int ->
  PinnedBuffer pin a %1 ->
  BO scope (Ur a, PinnedBuffer pin a)
{-# INLINE pinnedBufferUnsafeCopyAt #-}
pinnedBufferUnsafeCopyAt =
  Unsafe.toLinear2 \index pinned@(PinnedBuffer buffer) ->
    unsafeSystemIOToBO do
      !value <- MV.unsafeRead buffer index
      NonLinear.pure (Ur value, pinned)

-- Internal growth operation. It is intentionally unavailable to a caller that
-- holds a 'Pinned' view.
growAndPush ::
  (Copyable a) =>
  a ->
  Pinned pin a %1 ->
  BO scope (Pinned pin a)
{-# INLINE growAndPush #-}
growAndPush =
  Unsafe.toLinear2 \value (Pinned logicalSize buffer) ->
    unsafeSystemIOToBO do
      let !oldCapacity = MV.length buffer
      grown <-
        if logicalSize < oldCapacity
          then NonLinear.pure buffer
          else do
            let !newCapacity = max 1 (oldCapacity * 2)
            MV.unsafeGrow buffer (newCapacity - oldCapacity)
      MV.unsafeWrite grown logicalSize value
      NonLinear.pure (Pinned (logicalSize + 1) grown)
