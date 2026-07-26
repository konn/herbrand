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
Growable unboxed storage with stable outer identity.

The replaceable buffer and logical length live in a linear header behind one
Pure Borrow reference. Shared observations use 'RefBorrow.readShare'. Mutation
can open the header once with 'withPinned' and then perform an arbitrary scoped
sequence of reads, writes, truncations, and growth without another reference
update.
-}
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
  truncate,
  withPinned,
  withPinnedBuffer,
  pinnedSize,
  pinnedCapacity,
  pinnedCopyAt,
  pinnedUnsafeCopyAt,
  pinnedWrite,
  pinnedUnsafeWrite,
  pinnedModify,
  pinnedUnsafeModify,
  pinnedTruncate,
  pinnedBufferUnsafeCopyAt,
  pinnedBufferUnsafeWrite,
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
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Mutable qualified as UM
import GHC.Exts qualified as GHC
import GHC.IO (unsafePerformIO)
import GHC.Stack (HasCallStack)
import Prelude.Linear hiding (truncate)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as NonLinear

data Header a where
  Header ::
    {-# UNPACK #-} !Int ->
    !(UM.IOVector a) %1 ->
    Header a

data Vector a where
  Vector :: !(Ref.Ref (Header a)) %1 -> Vector a

-- | A header removed from its stable reference for one scoped transaction.
data Pinned pin a where
  Pinned ::
    {-# UNPACK #-} !Int ->
    !(UM.IOVector a) %1 ->
    Pinned pin a

{- | A zero-cost pin of only the active buffer.

The logical length is supplied separately by 'withPinnedBuffer' and cannot
be changed. The newtype erases before the recursive hot worker.
-}
newtype PinnedBuffer pin a where
  PinnedBuffer :: UM.IOVector a %1 -> PinnedBuffer pin a

type role Header nominal

type role Vector nominal

type role Pinned nominal nominal

type role PinnedBuffer nominal nominal

-- | Allocate an empty vector.
empty :: (U.Unbox a) => Linearly %1 -> Vector a
{-# NOINLINE empty #-}
empty = GHC.noinline \linear ->
  dup linear & \(bufferLinear, refLinear) ->
    let !buffer = allocateBuffer 0 bufferLinear
        !header = Header 0 buffer
     in Vector (Ref.new header refLinear)

-- | Clone an immutable vector.
fromVector ::
  (U.Unbox a, Copyable a) =>
  U.Vector a ->
  Linearly %1 ->
  Vector a
{-# NOINLINE fromVector #-}
fromVector = GHC.noinline \source linear ->
  dup linear & \(bufferLinear, refLinear) ->
    let !buffer = cloneBuffer source bufferLinear
        !header = Header (U.length source) buffer
     in Vector (Ref.new header refLinear)

allocateBuffer :: (U.Unbox a) => Int -> Linearly %1 -> UM.IOVector a
{-# NOINLINE allocateBuffer #-}
allocateBuffer =
  GHC.noinline \count linear ->
    linear `lseq` unsafePerformIO (UM.unsafeNew count)

cloneBuffer ::
  (U.Unbox a) =>
  U.Vector a ->
  Linearly %1 ->
  UM.IOVector a
{-# NOINLINE cloneBuffer #-}
cloneBuffer =
  GHC.noinline \source linear ->
    linear `lseq` unsafePerformIO (U.thaw source)

-- | Freeze exactly the logical prefix after all borrows have ended.
toVector ::
  (U.Unbox a, Copyable a) =>
  Vector a %1 ->
  Ur (U.Vector a)
{-# NOINLINE toVector #-}
toVector =
  GHC.noinline $
    Unsafe.toLinear \(Vector ref) ->
      case Ref.free ref of
        Header logicalSize buffer ->
          Ur
            ( unsafePerformIO
                (U.unsafeFreeze (UM.unsafeTake logicalSize buffer))
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

{- | Pin only the current active buffer and keep its logical length fixed.

This is the hot-loop entry point. Unlike 'Pinned', the view is a newtype, so
optimized recursive workers carry the active vector directly.
-}
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
  (U.Unbox a, lifetime >= scope) =>
  Borrow borrowKind lifetime (Vector a) %1 ->
  BO scope (Ur Int)
{-# INLINE capacity #-}
capacity =
  inspectHeader $
    Unsafe.toLinear \(Header logicalSize buffer) ->
      Control.pure (Ur (UM.length buffer), Header logicalSize buffer)

-- | Copy a logical cell after checking its index.
copyAt ::
  (HasCallStack, U.Unbox a, Copyable a, lifetime >= scope) =>
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
            !value <- UM.unsafeRead buffer index
            NonLinear.pure (Ur value, Header logicalSize buffer)
    )
    vector

-- | Copy a logical cell without checking its index.
unsafeCopyAt ::
  (U.Unbox a, Copyable a, lifetime >= scope) =>
  Int ->
  Share lifetime (Vector a) ->
  BO scope (Ur a)
{-# INLINE unsafeCopyAt #-}
unsafeCopyAt index vector =
  inspectHeader
    ( Unsafe.toLinear \(Header logicalSize buffer) ->
        unsafeSystemIOToBO do
          !value <- UM.unsafeRead buffer index
          NonLinear.pure (Ur value, Header logicalSize buffer)
    )
    vector

-- | Temporarily share a mutable vector and copy a checked cell.
copyAtMut ::
  forall a lifetime scope.
  (HasCallStack, U.Unbox a, Copyable a, lifetime >= scope) =>
  Int ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Ur a, Mut lifetime (Vector a))
{-# INLINE copyAtMut #-}
copyAtMut index vector =
  upcast $ sharing @_ @lifetime vector $ copyAt index

-- | Temporarily share a mutable vector and copy an unchecked cell.
unsafeCopyAtMut ::
  forall a lifetime scope.
  (U.Unbox a, Copyable a, lifetime >= scope) =>
  Int ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Ur a, Mut lifetime (Vector a))
{-# INLINE unsafeCopyAtMut #-}
unsafeCopyAtMut index vector =
  upcast $ sharing @_ @lifetime vector $ unsafeCopyAt index

-- | Overwrite a logical cell after checking its index.
write ::
  ( HasCallStack
  , U.Unbox a
  , Copyable a
  , Consumable a
  , lifetime >= scope
  ) =>
  Int ->
  a ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Mut lifetime (Vector a))
{-# INLINE write #-}
write index value vector = Control.do
  ((), updatedVector) <-
    withPinned
      ( \pinned -> Control.do
          pinned <- pinnedWrite index value pinned
          Control.pure ((), pinned)
      )
      vector
  Control.pure updatedVector

-- | Overwrite a logical cell without checking its index.
unsafeWrite ::
  ( U.Unbox a
  , Copyable a
  , Consumable a
  , lifetime >= scope
  ) =>
  Int ->
  a ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Mut lifetime (Vector a))
{-# INLINE unsafeWrite #-}
unsafeWrite index value vector = Control.do
  ((), updatedVector) <-
    withPinned
      ( \pinned -> Control.do
          pinned <- pinnedUnsafeWrite index value pinned
          Control.pure ((), pinned)
      )
      vector
  Control.pure updatedVector

-- | Modify a logical cell and return an unrestricted auxiliary result.
modify ::
  ( HasCallStack
  , U.Unbox a
  , Copyable a
  , Consumable a
  , lifetime >= scope
  ) =>
  (a -> (a, result)) ->
  Int ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Ur result, Mut lifetime (Vector a))
{-# INLINE modify #-}
modify function index vector =
  withPinned (pinnedModify function index) vector

-- | Modify a logical cell without checking its index.
unsafeModify ::
  ( U.Unbox a
  , Copyable a
  , Consumable a
  , lifetime >= scope
  ) =>
  (a -> (a, result)) ->
  Int ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Ur result, Mut lifetime (Vector a))
{-# INLINE unsafeModify #-}
unsafeModify function index vector =
  withPinned (pinnedUnsafeModify function index) vector

-- | Append one element, growing the private buffer when necessary.
push ::
  (U.Unbox a, Copyable a, Consumable a) =>
  a ->
  Mut lifetime (Vector a) %1 ->
  BO lifetime (Mut lifetime (Vector a))
{-# INLINE push #-}
push value vector = Control.do
  ((), updatedVector) <-
    withPinned
      ( \pinned -> Control.do
          pinned <- growAndPush value pinned
          Control.pure ((), pinned)
      )
      vector
  Control.pure updatedVector

-- | Reduce the logical length without changing backing identity.
truncate ::
  (HasCallStack, Consumable a, lifetime >= scope) =>
  Int ->
  Mut lifetime (Vector a) %1 ->
  BO scope (Mut lifetime (Vector a))
{-# INLINE truncate #-}
truncate newSize vector = Control.do
  ((), updatedVector) <-
    withPinned
      ( \pinned ->
          case pinnedTruncate newSize pinned of
            updatedPinned ->
              Control.pure ((), updatedPinned)
      )
      vector
  Control.pure updatedVector

-- | Return a pinned logical length without touching the stable reference.
pinnedSize :: Pinned pin a %1 -> (Ur Int, Pinned pin a)
{-# INLINE pinnedSize #-}
pinnedSize (Pinned logicalSize buffer) =
  (Ur logicalSize, Pinned logicalSize buffer)

-- | Return a pinned capacity without touching the stable reference.
pinnedCapacity ::
  (U.Unbox a) =>
  Pinned pin a %1 ->
  (Ur Int, Pinned pin a)
{-# INLINE pinnedCapacity #-}
pinnedCapacity =
  Unsafe.toLinear \(Pinned logicalSize buffer) ->
    (Ur (UM.length buffer), Pinned logicalSize buffer)

-- | Copy a checked pinned cell.
pinnedCopyAt ::
  (HasCallStack, U.Unbox a, Copyable a) =>
  Int ->
  Pinned pin a %1 ->
  BO scope (Ur a, Pinned pin a)
{-# INLINE pinnedCopyAt #-}
pinnedCopyAt index pinned =
  case pinnedSize pinned of
    (Ur logicalSize, updatedPinned) ->
      if index < 0 || index >= logicalSize
        then
          error
            ( "pinnedCopyAt: index "
                <> show index
                <> " out of bounds for length "
                <> show logicalSize
            )
            updatedPinned
        else pinnedUnsafeCopyAt index updatedPinned

-- | Copy an unchecked pinned cell.
pinnedUnsafeCopyAt ::
  (U.Unbox a, Copyable a) =>
  Int ->
  Pinned pin a %1 ->
  BO scope (Ur a, Pinned pin a)
{-# INLINE pinnedUnsafeCopyAt #-}
pinnedUnsafeCopyAt =
  Unsafe.toLinear2 \index pinned@(Pinned _ buffer) ->
    unsafeSystemIOToBO do
      !value <- UM.unsafeRead buffer index
      NonLinear.pure (Ur value, pinned)

-- | Overwrite a checked pinned cell.
pinnedWrite ::
  ( HasCallStack
  , U.Unbox a
  , Copyable a
  , Consumable a
  ) =>
  Int ->
  a ->
  Pinned pin a %1 ->
  BO scope (Pinned pin a)
{-# INLINE pinnedWrite #-}
pinnedWrite index value pinned =
  case pinnedSize pinned of
    (Ur logicalSize, updatedPinned) ->
      if index < 0 || index >= logicalSize
        then
          error
            ( "pinnedWrite: index "
                <> show index
                <> " out of bounds for length "
                <> show logicalSize
            )
            updatedPinned
            value
        else pinnedUnsafeWrite index value updatedPinned

-- | Overwrite an unchecked pinned cell.
pinnedUnsafeWrite ::
  (U.Unbox a, Copyable a, Consumable a) =>
  Int ->
  a ->
  Pinned pin a %1 ->
  BO scope (Pinned pin a)
{-# INLINE pinnedUnsafeWrite #-}
pinnedUnsafeWrite =
  Unsafe.toLinear3 \index !value pinned@(Pinned _ buffer) ->
    unsafeSystemIOToBO do
      UM.unsafeWrite buffer index value
      NonLinear.pure pinned

-- | Modify a checked pinned cell.
pinnedModify ::
  ( HasCallStack
  , U.Unbox a
  , Copyable a
  , Consumable a
  ) =>
  (a -> (a, result)) ->
  Int ->
  Pinned pin a %1 ->
  BO scope (Ur result, Pinned pin a)
{-# INLINE pinnedModify #-}
pinnedModify function index pinned =
  case pinnedSize pinned of
    (Ur logicalSize, updatedPinned) ->
      if index < 0 || index >= logicalSize
        then
          error
            ( "pinnedModify: index "
                <> show index
                <> " out of bounds for length "
                <> show logicalSize
            )
            updatedPinned
            function
        else pinnedUnsafeModify function index updatedPinned

-- | Modify an unchecked pinned cell.
pinnedUnsafeModify ::
  (U.Unbox a, Copyable a, Consumable a) =>
  (a -> (a, result)) ->
  Int ->
  Pinned pin a %1 ->
  BO scope (Ur result, Pinned pin a)
{-# INLINE pinnedUnsafeModify #-}
pinnedUnsafeModify =
  Unsafe.toLinear3 \function index pinned@(Pinned _ buffer) ->
    unsafeSystemIOToBO do
      !old <- UM.unsafeRead buffer index
      case function old of
        (!new, !result) -> do
          UM.unsafeWrite buffer index new
          NonLinear.pure (Ur result, pinned)

-- Internal growth operation. It is intentionally unavailable to a caller that
-- holds a 'Pinned' view.
growAndPush ::
  (U.Unbox a, Copyable a, Consumable a) =>
  a ->
  Pinned pin a %1 ->
  BO scope (Pinned pin a)
{-# INLINE growAndPush #-}
growAndPush =
  Unsafe.toLinear2 \ !value (Pinned logicalSize buffer) ->
    unsafeSystemIOToBO do
      let !oldCapacity = UM.length buffer
      grown <-
        if logicalSize < oldCapacity
          then NonLinear.pure buffer
          else do
            let !newCapacity = max 1 (oldCapacity * 2)
            UM.unsafeGrow buffer (newCapacity - oldCapacity)
      UM.unsafeWrite grown logicalSize value
      NonLinear.pure (Pinned (logicalSize + 1) grown)

-- | Reduce a pinned logical length.
pinnedTruncate ::
  (HasCallStack, Consumable a) =>
  Int ->
  Pinned pin a %1 ->
  Pinned pin a
{-# INLINE pinnedTruncate #-}
pinnedTruncate newSize (Pinned logicalSize buffer)
  | newSize < 0 || newSize > logicalSize =
      error
        ( "pinnedTruncate: length "
            <> show newSize
            <> " out of bounds for length "
            <> show logicalSize
        )
        buffer
  | otherwise = Pinned newSize buffer

-- | Copy from a buffer pin without checking against the supplied logical size.
pinnedBufferUnsafeCopyAt ::
  (U.Unbox a, Copyable a) =>
  Int ->
  PinnedBuffer pin a %1 ->
  BO scope (Ur a, PinnedBuffer pin a)
{-# INLINE pinnedBufferUnsafeCopyAt #-}
pinnedBufferUnsafeCopyAt =
  Unsafe.toLinear2 \index pinned@(PinnedBuffer buffer) ->
    unsafeSystemIOToBO do
      !value <- UM.unsafeRead buffer index
      NonLinear.pure (Ur value, pinned)

-- | Overwrite a cell through a buffer pin.
pinnedBufferUnsafeWrite ::
  (U.Unbox a, Copyable a, Consumable a) =>
  Int ->
  a ->
  PinnedBuffer pin a %1 ->
  BO scope (PinnedBuffer pin a)
{-# INLINE pinnedBufferUnsafeWrite #-}
pinnedBufferUnsafeWrite =
  Unsafe.toLinear3 \index !value pinned@(PinnedBuffer buffer) ->
    unsafeSystemIOToBO do
      UM.unsafeWrite buffer index value
      NonLinear.pure pinned
