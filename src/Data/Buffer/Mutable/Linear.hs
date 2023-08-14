{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}

module Data.Buffer.Mutable.Linear (
  Buffer (),
  alloc,
  fromList,
  fromListCapacity,
  freeze,
  capacity,
  size,
  push,
  pop,
  unsafePop,
  shrink,
  get,
  unsafeGet,
  set,
  unsafeSet,
  modify,
  unsafeModify,
) where

import Data.Array.Mutable.Linear (Array)
import qualified Data.Array.Mutable.Linear as A
import qualified Data.Bifunctor.Linear as BiL
import Data.Unrestricted.Linear (Consumable (..))
import qualified Data.Unrestricted.Linear as Ur
import qualified Data.Vector as V
import GHC.Stack (HasCallStack)
import Prelude.Linear (Ur (..), ($), (&), (.))
import Prelude hiding (($), (.))

data Buffer a where
  Buffer :: {-# UNPACK #-} !Int -> {-# UNPACK #-} !(Array a) %1 -> Buffer a

instance Consumable (Buffer a) where
  consume (Buffer _ arr) = consume arr

instance Ur.Dupable (Buffer a) where
  dup2 (Buffer l arr) =
    BiL.bimap (Buffer l) (Buffer l) $ Ur.dup2 arr

push :: (HasCallStack) => a -> Buffer a %1 -> Buffer a
push a (Buffer l arr) =
  let !l' = l + 1
   in case A.size arr of
        (Ur cap, arr') ->
          if cap >= l'
            then Buffer l' (A.set l a arr')
            else Buffer l' (A.set l a (A.resize (max 1 cap * 2) (error "uninitlised growth") arr'))

unsafePop :: Buffer a %1 -> (Ur a, Buffer a)
unsafePop (Buffer l arr) =
  A.unsafeGet (l - 1) arr & \case
    (a, arr') -> (a, Buffer (l - 1) arr')

pop :: Buffer a %1 -> (Ur (Maybe a), Buffer a)
pop (Buffer l arr)
  | l > 0 = BiL.first (Ur.lift Just) $ unsafePop (Buffer l arr)
  | otherwise = (Ur Nothing, Buffer l arr)

size :: Buffer a %1 -> (Ur Int, Buffer a)
size (Buffer i c) = (Ur i, Buffer i c)

fromList :: (HasCallStack) => [a] -> (Buffer a %1 -> Ur b) %1 -> Ur b
fromList xs k =
  A.fromList xs $ k . Buffer (Prelude.length xs)

fromListCapacity :: (HasCallStack) => Int -> [a] -> (Buffer a %1 -> Ur b) %1 -> Ur b
fromListCapacity cap xs k =
  A.fromList
    xs
    let l = Prelude.length xs
     in if cap > l
          then k . Buffer l . A.resize (max 1 cap) (error "unintialised growth")
          else k . Buffer l

capacity :: Buffer a %1 -> (Ur Int, Buffer a)
capacity (Buffer i c) =
  A.size c & \case (cap, c') -> (cap, Buffer i c')

alloc :: (HasCallStack) => Int -> (Buffer a %1 -> Ur b) %1 -> Ur b
alloc cap k =
  A.alloc
    cap
    (error "Uninitialised array element")
    (k . Buffer 0)

shrink :: (HasCallStack) => Buffer a %1 -> Buffer a
shrink (Buffer l c) = Buffer l (A.resize l (error "shrink: uninit") c)

unsafeGet :: Int -> Buffer a %1 -> (Ur a, Buffer a)
unsafeGet i (Buffer l arr) =
  A.unsafeGet i arr & \case
    (a, arr') -> (a, Buffer l arr')

get :: (HasCallStack) => Int -> Buffer a %1 -> (Ur a, Buffer a)
get i (Buffer l arr) =
  if i < l
    then unsafeGet i (Buffer l arr)
    else arr `Ur.lseq` error ("get: Out of bound " <> show (i, l))

unsafeSet :: Int -> a -> Buffer a %1 -> Buffer a
unsafeSet i a (Buffer l arr) =
  Buffer l (A.set i a arr)

set :: (HasCallStack) => Int -> a -> Buffer a %1 -> Buffer a
set i a (Buffer l arr)
  | i < l = Buffer l (A.unsafeSet i a arr)
  | otherwise = arr `Ur.lseq` error ("set: Out of bound " <> show (i, l))

freeze :: Buffer a %1 -> Ur (V.Vector a)
freeze (Buffer l c) = Ur.lift (V.unsafeTake l) $ A.freeze c

unsafeModify :: Int -> (a -> a) -> Buffer a %1 -> Buffer a
unsafeModify i f buf =
  case unsafeGet i buf of
    (Ur a, buf') -> unsafeSet i (f a) buf'

modify :: (HasCallStack) => Int -> (a -> a) -> Buffer a %1 -> Buffer a
modify i f (Buffer l arr)
  | i < l = unsafeModify i f $ Buffer l arr
  | otherwise = arr `Ur.lseq` error ("modify: out of bound" <> show (i, l))
