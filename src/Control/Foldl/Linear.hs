{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Control.Foldl.Linear (
  Fold (..),
  fold,
  foldOver,
  mapAccumLOf,
  find,
  find_,
  alterOnce,
) where

import qualified Control.Functor.Linear as C
import qualified Control.Functor.Linear as Control
import Control.Optics.Linear
import qualified Data.Bifunctor.Linear as BiL
import Data.Functor.Linear (Traversable, mapAccumL)
import qualified Data.Functor.Linear as D
import Data.Profunctor.Kleisli.Linear
import qualified Data.Strict as S
import Data.Strict.Tuple (Pair (..))
import qualified Data.Tuple.Linear as TL
import Data.Unrestricted.Linear
import Prelude.Linear hiding (find)
import qualified Unsafe.Linear as Unsafe
import Prelude ()

data Fold a b where
  Fold :: (x %1 -> a %1 -> Pair x a) -> x %1 -> (x %1 -> b) %1 -> Fold a b

instance D.Functor (Fold a) where
  fmap f (Fold l x0 out) = Fold l x0 (f . out)
  {-# INLINE fmap #-}

instance C.Functor (Fold a) where
  fmap f (Fold l x0 out) = Fold l x0 (f . out)
  {-# INLINE fmap #-}

instance D.Applicative (Fold a) where
  pure x = Fold (\() -> (() :!:)) () (\() -> x)
  Fold stepL beginL doneL <*> Fold stepR beginR doneR =
    Fold
      ( \(l :!: r) a ->
          stepL l a & \(l :!: a) ->
            stepR r a & \(r :!: a) ->
              (l :!: r) :!: a
      )
      (beginL :!: beginR)
      (\(l :!: r) -> doneL l (doneR r))

instance C.Applicative (Fold a) where
  pure x = Fold (\() -> (() :!:)) () (\() -> x)
  Fold stepL beginL doneL <*> Fold stepR beginR doneR =
    Fold
      ( \(l :!: r) a ->
          stepL l a & \(l :!: a) ->
            stepR r a & \(r :!: a) ->
              (l :!: r) :!: a
      )
      (beginL :!: beginR)
      (\(l :!: r) -> doneL l (doneR r))

fold :: (Traversable t) => Fold a b -> t a %1 -> (b, t a)
fold (Fold f x0 out) =
  BiL.first out
    . mapAccumL (\x a -> f x a & \case (l :!: r) -> (l, r)) x0

mapAccumLOf ::
  Optic_ (Kleisli (Control.State x)) s t a b ->
  (x %1 -> a %1 -> (x, b)) ->
  x %1 ->
  s %1 ->
  (x, t)
mapAccumLOf (Optical p) f s t =
  TL.swap
    $ Control.runState
      (runKleisli (p (Kleisli (\b -> Control.state $ \i -> TL.swap $ f i b))) t)
      s

foldOver :: Traversal' s a -> Fold a b -> s %1 -> (b, s)
foldOver p (Fold f x0 out) =
  BiL.first out
    . mapAccumLOf p (\x a -> f x a & \case (l :!: r) -> (l, r)) x0

alterOnce :: (Dupable a) => (a %1 -> Maybe (b, a)) -> Fold a (Maybe b)
alterOnce p =
  Fold
    ( \case
        S.Just a -> \x -> S.Just a :!: x
        S.Nothing -> \x ->
          dup2 x & \(x, x') ->
            p x & \case
              Just (b, x) -> x' `lseq` S.Just b :!: x
              Nothing -> S.Nothing :!: x'
    )
    S.Nothing
    (Unsafe.toLinear S.toLazy)

find :: (Movable a) => (a -> Bool) -> Fold a (Maybe a)
find p =
  Fold
    ( \case
        S.Just a -> \x -> S.Just a :!: x
        S.Nothing -> \x ->
          move x & \(Ur x) ->
            if p x
              then S.Just x :!: x
              else S.Nothing :!: x
    )
    S.Nothing
    (Unsafe.toLinear S.toLazy)

find_ :: (Dupable a) => (a %1 -> (Bool, a)) -> Fold a (Maybe a)
find_ p =
  Fold
    ( \case
        S.Just a -> \x -> S.Just a :!: x
        S.Nothing -> \x ->
          p x & \case
            (True, x) -> dup2 x & \(x, x') -> S.Just x :!: x'
            (False, x) -> S.Nothing :!: x
    )
    S.Nothing
    (Unsafe.toLinear S.toLazy)
