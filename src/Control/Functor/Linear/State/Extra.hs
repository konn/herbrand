{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Functor.Linear.State.Extra (
  StateT (..),
  State,
  state,
  runState,
  evalState,
  execState,
  mapState,
  withState,
  runStateT,
  evalStateT,
  execStateT,
  mapStateT,
  withStateT,
  get,
  put,
  modify,
  gets,
  zoom,
  (%=),
  (.=),
  pure,
  (>>=),
  return,
  (>>),
  (<*>),
  (<*),
  (<$>),
  (<$),
  fail,
  uses,
  use,
) where

import Control.Functor.Linear
import qualified Control.Optics.Linear as Optics
import qualified Control.Optics.Linear.Lens as Optic
import Data.Functor.Compose
import qualified Data.Functor.Linear as D
import Data.Kind
import Data.Profunctor.Kleisli.Linear
import GHC.Exts (Multiplicity (..))
import Prelude.Linear

zoom ::
  (Functor m) =>
  Optics.Optic_ (Kleisli (Compose ((,) t) (FUN 'One t))) s s t t ->
  StateT t m a %1 ->
  StateT s m a
{-# INLINE zoom #-}
zoom l (StateT f) = StateT \ !s0 ->
  Optic.reifyLens l s0 & \(!t, !back) ->
    fmap back <$> f t

infix 4 %=, .=

(%=) ::
  (Applicative m) =>
  Optics.Optic_ (Kleisli (Compose ((,) t) (FUN 'One t'))) s s t t' ->
  (t %1 -> t') %1 ->
  StateT s m ()
{-# INLINE (%=) #-}
l %= f = StateT \s0 ->
  Optic.reifyLens l s0 & \(!t, !back) ->
    pure ((), back $! f t)

(.=) ::
  (Applicative m, Consumable t) =>
  Optics.Optic_ (Kleisli (Compose ((,) t) (FUN 'One t'))) s s t t' ->
  t' %1 ->
  StateT s m ()
{-# INLINE (.=) #-}
l .= a = StateT \s0 ->
  Optic.reifyLens l s0 & \(!t, !back) ->
    t `lseq` pure ((), back a)

uses ::
  (Applicative m) =>
  Optics.Optic_ (Kleisli (Compose ((,) t) (FUN 'One t))) s s t t ->
  (t %1 -> (a, t)) %1 ->
  StateT s m a
{-# INLINE uses #-}
uses l f = zoom l (state f)

use ::
  (Applicative m, Dupable a) =>
  Optics.Optic_ (Kleisli (Compose ((,) a) (FUN 'One a))) s s a a ->
  StateT s m a
{-# INLINE use #-}
use l = uses l dup2

instance D.Functor (FUN 'One t) where
  fmap = (.)
  {-# INLINE fmap #-}

instance Functor (FUN 'One t) where
  fmap = (.)
  {-# INLINE fmap #-}
