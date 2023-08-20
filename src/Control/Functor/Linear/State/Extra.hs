{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}

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
) where

import Control.Functor.Linear
import qualified Control.Optics.Linear as Optics
import qualified Control.Optics.Linear.Lens as Optic
import Data.Functor.Compose
import Data.Kind
import Data.Profunctor.Kleisli.Linear
import GHC.Exts (Multiplicity (..))
import Prelude.Linear

zoom ::
  (Functor m) =>
  Optics.Optic_ (Kleisli (Compose ((,) t) (FUN 'One t))) s s t t ->
  StateT t m a ->
  StateT s m a
zoom l (StateT f) = StateT \s0 ->
  Optic.reifyLens l s0 & \(t, back) ->
    fmap back <$> f t
