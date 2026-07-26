{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Data.Monoid.Linear.Orphans () where

import Data.Unrestricted.Linear qualified as Ur

instance (Semigroup a) => Semigroup (Ur.Ur a) where
  (<>) = liftA2 (<>)

instance (Monoid a) => Monoid (Ur.Ur a) where
  mempty = Ur.Ur mempty
