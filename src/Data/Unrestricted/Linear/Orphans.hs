{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Unrestricted.Linear.Orphans () where

import Data.Strict.Tuple
import Generics.Linear
import Generics.Linear.TH
import Prelude.Linear

deriveGeneric ''Pair

deriving via
  Generically (Pair a b)
  instance
    (Consumable a, Consumable b) => Consumable (Pair a b)

deriving via
  Generically (Pair a b)
  instance
    (Dupable a, Dupable b) => Dupable (Pair a b)

deriving via
  Generically (Pair a b)
  instance
    (Movable a, Movable b) => Movable (Pair a b)
