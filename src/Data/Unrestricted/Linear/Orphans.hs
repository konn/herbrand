{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Unrestricted.Linear.Orphans () where

import qualified Control.Functor.Linear as C
import Data.Bifunctor.Linear
import qualified Data.Functor.Linear as D
import Data.Strict.Tuple
import Data.Unrestricted.Linear
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Generics.Linear
import Generics.Linear.TH
import Prelude.Linear
import qualified Unsafe.Linear as Unsafe
import Prelude hiding ((.))
import qualified Prelude as P

deriveGeneric ''Pair
deriveGeneric1 ''Pair

deriving via
  Generically (Pair a b)
  instance
    (Consumable a, Consumable b) => Consumable (Pair a b)

deriving via
  Generically1 (Pair a)
  instance
    D.Functor (Pair a)

deriving via
  Generically1 (Pair a)
  instance
    (Prelude.Linear.Monoid a) => D.Applicative (Pair a)

deriving via
  Generically1 (Pair a)
  instance
    C.Functor (Pair a)

instance Bifunctor Pair where
  bimap f g (l :!: r) = f l :!: g r

deriving via
  Generically (Pair a b)
  instance
    (Dupable a, Dupable b) => Dupable (Pair a b)

deriving via
  Generically (Pair a b)
  instance
    (Movable a, Movable b) => Movable (Pair a b)

instance (Consumable a, U.Unbox a) => Consumable (U.Vector a) where
  consume = consume . Unsafe.toLinear U.toList
  {-# INLINE consume #-}

instance (Dupable a, U.Unbox a) => Dupable (U.Vector a) where
  dup2 = Unsafe.toLinear (U.unzip P.. U.map (Unsafe.toLinear dup2))
  {-# INLINE dup2 #-}

instance (Dupable a) => Dupable (V.Vector a) where
  dup2 = Unsafe.toLinear (V.unzip P.. V.map (Unsafe.toLinear dup2))
  {-# INLINE dup2 #-}

instance (Movable a, U.Unbox a) => Movable (U.Vector a) where
  move = Unsafe.toLinear (U.mapM (Unsafe.toLinear move))
  {-# INLINE move #-}

instance (Movable a) => Movable (V.Vector a) where
  move = Unsafe.toLinear (V.mapM (Unsafe.toLinear move))
  {-# INLINE move #-}
