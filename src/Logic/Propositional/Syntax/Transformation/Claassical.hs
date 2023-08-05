{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Logic.Propositional.Syntax.Transformation.Claassical (
  deMorgan,
  DeMorgan,
  dne,
  eliminateImpl,
  NoImpl,
) where

import Control.Lens (view)
import Data.Function ((&))
import Data.Functor.Foldable (Recursive (para), cata)
import GHC.Generics (Generic)
import Logic.Propositional.Syntax.General

data DeMorgan x

type instance XBot (DeMorgan x) = XBot x

type instance XTop (DeMorgan x) = XTop x

type instance XNot (DeMorgan x) = NoExtCon

type instance XImpl (DeMorgan x) = NoExtCon

data Polarity = P | N
  deriving (Show, Eq, Ord, Generic)

posNeg :: p -> p -> Polarity -> p
posNeg p n = \case
  P -> p
  N -> n

flipPos :: Polarity -> Polarity
flipPos = \case
  P -> N
  N -> P

-- | Applies de Morgan laws to eliminate negation except for literals
deMorgan :: (XTop x ~ XBot x) => Formula x a -> Formula (DeMorgan x) (Literal a)
deMorgan =
  (P &) . cata \case
    TopF x -> posNeg (Top x) (Bot x)
    BotF x -> posNeg (Bot x) (Top x)
    AtomF f -> posNeg (Atom $ Positive f) (Atom $ Negative f)
    NotF _ k -> k . flipPos
    l ::/\ r -> \case
      P -> l P :/\ r P
      N -> l N :\/ l N
    l ::\/ r -> \case
      P -> l P :\/ r P
      N -> l N :/\ l N
    ImplF _ l r -> \case
      P -> l N :\/ r P
      N -> l P :/\ r N

-- | Double-negation elimination
dne :: Formula x a -> Maybe (Formula x a)
dne = para \case
  NotF _ (_, Just (Not _ a)) -> Just a
  NotF _ (Not _ a, _) -> Just a
  f -> view _Formula <$> traverse snd f

data NoImpl x

type instance XBot (NoImpl x) = XBot x

type instance XTop (NoImpl x) = XTop x

type instance XNot (NoImpl x) = NoExtField

type instance XImpl (NoImpl x) = NoExtCon

{-
>>> eliminateImpl (Atom "a" :==> Atom "b")
Just (Not "a" \/ "b")

>>> eliminateImpl (Not ((Atom "z" :==> Atom "a" ):==> (Atom "b" :==> Atom "c")))
Just (Not (Not (Not "z" \/ "a") \/ Not "b" \/ "c"))
-}
eliminateImpl :: Formula x a -> Formula (NoImpl x) a
eliminateImpl = cata \case
  AtomF a -> Atom a
  TopF x -> Top x
  BotF x -> Bot x
  NotF _ r -> Not NoExtField r
  ImplF _ l r ->
    Not NoExtField l :\/ r
  l ::/\ r -> l :/\ r
  l ::\/ r -> l :\/ r
