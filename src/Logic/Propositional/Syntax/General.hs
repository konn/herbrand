{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | The most general syntax of (classical and intuitionistic) propositional logic
module Logic.Propositional.Syntax.General (
  Formula (..),
  Full,
  full,
  _Formula,
  _Formula',
  NoExtField (..),
  NoExtCon,
  noExtCon,
  XBot,
  XTop,
  XNot,
  XImpl,

  -- ** Queries
  disjunctives,
  conjunctives,

  -- * Smart contructors
  neg,
  (==>),
  (/\),
  (\/),
  (⊥),
  (⊤),

  -- ** Prisms
  (.⊥),
  _Bot,
  (.⊤),
  _Top,
  _T,
  _Atom,
  (.==>),
  _Impl,
  (./\),
  _And,
  (.\/),
  _Or,

  -- * Recusion functors

  -- | Underlying representation of 'Formula', to be used for recursion schemes.
  FormulaF (.., (::==>)),

  -- ** Prisms
  (.:⊥),
  _Bot',
  (.:⊤),
  _Top',
  _T',
  _Atom',
  (.==>$),
  _Impl',
  (./\$),
  _And',
  (.\/$),
  _Or',

  -- * Literals
  Literal (..),
  negLit,
  idempLit,
  toLit,
  size,
  compressVariables,
  VarStatistics (..),
  height,
) where

import Control.DeepSeq (NFData)
import Control.Lens
import Control.Monad.Trans.State.Strict (gets, runState, state)
import Data.Bifunctor.TH
import Data.DList qualified as DL
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Functor.Foldable qualified as R
import Data.Functor.Foldable.TH
import Data.Functor.Linear qualified as Lin
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable)
import Data.Strict.Tuple (Pair (..))
import Data.Strict.Tuple qualified as S
import Data.String (IsString (..))
import Data.Unrestricted.Linear qualified as L
import GHC.Generics (Generic, Generic1)
import Generics.Linear qualified as L
import Generics.Linear.TH qualified as L

data NoExtField = NoExtField
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

data NoExtCon
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

noExtCon :: NoExtCon -> a
noExtCon = \case {}

type family XTop x

type family XBot x

type family XNot x

type family XImpl x

data Full

type instance XTop Full = NoExtField

type instance XBot Full = NoExtField

type instance XNot Full = NoExtField

type instance XImpl Full = NoExtField

{- |
Propositional formula with proposition variable @a@

See also: 'FormulaF' for use with recursion schemes
-}
data Formula x a
  = Top !(XTop x)
  | Bot !(XBot x)
  | Atom !a
  | Not !(XNot x) !(Formula x a)
  | Impl !(XImpl x) !(Formula x a) !(Formula x a)
  | !(Formula x a) :/\ !(Formula x a)
  | !(Formula x a) :\/ !(Formula x a)
  deriving (Generic, Generic1, Foldable, Functor, Traversable)

deriving instance
  ( Eq (XTop x)
  , Eq (XBot x)
  , Eq (XNot x)
  , Eq (XImpl x)
  , Eq a
  ) =>
  Eq (Formula x a)

deriving instance
  ( Ord (XTop x)
  , Ord (XBot x)
  , Ord (XNot x)
  , Ord (XImpl x)
  , Ord a
  ) =>
  Ord (Formula x a)

deriving anyclass instance
  ( Hashable (XTop x)
  , Hashable (XBot x)
  , Hashable (XNot x)
  , Hashable (XImpl x)
  , Hashable a
  ) =>
  Hashable (Formula x a)

deriving anyclass instance
  ( NFData (XTop x)
  , NFData (XBot x)
  , NFData (XNot x)
  , NFData (XImpl x)
  , NFData a
  ) =>
  NFData (Formula x a)

type role Formula nominal representational

infixl 3 :/\

infixl 2 :\/

makeBaseFunctor ''Formula

type role FormulaF nominal representational representational

deriving instance Generic (FormulaF x e t)

deriving instance Generic1 (FormulaF x e)

deriving instance
  ( Eq (XTop x)
  , Eq (XBot x)
  , Eq (XNot x)
  , Eq (XImpl x)
  , Eq a
  , Eq fml
  ) =>
  Eq (FormulaF x a fml)

deriving instance
  ( Ord (XTop x)
  , Ord (XBot x)
  , Ord (XNot x)
  , Ord (XImpl x)
  , Ord a
  , Ord fml
  ) =>
  Ord (FormulaF x a fml)

deriving anyclass instance
  ( Hashable (XTop x)
  , Hashable (XBot x)
  , Hashable (XNot x)
  , Hashable (XImpl x)
  , Hashable a
  , Hashable fml
  ) =>
  Hashable (FormulaF x a fml)

deriving anyclass instance
  ( NFData (XTop x)
  , NFData (XBot x)
  , NFData (XNot x)
  , NFData (XImpl x)
  , NFData a
  , NFData fml
  ) =>
  NFData (FormulaF x a fml)

pattern (::==>) :: (XImpl x ~ NoExtField) => () => t -> t -> FormulaF x a t
pattern l ::==> r <- ImplF _ l r
  where
    l ::==> r = ImplF NoExtField l r

infixr 0 ::==>

infixl 2 :\/$

infixl 3 :/\$

instance (Show a, Show t) => Show (FormulaF x a t) where
  showsPrec = showsPrec1

instance (Show a) => Show1 (FormulaF x a) where
  liftShowsPrec _ _ _ TopF {} = showString "⊤"
  liftShowsPrec _ _ _ BotF {} = showString "⊥"
  liftShowsPrec _ _ d (AtomF a) = showsPrec d a
  liftShowsPrec showsF _ d (NotF _ f) =
    showParen (d > 10)
      $ showString "Not "
      . showsF 11 f
  liftShowsPrec showsF _ d (ImplF _ l r) =
    showParen (d > 0)
      $ showsF 1 l
      . showString " ==> "
      . showsF 0 r
  liftShowsPrec showsF _ d (l :\/$ r) =
    showParen (d > 2)
      $ showsF 2 l
      . showString " \\/ "
      . showsF 2 r
  liftShowsPrec showsF _ d (l :/\$ r) =
    showParen (d > 3)
      $ showsF 3 l
      . showString " /\\ "
      . showsF 3 r

deriveBifunctor ''FormulaF
deriveBifoldable ''FormulaF
deriveBitraversable ''FormulaF

instance (Show a) => Show (Formula x a) where
  showsPrec d = showsPrec1 d . project

_Formula :: Iso (FormulaF x a (Formula x a)) (FormulaF x b (Formula x b)) (Formula x a) (Formula x b)
_Formula = iso embed project

_Formula' :: Iso' (FormulaF x a (Formula x a)) (Formula x a)
_Formula' = iso embed project

(⊥) :: (XBot x ~ NoExtField) => Formula x a
(⊥) = Bot NoExtField

(⊤) :: (XTop x ~ NoExtField) => Formula x a
(⊤) = Top NoExtField

infixr 0 :==>, ==>

pattern (:==>) :: (XImpl x ~ NoExtField) => () => Formula x a -> Formula x a -> Formula x a
pattern l :==> r = Impl NoExtField l r

neg :: (XNot x ~ NoExtField) => Formula x a -> Formula x a
neg = Not NoExtField

(==>) :: (XImpl x ~ NoExtField) => Formula x a -> Formula x a -> Formula x a
l ==> r = l :==> r

infixl 3 /\

(/\) :: Formula x a -> Formula x a -> Formula x a
l /\ r = l :/\ r

infixl 2 \/

(\/) :: Formula x a -> Formula x a -> Formula x a
l \/ r = l :\/ r

_And, (./\) :: Prism' (Formula x a) (Formula x a, Formula x a)
(./\) = prism' (uncurry (/\)) \case
  a :/\ b -> Just (a, b)
  _ -> Nothing
_And = (./\)

_Or, (.\/) :: Prism' (Formula x a) (Formula x a, Formula x a)
(.\/) = prism' (uncurry (\/)) \case
  a :\/ b -> Just (a, b)
  _ -> Nothing
_Or = (.\/)

_Impl :: Prism' (Formula x a) (XImpl x, Formula x a, Formula x a)
_Impl = prism' (\(a, b, c) -> Impl a b c) \case
  Impl x a b -> Just (x, a, b)
  _ -> Nothing

(.==>) :: (XImpl x ~ NoExtField) => Prism' (Formula x a) (Formula x a, Formula x a)
(.==>) = prism' (uncurry $ Impl NoExtField) \case
  Impl _ a b -> Just (a, b)
  _ -> Nothing

(.⊥), _Bot :: Prism' (Formula x a) (XBot x)
_Bot = prism' Bot \case Bot x -> Just x; _ -> Nothing
(.⊥) = _Bot

(.⊤), _T, _Top :: Prism' (Formula x a) (XTop x)
_Top = prism' Top \case Top x -> Just x; _ -> Nothing
_T = _Top
(.⊤) = _Top

_Atom :: Prism' (Formula x a) a
_Atom = prism' Atom \case
  Atom a -> Just a
  _ -> Nothing

_And', (./\$) :: Prism' (FormulaF x a t) (t, t)
(./\$) = prism' (uncurry (:/\$)) \case
  a :/\$ b -> Just (a, b)
  _ -> Nothing
_And' = (./\$)

_Or', (.\/$) :: Prism' (FormulaF x a t) (t, t)
(.\/$) = prism' (uncurry (:\/$)) \case
  a :\/$ b -> Just (a, b)
  _ -> Nothing
_Or' = (.\/$)

(.==>$) :: (XImpl x ~ NoExtField) => Prism' (FormulaF x a t) (t, t)
(.==>$) = prism' (uncurry $ ImplF NoExtField) \case
  a ::==> b -> Just (a, b)
  _ -> Nothing

_Impl' :: Prism' (FormulaF x a t) (XImpl x, t, t)
_Impl' = prism' (\(x, a, b) -> ImplF x a b) \case
  ImplF x a b -> Just (x, a, b)
  _ -> Nothing

(.:⊥), _Bot' :: Prism' (FormulaF x a t) (XBot x)
_Bot' = prism' BotF \case BotF x -> Just x; _ -> Nothing
(.:⊥) = _Bot'

(.:⊤), _T', _Top' :: Prism' (FormulaF x a t) (XTop x)
_Top' = prism' TopF \case TopF x -> Just x; _ -> Nothing
_T' = prism' TopF \case TopF x -> Just x; _ -> Nothing
(.:⊤) = _Top'

_Atom' :: Prism' (Formula x a) a
_Atom' = prism' Atom \case
  Atom a -> Just a
  _ -> Nothing

instance Plated (Formula x a) where
  plate _ atm@Atom {} = pure atm
  plate _ b@Bot {} = pure b
  plate _ t@Top {} = pure t
  plate f (Not x l) = Not x <$> f l
  plate f (Impl x l r) = Impl x <$> f l <*> f r
  plate f (l :/\ r) = (:/\) <$> f l <*> f r
  plate f (l :\/ r) = (:\/) <$> f l <*> f r

{- |
Decompose a formula into a disjunction of terms with the outermost connectives
are not a disjunction.
-}
disjunctives :: Formula x a -> [Formula x a]
disjunctives =
  DL.toList . R.para \case
    (_, l) :\/$ (_, r) -> l <> r
    f -> DL.singleton $ (fst <$> f) ^. _Formula

{- |
Decompose a formula into a disjunction of terms with the outermost connectives
are not a disjunction.
-}
conjunctives :: Formula x a -> [Formula x a]
conjunctives =
  DL.toList . R.para \case
    (_, l) :/\$ (_, r) -> l <> r
    f -> DL.singleton $ (fst <$> f) ^. _Formula

-- | A literal is mere a atomic formula or its negation.
data Literal a = Positive !a | Negative !a
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

idempLit :: Literal (Literal a) -> Literal a
idempLit (Positive a) = a
idempLit (Negative a) = negLit a

instance (a ~ String) => IsString (Literal a) where
  fromString = Positive

negLit :: Literal a -> Literal a
{-# INLINE [1] negLit #-}

{-# RULES
"negLit/involutive" forall x.
  negLit (negLit x) =
    x
  #-}

negLit = \case
  Positive v -> Negative v
  Negative v -> Positive v

full :: Formula e v -> Formula Full v
full = cata \case
  AtomF a -> Atom a
  BotF _ -> (⊥)
  TopF _ -> (⊤)
  NotF _ l -> Not NoExtField l
  l :/\$ r -> l :/\ r
  l :\/$ r -> l :\/ r
  ImplF _ l r -> l :==> r

toLit :: Formula e v -> Literal (Formula e v)
toLit (Not _ (Not _ a)) = toLit a
toLit (Not _ a) = Negative a
toLit f = Positive f

size :: Formula e v -> Word
size = cata \case
  AtomF {} -> 1
  BotF {} -> 1
  TopF {} -> 1
  NotF _ l -> l + 1
  ImplF _ l r -> l + 1 + r
  l :/\$ r -> l + 1 + r
  l :\/$ r -> l + 1 + r

height :: Formula e v -> Word
height = cata \case
  AtomF {} -> 0
  BotF {} -> 0
  TopF {} -> 0
  NotF _ l -> l + 1
  ImplF _ l r -> max l r + 1
  l :/\$ r -> max l r + 1
  l :\/$ r -> max l r + 1

newtype VarStatistics = VarStatistics {maxVar :: Word}
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, Hashable)

-- | Compresses variable into 1-origin natural numbers
compressVariables :: (Traversable t, Hashable v) => t v -> (t Word, VarStatistics)
compressVariables =
  fmap (VarStatistics . S.fst) . flip runState (0 :!: mempty) . traverse \v ->
    gets (HM.lookup v . S.snd) >>= \case
      Nothing -> state $ \(((+ 1) -> !i) :!: e) ->
        (i, i :!: HM.insert v i e)
      Just i -> pure i

L.deriveGenericAnd1 ''Literal

deriving via L.Generically1 Literal instance Lin.Functor Literal

deriving via
  L.Generically (Literal a)
  instance
    (L.Consumable a) => L.Consumable (Literal a)

deriving via
  L.Generically (Literal a)
  instance
    (L.Dupable a) => L.Dupable (Literal a)

deriving via
  L.Generically (Literal a)
  instance
    (L.Movable a) => L.Movable (Literal a)

instance Lin.Traversable Literal where
  traverse = Lin.genericTraverse
