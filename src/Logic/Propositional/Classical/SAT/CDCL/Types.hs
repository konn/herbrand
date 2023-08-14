{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Logic.Propositional.Classical.SAT.CDCL.Types (
  Lit (PosL, NegL),
  litVar,
  _PosL,
  _NegL,
  litVarL,
  encodeLit,
  decodeLit,
  Index,
  Clause (..),
  CDLLState (..),
  withCDLLState,
) where

import Control.DeepSeq (NFData)
import Control.Foldl qualified as L
import Control.Lens (Lens', Prism', folded, imapAccumL, lens, prism')
import Control.Monad (guard)
import Data.Bits ((.&.), (.|.))
import Data.Foldable (fold)
import Data.Generics.Labels ()
import Data.Hashable (Hashable)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.Strict.Maybe qualified as S
import Data.Unrestricted.Linear (Ur)
import Data.Vector.Mutable.Linear qualified as LV
import Data.Vector.Unboxed qualified as U
import Data.Vector.Unboxed.Deriving (derivingUnbox)
import GHC.Generics (Generic)
import Logic.Propositional.Syntax.NormalForm.Classical.Conjunctive
import Prelude.Linear qualified as PL

-- | Up to 32-bit
newtype Lit = Lit {runLit :: Word}
  deriving (Eq, Ord)
  deriving newtype (Hashable, NFData)

{-# COMPLETE PosL, NegL :: Lit #-}

pattern PosL :: Word -> Lit
pattern PosL w <- (decodeLit -> Positive w)
  where
    PosL w = Lit (w .&. idMask)

pattern NegL :: Word -> Lit
pattern NegL w <- (decodeLit -> Negative w)
  where
    NegL w = Lit (negateMask .|. (w .&. idMask))

_PosL :: Prism' Lit Word
_PosL = prism' PosL \(Lit l) -> do
  guard $ l .&. negateMask == 0
  pure $ l .&. idMask

_NegL :: Prism' Lit Word
_NegL = prism' NegL \(Lit l) -> do
  guard $ l .&. negateMask /= 0
  pure $ l .&. idMask

litVar :: Lit -> Word
{-# INLINE litVar #-}
litVar = (.&. idMask) . runLit

litVarL :: Lens' Lit Word
litVarL = lens litVar \l v -> Lit (negateMask .&. runLit l .|. idMask .&. v)

instance Show Lit where
  showsPrec d = showsPrec d . decodeLit
  {-# INLINE showsPrec #-}

negateMask :: Word
negateMask = 0x8000000000000000

idMask :: Word
idMask = 0x7fffffffffffffff

encodeLit :: Literal Word -> Lit
encodeLit (Positive w) = Lit $ w .&. idMask
encodeLit (Negative w) = Lit $ negateMask .|. (w .&. idMask)

decodeLit :: Lit -> Literal Word
decodeLit (Lit w)
  | w .&. negateMask /= 0 = Negative $ w .&. idMask
  | otherwise = Positive $ w .&. idMask

derivingUnbox "Lit" [t|Lit -> Word|] [|runLit|] [|Lit|]

type Index = Int

data Clause = Clause
  { lits :: {-# UNPACK #-} !(U.Vector Lit)
  , watched1 :: {-# UNPACK #-} !Index
  , watched2 :: {-# UNPACK #-} !Index
  }
  deriving (Show, Eq, Ord, Generic)

data Variable = Variable
  { assignment :: !(S.Maybe Bool)
  , watchedIn :: !IntSet
  }
  deriving (Show, Eq, Ord, Generic)

data CDLLState where
  CDLLState ::
    -- | Clauses
    {-# UNPACK #-} !(LV.Vector Clause) %1 ->
    -- | Variables
    {-# UNPACK #-} !(LV.Vector Variable) %1 ->
    CDLLState

withCDLLState :: CNF Word -> (CDLLState %1 -> Ur a) %1 -> Ur a
withCDLLState (CNF cls) k =
  let (cls', vs) =
        L.fold
          ( (,)
              <$> L.handles #_CNFClause (L.premap (L.fold L.nub . map encodeLit) L.nub)
              <*> L.handles folded L.maximum
          )
          cls
      (upds, cls'') = imapAccumL toVariable IntMap.empty cls'
   in LV.fromList cls'' \clauses ->
        LV.fromList
          ( maybe
              []
              ( \maxV ->
                  [ Variable S.Nothing $ fold $ IntMap.lookup i upds
                  | i <- [0 .. fromIntegral maxV]
                  ]
              )
              vs
          )
          (k PL.. CDLLState clauses)

toVariable ::
  Int ->
  IntMap IntSet ->
  [Lit] ->
  (IntMap IntSet, Clause)
toVariable _ watches [] =
  (watches, Clause {lits = mempty, watched1 = -1, watched2 = -1})
toVariable i watches [x] =
  ( IntMap.insertWith IS.union (fromIntegral $ litVar x) (IS.singleton i) watches
  , Clause {lits = U.singleton x, watched1 = 0, watched2 = -1}
  )
toVariable i watches xs =
  ( IntMap.insertWith
      IS.union
      (fromIntegral $ litVar $ head xs)
      (IS.singleton i)
      $ IntMap.insertWith
        IS.union
        (fromIntegral $ litVar $ xs !! 1)
        (IS.singleton i)
        watches
  , Clause {lits = U.fromList xs, watched1 = 0, watched2 = 1}
  )
