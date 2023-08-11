{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Logic.Theory.Decision.DPLL.Abstract where

import Control.DeepSeq
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Logic.Propositional.Syntax.General (Literal (..))

-- FIXME: Use linear types for efficiency
data Context atom
  = Assumption !(HashSet (Literal atom))
  | DecidePos !(HashSet (Literal atom)) !atom !Word !(Context atom)
  | DecideNeg !(HashSet (Literal atom)) !atom !Word !(Context atom)
  deriving (Show, Eq, Ord, Generic, Foldable)
  deriving anyclass (NFData)

decLevel :: Context atom -> Word
decLevel Assumption {} = 0
decLevel (DecidePos _ _ l _) = l
decLevel (DecideNeg _ _ l _) = l

assume :: (Hashable atom) => Literal atom -> Context atom -> Context atom
assume l (Assumption set) = Assumption $ HS.insert l set
assume p (DecidePos ctx ld l rest) = DecidePos (HS.insert p ctx) ld l rest
assume p (DecideNeg ctx ld l rest) = DecideNeg (HS.insert p ctx) ld l rest

decide :: atom -> Context atom -> Context atom
decide p = DecidePos HS.empty p . (+ 1) <$> decLevel <*> id
