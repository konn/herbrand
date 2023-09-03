{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}

module Units (SIPrefix (..), showPrefix, adjustSITo, detectSIPrefix, Radix (..)) where

import Data.Semigroup
import GHC.Generics (Generic)
import Math.NumberTheory.Logarithms (integerLog10', integerLog2')

data Radix = Decimal | Binary
  deriving (Show, Eq, Ord, Generic, Enum, Bounded)

data SIPrefix = Pico | Nano | Micro | Mili | Unit | Kilo | Mega | Giga
  deriving (Show, Eq, Ord, Generic, Enum, Bounded)
  deriving (Semigroup) via Max SIPrefix

showPrefix :: Radix -> SIPrefix -> String
showPrefix _ Pico = "p"
showPrefix _ Nano = "n"
showPrefix _ Micro = "u"
showPrefix _ Mili = "m"
showPrefix _ Unit = ""
showPrefix Decimal Kilo = "k"
showPrefix Binary Kilo = "Ki"
showPrefix Decimal Mega = "M"
showPrefix Binary Mega = "Mi"
showPrefix Decimal Giga = "G"
showPrefix Binary Giga = "Gi"

adjustSITo :: Radix -> SIPrefix -> Integer -> SIPrefix -> Double
adjustSITo _ _ 0 _ = 0.0
adjustSITo Decimal std i new =
  fromInteger i * 10 ^^ (3 * (fromEnum std - fromEnum new))
adjustSITo Binary std i new =
  fromInteger i * 2.0 ^^ (10 * (fromEnum std - fromEnum new))

detectSIPrefix :: Radix -> SIPrefix -> Integer -> Maybe SIPrefix
detectSIPrefix _ _ 0 = Nothing
detectSIPrefix Decimal orig i =
  let ub = fromEnum (maxBound :: SIPrefix)
      lvl = integerLog10' (abs i) `quot` 3 + fromEnum orig
   in if lvl > ub
        then Just Giga
        else Just $ toEnum lvl
detectSIPrefix Binary orig i =
  let ub = fromEnum (maxBound :: SIPrefix)
      lvl = integerLog2' (abs i) `quot` 10 + fromEnum orig
   in if lvl > ub
        then Just Giga
        else Just $ toEnum lvl
