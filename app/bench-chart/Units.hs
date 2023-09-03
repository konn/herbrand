{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}

module Units (SIPrefix (..), showPrefix, adjustSITo, detectSIPrefix) where

import Data.Semigroup
import GHC.Generics (Generic)
import Math.NumberTheory.Logarithms (integerLog10')

data SIPrefix = Pico | Nano | Micro | Mili | Unit | Kilo | Mega | Giga
  deriving (Show, Eq, Ord, Generic, Enum, Bounded)
  deriving (Semigroup) via Max SIPrefix

showPrefix :: SIPrefix -> String
showPrefix Pico = "p"
showPrefix Nano = "n"
showPrefix Micro = "u"
showPrefix Mili = "m"
showPrefix Unit = ""
showPrefix Kilo = "k"
showPrefix Mega = "M"
showPrefix Giga = "G"

adjustSITo :: SIPrefix -> Integer -> SIPrefix -> Double
adjustSITo _ 0 _ = 0.0
adjustSITo std i new =
  fromInteger i * 10 ^^ (3 * (fromEnum std - fromEnum new))

detectSIPrefix :: SIPrefix -> Integer -> Maybe SIPrefix
detectSIPrefix _ 0 = Nothing
detectSIPrefix orig i =
  let ub = fromEnum (maxBound :: SIPrefix)
      lvl = integerLog10' (abs i) `quot` 3 + fromEnum orig
   in if lvl > ub
        then Just Giga
        else Just $ toEnum lvl
