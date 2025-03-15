{-# LANGUAGE LinearTypes #-}

module Control.Qualified.DataFlow ((>>=), (>>)) where

import Prelude hiding ((>>), (>>=))

(>>=) :: a %1 -> (a %1 -> b) %1 -> b
a >>= b = b a

(>>) :: () %1 -> b %1 -> b
() >> b = b
