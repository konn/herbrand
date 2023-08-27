{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Debug.Trace.Lienar.Extra (traceStack, traceStackM) where

import Control.Functor.Linear qualified as PL
import Debug.Trace.Linear qualified as NDTL
import GHC.Stack
import Prelude.Linear qualified as PL
import Prelude
import Prelude qualified as P

traceStackM :: (HasCallStack, PL.Applicative m) => String %1 -> m ()
traceStackM msg = traceStack msg (PL.pure ())

traceStack :: (HasCallStack) => String %1 -> a %1 -> a
traceStack msg =
  let theStack = getCallStack callStack
      (site, loc) = P.head theStack
      caller = case getCallStack callStack of
        (_ : (c, _) : _) -> Just c
        _ -> Nothing
      locStr =
        site
          <> ", "
          <> srcLocFile loc
          <> ":"
          <> show (srcLocStartLine loc)
          <> ":"
          <> show (srcLocStartCol loc)
          <> "-"
          <> show (srcLocEndLine loc)
          <> ":"
          <> show (srcLocEndCol loc)
          <> P.maybe "" ("; from " <>) caller
   in NDTL.trace (msg PL.<> "\n\t\ESC[2m@" <> locStr <> "\ESC[0m")
