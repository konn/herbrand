{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Applicative ((<**>))
import Control.Lens ((^.))
import Control.Monad
import qualified Data.Aeson as A
import qualified Data.ByteString.Builder as BB
import Data.Function (fix)
import GHC.Generics (Generic)
import Herbrand.Test
import Logic.Propositional.Classical.SAT.Format.DIMACS
import qualified Options.Applicative as Opt
import System.Directory
import System.FilePath
import Test.Falsify.Interactive (sample)

data FormulaSize = FormulaSize
  { variables :: {-# UNPACK #-} !Word
  , size :: {-# UNPACK #-} !Word
  }
  deriving (Show, Eq, Ord, Generic)

data Options = Options
  { output :: !FilePath
  , name :: !(Maybe String)
  , formSize :: !FormulaSize
  , count :: !Word
  }
  deriving (Show, Eq, Ord, Generic)

optsP :: Opt.ParserInfo Options
optsP = Opt.info (p <**> Opt.helper) $ Opt.progDesc "Generate formula(e) of specified size in (extended) DIMACS SAT format"
  where
    p = do
      output <-
        Opt.strOption
          $ Opt.long "output"
          <> Opt.short 'o'
          <> Opt.metavar "OUT_DIR"
          <> Opt.help "Output dir"
      name <-
        Opt.optional
          $ Opt.strOption
          $ Opt.long "name"
          <> Opt.short 'N'
          <> Opt.metavar "NAME"
          <> Opt.showDefault
          <> Opt.help "Base name of output value. Each formula will be saved as `<OUT_DIR>/<NAME>-%i.sat`, where `%i` is 0-origin number. If omitted, saved as `<OUT_DIR>/%i.sat`."
      count <-
        Opt.option Opt.auto
          $ Opt.long "count"
          <> Opt.short 'n'
          <> Opt.value 1
          <> Opt.metavar "NUM"
          <> Opt.showDefault
          <> Opt.help "Number of examples to generate"
      formSize <- sizeP
      pure Options {..}
    sizeP = do
      variables <-
        Opt.option Opt.auto
          $ Opt.metavar "NUM_VARS"
          <> Opt.long "vars"
          <> Opt.short 'v'
          <> Opt.help "Number of variables (Arity)"
      size <-
        Opt.option Opt.auto
          $ Opt.metavar "SIZE"
          <> Opt.long "size"
          <> Opt.short 's'
          <> Opt.help "Size of a formula, i.e. # of connectives and atoms"
      pure FormulaSize {..}

main :: IO ()
main = do
  Options {..} <- Opt.execParser optsP
  let FormulaSize {..} = formSize
  createDirectoryIfMissing True output
  ($ 0) $ fix $ \ !self !i -> unless (i > count) $ do
    fml <- sample $ fullFormula variables size
    let dimacs = toDIMACS fml
        stat = A.decode @SATStatistics $ dimacs ^. commentL
        dest = output </> maybe "" (<> "-") name <> show i <> ".sat"
    BB.writeFile dest $ formatDIMACS dimacs
    putStrLn $ "Written: " <> dest <> " (" <> show stat <> ")"
    self $ i + 1
  pure ()
