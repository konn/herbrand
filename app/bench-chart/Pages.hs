{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Pages (PagesOpts (..), PullRequest (..), updateReportPages) where

import Control.DeepSeq
import Control.Lens hiding ((<.>))
import Control.Monad (forM_, guard, when)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Aeson (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.Aeson as J
import qualified Data.Bifunctor as Bi
import qualified Data.Char as C
import Data.Function (on)
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable)
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust)
import Data.Ord (Down (..), comparing)
import Data.String (IsString, fromString)
import qualified Data.Text as T
import Data.Time (FormatTime, ParseTime, ZonedTime, defaultTimeLocale, formatTime, parseTimeOrError, zonedTimeToUTC)
import GHC.Generics (Generic)
import GitHash
import Lucid
import Path
import Path.IO
import System.Directory
import System.FilePath.Glob (globDir1)
import System.IO (hPutStrLn)
import UnliftIO.Environment (lookupEnv)
import UnliftIO.Exception
import UnliftIO.IO

data PagesOpts = PagesOpts
  { input :: FilePath
  , output :: FilePath
  , repo :: T.Text
  , pull :: Maybe PullRequest
  , configPath :: FilePath
  }
  deriving (Show, Eq, Ord, Generic)

data Dirs = Dirs {inputDir, commitOutDir :: Path Abs Dir}
  deriving (Show, Eq, Ord, Generic)

updateReportPages :: PagesOpts -> IO ()
updateReportPages opts@PagesOpts {..} = do
  !reps <-
    either throwString evaluateDeep
      =<< J.eitherDecodeFileStrict' @Reports configPath
  ginfo <-
    either throwIO pure
      =<< either throwIO getGitInfo
      =<< getGitRoot
      =<< getCurrentDirectory
  let newCommit =
        Commit
          { commit = fromString $ giHash ginfo
          , branch = fromString $ giBranch ginfo
          , pull
          , commitMessage = fromString $ giCommitMessage ginfo
          , commitDate = parseTimeOrError True defaultTimeLocale "%a %b %-d %H:%M:%S %Y %z" $ giCommitDate ginfo
          }
      (symlink, brs') =
        Bi.second
          ( take 10
              . sortOn (Down . view #commitDate . snd)
              . HM.toList
          )
          $ HM.alterF
            ( maybe
                (True, Just newCommit)
                ( \c ->
                    if commitDate c > commitDate newCommit
                      then (False, Just c)
                      else (True, Just newCommit)
                )
            )
            (newCommit ^. #branch)
          $ branchCommits reps
      recentComms =
        take 10
          $ sortOn (Down . view #commitDate . snd)
          $ HM.toList
          $ HM.insert (newCommit ^. #commit) newCommit
          $ commits reps
  output' <- resolveDir' output
  createDirIfMissing True output'
  inputDir <- resolveDir' input
  let commitOutDir =
        output' </> treeReportRelPath (runCommitHash $ newCommit ^. #commit)
  when symlink do
    let brDir = output' </> treeReportRelPath (runBranchName $ newCommit ^. #branch)
    thereSym <- doesDirExist brDir
    when thereSym $ removeDirLink brDir
    createDirIfMissing True $ parent brDir
    createDirLink commitOutDir brDir
  let rootIndexPath = fromAbsFile $ output' </> [relfile|index.html|]
  hPutStrLn stderr $ "Writing root index.html to: " <> rootIndexPath <> " ..."
  renderToFile rootIndexPath $ generateIndex opts brs' recentComms
  hPutStrLn stderr $ "Root index.html Written to: " <> rootIndexPath <> " ."
  let dirs = Dirs {..}
  generateCommitIndex repo dirs newCommit
  J.encodeFile
    configPath
    Reports
      { branchCommits = HM.fromList brs'
      , commits = HM.fromList recentComms
      }
  mout <- lookupEnv "GITHUB_OUTPUT"
  forM_ mout $ \stepOutPath -> do
    let (own, T.drop 1 -> rep) = T.breakOn "/" repo
    appendFile stepOutPath
      $ "url=https://"
      <> T.unpack own
      <> ".github.io/"
      <> T.unpack rep
      <> "/reports/"
      <> T.unpack (runCommitHash (newCommit ^. #commit))
      <> "/index.html"
      <> "\n"

generateCommitIndex :: T.Text -> Dirs -> Commit -> IO ()
generateCommitIndex repo Dirs {..} Commit {..} = do
  createDirIfMissing True commitOutDir
  hPutStrLn stderr $ "Globbing: " <> fromAbsDir inputDir
  reports0 <- globDir1 "*/index.html" $ fromAbsDir inputDir
  hPutStrLn stderr $ "Globbed: " <> show reports0
  !reports <-
    Map.fromList
      . catMaybes
      <$> traverse
        ( \fp0 -> runMaybeT do
            fp <- parseAbsFile fp0
            let origDir = parent fp
            p <- doesDirExist origDir
            guard p
            pure (dirname origDir, origDir)
        )
        reports0
  hPutStrLn stderr $ "Detected reports: " <> show reports
  iforM_ reports $ \k fp -> do
    hPutStrLn stderr $ "Copying dir: " <> show (k, fp)
    copyDirRecur fp (commitOutDir </> k)
  let reportIndex = fromAbsFile $ commitOutDir </> [relfile|index.html|]
  hPutStrLn stderr $ "Writing commit index to: " <> reportIndex <> " ..."
  renderToFile reportIndex
    $ mkHtmlTitled ("Benchmark Report for " <> runCommitHash commit) do
      h1_ $ "Herbrand benchmark report(s) for " <> toHtml commit
      h2_ "Metadata"
      table_ $ tbody_ do
        tr_ $ do
          th_ [scope_ "row"] "Commit"
          td_ $ gitHubTreeLink repo (runCommitHash commit) commit
        tr_ $ do
          th_ [scope_ "row"] "Date"
          td_ $ toHtml commitDate
        tr_ $ do
          th_ [scope_ "row"] "Message"
          td_ $ toHtml commitMessage
        tr_ do
          th_ [scope_ "row"] "Branch"
          td_ $ gitHubTreeLink repo (runBranchName branch) branch
        forM_ pull \_ -> do
          th_ [scope_ "row"] "Pull Req"
          td_ $ formatPull repo pull

      h2_ "Reports"
      ul_ $ iforM_ reports \k _ -> li_ do
        a_ [href_ $ T.pack $ fromRelFile $ k </> [relfile|index.html|]]
          $ toHtml (titleCase $ fromRelDir k)
  hPutStrLn stderr $ "Commit index written to: " <> reportIndex

titleCase :: FilePath -> T.Text
titleCase =
  T.unwords
    . map (_head %~ C.toUpper)
    . filter (not . T.null)
    . T.split (`elem` ("-_" :: String))
    . T.dropWhileEnd (== '/')
    . T.pack

gitHubTreeLink :: (ToHtml body) => T.Text -> T.Text -> body -> Html ()
gitHubTreeLink repo tree = a_ [href_ $ "https://github.com/" <> repo <> "/tree/" <> tree] . toHtml

mkHtmlTitled :: T.Text -> Html () -> Lucid.Html ()
mkHtmlTitled title body = doctypehtml_ do
  head_ do
    title_ $ toHtml title
    meta_ [charset_ "UTF-8"]
    meta_
      [ name_ "viewport"
      , content_ "width=device-width, initial-scale=1.0"
      ]
    link_ [rel_ "stylesheet", href_ "https://cdn.simplecss.org/simple.min.css"]
  body

treeReportRelPath :: T.Text -> Path Rel Dir
treeReportRelPath name = fromJust $ parseRelDir (T.unpack name)

linkToReportRoot :: (ToHtml body) => T.Text -> body -> Html ()
linkToReportRoot name =
  a_
    [ href_
        $ T.pack
        $ fromRelFile
        $ treeReportRelPath name
        </> [relfile|index.html|]
    ]
    . toHtml

generateIndex :: PagesOpts -> [(BranchName, Commit)] -> [(CommitHash, Commit)] -> Lucid.Html ()
generateIndex PagesOpts {repo} branches comms = mkHtmlTitled "Herbrand Benchmark Reports" do
  h1_ "Herbrand benchmark reports"

  h2_ "Recently updated branches"
  table_ do
    thead_ $ tr_ do
      th_ [scope_ "col"] "Branch"
      th_ [scope_ "col"] "Commit"
      th_ [scope_ "col"] "Date"
      th_ [scope_ "col"] "Pull"
      th_ [scope_ "col"] "Message"
    tbody_ $ forM_ branches \(bName, Commit {..}) -> tr_ do
      th_ [scope_ "row"]
        $ linkToReportRoot (runBranchName bName) bName
      td_
        $ linkToReportRoot (runBranchName bName)
        $ T.take 7
        $ runCommitHash commit
      td_ $ toHtml commitDate
      td_ $ formatPull repo pull
      td_ $ toHtml commitMessage

  h2_ "Recent commits"
  table_ do
    thead_ $ tr_ do
      th_ [scope_ "col"] "Commit"
      th_ [scope_ "col"] "Date"
      th_ [scope_ "col"] "Message"
      th_ [scope_ "col"] "Branch"
      th_ [scope_ "col"] "Pull"
    tbody_ $ forM_ comms \(_, Commit {..}) -> tr_ do
      th_ [scope_ "row"]
        $ linkToReportRoot (runCommitHash commit)
        $ T.take 7
        $ runCommitHash commit
      td_ $ toHtml commitDate
      td_ $ toHtml commitMessage
      td_ $ gitHubTreeLink repo (runBranchName branch) branch
      td_ $ formatPull repo pull

formatPull :: T.Text -> Maybe PullRequest -> Html ()
formatPull repo p = case p of
  Nothing -> "-"
  Just PullRequest {..} ->
    a_ [href_ $ "https://github.com/" <> repo <> "/pull/" <> T.pack (show pullNumber)]
      $ "#"
      <> toHtml (show pullNumber)
      <> ": "
      <> toHtml pullTitle

newtype Timestamp = Timestamp {getTimestamp :: ZonedTime}
  deriving (Show, Generic)
  deriving newtype (ToJSON, FromJSON, ParseTime, FormatTime, NFData)

instance ToHtml Timestamp where
  toHtml = toHtml . formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S %Z"
  toHtmlRaw = toHtmlRaw . formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S %Z"

instance Eq Timestamp where
  (==) = (==) `on` zonedTimeToUTC . getTimestamp

instance Ord Timestamp where
  compare = comparing $ zonedTimeToUTC . getTimestamp

newtype BranchName = BranchName {runBranchName :: T.Text}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (FromJSON, ToJSON, Hashable, IsString, FromJSONKey, ToJSONKey, NFData, ToHtml)

newtype CommitHash = CommitHash {runCommitHash :: T.Text}
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (FromJSON, ToJSON, Hashable, IsString, FromJSONKey, ToJSONKey, NFData, ToHtml)

data ReportInfo = ReportInfo {commit :: T.Text, branch :: T.Text}
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON)

data PullRequest = PullRequest
  { pullNumber :: Word
  , pullTitle :: T.Text
  , baseBranch :: BranchName
  , baseCommit :: CommitHash
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON, NFData)

data Commit = Commit
  { commit :: CommitHash
  , branch :: BranchName
  , pull :: Maybe PullRequest
  , commitMessage :: T.Text
  , commitDate :: Timestamp
  }
  deriving (Show, Generic)
  deriving anyclass (FromJSON, ToJSON, NFData)

data Reports = Reports
  { branchCommits :: HashMap BranchName Commit
  , commits :: HashMap CommitHash Commit
  }
  deriving (Show, Generic)
  deriving anyclass (FromJSON, ToJSON, NFData)
