{-# LANGUAGE TemplateHaskell #-}
module Rll.ScSpecUtil
  ( txt
  , prepare
  , parseFile
  , parseFile'
  , clearTestData
  , STestConfig(..)
  ) where

import QuoteTxt

import qualified Rll.Parser as RP
import Rll.TypeCheck
import Rll.TypeError (prettyPrintError)
import Rll.TcMonad
import Rll.Spec
import Rll.SpecIR
import Rll.Context
import Rll.Ast

import Data.IORef (newIORef, modifyIORef, readIORef)
import Control.Monad (when)
import System.FilePath (takeDirectory, (</>))
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Data.ByteString.Lazy qualified as BL
import Data.HashMap.Strict qualified as HM
import Data.Map qualified as M
import Data.Text qualified as T
import Text.Megaparsec qualified as MP
import Test.Hspec hiding (Spec)
import Data.Aeson (eitherDecodeFileStrict', encode, encodeFile)
import Prettyprinter.Render.Text (putDoc)
import Prettyprinter

emptyCEnv :: ClosureEnv
emptyCEnv = ClosureEnv HM.empty

-- | Are we logging the output for manual inspection or actually running the test.
data STestConfig = Log | Test | LogJSON | UpdateJSON

parseFile' :: Text -> IO (Maybe ([(MVar, SpecDecl)], HM.HashMap MVar SpecDecl))
parseFile' txt = case MP.parse RP.fileDecls "test.rll" txt of
  Left err -> exFail $ MP.errorBundlePretty err
  Right decls ->
    case runTc emptyCtx $ typeCheckFile decls of
      Left err -> exFail $ T.unpack $ prettyPrintError txt err
      Right (coreFns, ctx) ->
        case specModule ctx.dataTypes coreFns of
          Left err -> exFail $ "Specialization error: " <> show err
          Right declInfo -> pure $ Just declInfo
  where
  exFail msg = do
    expectationFailure msg
    pure Nothing

parseFile :: Text -> IO (Maybe (HM.HashMap MVar SpecDecl))
parseFile txt = fmap snd <$> parseFile' txt

hasTypeVariables :: HM.HashMap MVar SpecDecl -> Bool
hasTypeVariables = any checkDecl where
  checkDecl decl = case decl of
    SpecFun (ClosureEnv cenv) _ args ir -> any (any checkTy) cenv
      || any (\(_,ty,_) -> checkTy ty) args || checkIR ir
    SpecDataType dt -> case dt of
      SpecEnum m -> any (any checkTy) m
      SpecStruct _ ls -> any checkTy ls
      SpecBuiltIn _ -> False
  checkIR SpecIR{ty, specf} = checkTy ty || any checkIR specf
  checkTy Ty{tyf} = case tyf of
    TyVar _ -> True
    _ -> any checkTy tyf

testDataFilePath :: FilePath
testDataFilePath = takeDirectory locFile </> "spec-tests.json"
  where locFile = $currentFilePath

clearTestData :: IO ()
clearTestData = TIO.writeFile testDataFilePath "{}"

prepare :: HasCallStack => Maybe STestConfig -> IO (STestConfig -> Text -> Text -> Expectation, IO ())
prepare mbGlobalConfig = do
  testDataRaw <- eitherDecodeFileStrict' testDataFilePath
  (testData :: M.Map Text (HM.HashMap MVar SpecDecl)) <-
    case testDataRaw of
      Left msg -> fail $ "JSON parsing error: " <> msg
      Right v -> pure $ HM.fromList <$> v
  let getTestData name = case name `M.lookup` testData of
        Nothing -> error $ "Could not find test data for: " <> show name
        Just v -> v
  testDataRef <- newIORef testData

  let mkTest :: HasCallStack => STestConfig -> Text -> Text -> Expectation
      mkTest testCfg testName rllFile = do
        let cfg = case mbGlobalConfig of
              Nothing -> testCfg
              Just globalConfig -> globalConfig
        mbDeclMap <- parseFile rllFile
        case mbDeclMap of
          Nothing -> pure ()
          Just declMap -> do
            when (hasTypeVariables declMap) $ expectationFailure "has type variables somewhere"
            case cfg of
              Log -> do
                expectationFailure $ show $ "Logging:" <> line <> prettyDeclMap declMap <> line
              LogJSON -> do
                TIO.putStr $ "    \"" <> testName <> "\": "
                BL.putStr $ encode $ HM.toList declMap
                TIO.putStr "\n"
                expectationFailure "In logging mode."
              UpdateJSON -> do
                modifyIORef testDataRef $ M.insert testName declMap
                expectationFailure "Updating JSON."
              Test -> do
                declMap `shouldBe` getTestData testName
      commit :: IO ()
      commit = do
        updatedTestData <- readIORef testDataRef
        encodeFile testDataFilePath updatedTestData
  pure (mkTest, commit)
