module Rll.OrchTypes
  ( RllSrcModule(..), OrchErr(..)
  , prettyPrintError, toLlvmModule
  ) where

import qualified Rll.Parser as RP
import Rll.SpecIR (SpecErr)
import Rll.TypeError (TyErr)
import Rll.TypeError qualified as TE
import Rll.GenLLVM (GenErr)

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.ByteString.Short (ShortByteString, toShort)
import Text.Megaparsec qualified as MP

import LLVM.AST qualified as A
import LLVM.AST.DataLayout qualified as A

data RllSrcModule = RllSrcModule
  { fileName :: Text
  , moduleName :: Text
  , moduleSrc :: Text
  }

data OrchErr
  = OParseErr (MP.ParseErrorBundle Text RP.RllParseError)
  | OTyErr TyErr
  | OSpecErr SpecErr
  | OGenErr GenErr
  | JITError ShortByteString

prettyPrintError :: RllSrcModule -> OrchErr -> Text
prettyPrintError RllSrcModule{moduleSrc} err = case err of
  OParseErr bundle -> T.pack $ MP.errorBundlePretty bundle
  OTyErr tyErr -> TE.prettyPrintError moduleSrc tyErr
  OSpecErr specErr -> T.pack $ show specErr
  OGenErr genErr -> T.pack $ show genErr
  JITError sbs -> T.pack $ "JIT Error: " <> show sbs

toLlvmModule :: RllSrcModule -> A.DataLayout -> ShortByteString -> [A.Definition] -> A.Module
toLlvmModule src layout targetTriple defs =
  A.Module (conv (.moduleName)) (conv (.fileName)) (Just layout) (Just targetTriple) defs
  where conv f = toShort $ encodeUtf8 $ f $ src
