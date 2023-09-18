{-# LANGUAGE ForeignFunctionInterface #-}
module Rll.Orchestra (jitModule) where

import Rll.OrchTypes
import qualified Rll.Parser as RP
import Rll.TypeCheck (typeCheckFile)
import Rll.TcMonad (runTc)
import Rll.Spec (specModule)
import Rll.Context (emptyCtx)
import Rll.GenLLVM (runGen)

import Data.Text (Text)
import Data.Text qualified as T
import Text.Megaparsec qualified as MP
import Data.Int (Int64)
import Foreign.Ptr (FunPtr, wordPtrToPtr, castPtrToFunPtr)
import Foreign.C.Types (CLong(..))
import Data.ByteString.Char8 qualified as BSC
import Data.ByteString.Lazy qualified as LBS
import Data.Functor ((<&>))
import System.Process.Typed qualified as PT

import qualified LLVM.CodeModel
import qualified LLVM.CodeGenOpt
import LLVM.Relocation (Model(PIC))
import LLVM.AST qualified as A
import LLVM.Internal.Context qualified as I
import LLVM.Internal.Target qualified as I
import LLVM.OrcJIT qualified as J
import LLVM.Target qualified as L
import LLVM.Module qualified as L
import LLVM.Context qualified as L
import LLVM.Passes qualified as L

foreign import ccall "dynamic" mkMain :: FunPtr (CLong -> IO CLong) -> CLong -> IO CLong

prepareModule :: I.Context -> I.TargetMachine -> RllSrcModule -> IO (Either OrchErr A.Module)
prepareModule ctx target src@RllSrcModule{..} =
  case MP.parse RP.fileDecls (T.unpack fileName) moduleSrc of
    Left err -> pure $ Left $ OParseErr err
    Right decls ->
      case runTc emptyCtx $ typeCheckFile decls of
        Left err -> pure $ Left $ OTyErr err
        Right (tcResult, _) ->
          case specModule tcResult of
            Left err -> pure $ Left $ OSpecErr err
            Right specResult -> do
              layout <- I.getTargetMachineDataLayout target
              triple <- I.getTargetMachineTriple target
              result <- runGen specResult ctx layout
              pure $ case result of
                Left err -> Left $ OGenErr err
                Right defs -> Right $ toLlvmModule src layout triple defs

passes :: [L.ModulePass]
passes = [L.GlobalDeadCodeElimination, L.CuratedPassSet 3]

jitModule :: RllSrcModule -> (Either OrchErr (Int64 -> IO Int64) -> IO a) -> IO a
jitModule src cont = L.withContext \ctx ->
  L.withHostTargetMachine PIC LLVM.CodeModel.Default LLVM.CodeGenOpt.Default \tm -> do
    prepareModule ctx tm src >>= \case
      Left err -> cont $ Left err
      Right astMod -> L.withModuleFromAST ctx astMod \mod -> do
        let passSpec = L.PassSetSpec passes (Just tm)
        -- L.runPasses passSpec mod
        J.withExecutionSession \es -> do
          -- This gets us the LLVM IR
          asm <- L.moduleLLVMAssembly mod
          BSC.writeFile "./llvmir" asm
          PT.runProcess_ $ PT.setStdin (PT.byteStringInput $ LBS.fromStrict asm) $ "lli --load=$(gcc --print-file-name=libc.so.6)"
          dylib <- J.createJITDylib es "rllDylib"
          J.withClonedThreadSafeModule mod $ \tsm -> do
            ol <- J.createRTDyldObjectLinkingLayer es
            il <- J.createIRCompileLayer es ol tm

            -- path found via: `gcc -- gcc --print-file-name=libc.so.6`
            let glibcPath = "/nix/store/46m4xx889wlhsdj72j38fnlyyvvvvbyb-glibc-2.37-8/lib/libc.so.6"
            J.addDynamicLibrarySearchGenerator il dylib glibcPath
            J.addModule tsm dylib il
            sym <- J.lookupSymbol es il dylib "entryMain"
            case sym of
              Left (J.JITSymbolError err) -> cont $ Left $ JITError err
              Right (J.JITSymbol mainFn _) ->
                let raw = mkMain (castPtrToFunPtr (wordPtrToPtr mainFn))
                    f arg = raw (CLong arg) <&> \case
                      CLong res -> res
                in cont $ Right f
