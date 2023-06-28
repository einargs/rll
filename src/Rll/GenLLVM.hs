module Rll.GenLLVM
  (
  ) where

import Rll.SpecIR

import Data.Text (Text, encodeUtf8)
import Data.ByteString.Short (ShortByteString, toShort)
import Control.Monad.State (MonadState(..), StateT, runStateT, modify', gets, state)
import Control.Monad.Except (MonadError(..), ExceptT, runExcept)
import Control.Monad.State.Strict qualified as IRS
import Control.Monad.IO.Class (MonadIO(..))
import Data.Word
import Data.Map qualified as Map

import LLVM.Internal.FFI.DataLayout (getTypeAllocSize)
import LLVM.Internal.DataLayout (withFFIDataLayout)
import LLVM.Internal.Coding (EncodeM(..))
import LLVM.Internal.EncodeAST (EncodeAST, runEncodeAST)
import LLVM.IRBuilder.Module
import LLVM.Internal.Type qualified as L
import LLVM.Internal.Context qualified as L
import LLVM.AST.DataLayout qualified as A
import LLVM.AST qualified as A

data GenCtx = GenCtx
  { llvmContext :: L.Context
  , moduleState :: ModuleBuilderState
  }

data GenErr
  -- | The type was not an applied type constructor.
  = NotTyCon Ty
  -- | Could not find the type for the name.
  --
  -- I guess maybe out of order?
  | NoTypeForName A.Name

newtype Gen a = MkGen { unGen :: StateT GenCtx (ExceptT GenErr IO) a }
  deriving newtype (Functor, Applicative, Monad, MonadState GenCtx, MonadIO, MonadError GenErr)

instance MonadModuleBuilder Gen where
  liftModuleState m = state \ctx ->
    let (a, s) = IRS.runState m ctx.moduleState
    in (a, ctx{moduleState=s})

-- | Convert text to a short byte string.
textToSBS :: Text -> ShortByteString
textToSBS = toShort . enocdeUtf8

-- | Convert an MVar to a llvm name.
mvarToName :: MVar -> A.Name
mvarToName = A.Name . textToSBS . mvarToText

-- | Perform an encoding action inside the `Gen` monad
-- using the llvm context.
encode :: EncodeAST a -> Gen a
encode act = do
  ctx <- gets (.llvmContext)
  liftIO $ runEncodeAST ctx act

-- | Get the size in bytes of the type.
getTypeSize :: A.DataLayout -> A.Type -> Gen Word64
getTypeSize dl ty = do
  tyPtr <- encode $ encodeM ty
  liftIO $ withFFIDataLayout dl \dlPtr ->
    -- This is apparently actually a call to ABISizeOfType, which is
    -- what I want. Still weird.
    getTypeAllocSize dlPtr tyPtr

typeForName :: A.Name -> Gen A.Type
typeForName name = do
  mb <- gets (.moduleState)
  case M.lookup name mb.builderTypeDefs of
    Nothing -> throwError $ NoTypeForName name
    Just ty -> pure ty

-- | Since all of our types will eventually be generated, we can just
-- refer to them.
nameForTy :: Ty -> Gen A.Name
nameForTy ty = do
  mvar <- case collectApps [] ty of
    Nothing -> throwError $ NotTyCon ty
    Just (v, tys) -> mangleDataType v.name $ reverse tys
  pure $ mvarToName name
  where
    collectApps :: [Ty] -> Ty -> Maybe (Var, [Ty])
    collectApps rs ty = case ty.tyf of
      TyApp b a -> collectApps (a:rs) b
      TyCon v -> Just (v, rs)
      _ -> Nothing

toLlvmType :: Ty -> Gen A.Type
toLlvmType ty = A.NamedTypeReference <$> nameForType ty

genType :: MVar -> SpecDataType -> Gen ()
genType mvar sdt = case sdt of
  SpecStruct con mems -> genStruct mvar mems
  -- for the enums, we'll generate a type for each individual
  -- constructor and then do bitcasts.
  SpecEnum cons -> do
    conTys <- traverse (uncurry genCon) $ M.toList cons
    -- find biggest, use that to make a structure as a middle ground
    -- then create a structure that uses a tag
  where
  genCon :: Text -> [Ty] -> Gen A.Type
  genCon con mems = genStruct (mangleDataCon mvar con) mems
  genStruct :: MVar -> [Ty] -> Gen A.Type
  genStruct mvar mems = do
    emitDefn $ TypeDefinition (mvarToName mvar) (Just structTy)
    pure structTy
    where structTy = A.StructureType False $ toLlvmType <$> mems
