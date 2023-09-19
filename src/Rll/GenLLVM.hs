{-# LANGUAGE RecursiveDo #-}
module Rll.GenLLVM
  ( runGen
  , GenErr(..)
  ) where

import Rll.SpecIR
import Rll.Ast
import Rll.Context (BuiltInFun(..), getBuiltInFunTy)

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.ByteString.Short (ShortByteString, toShort)
import Control.Monad.State (MonadState(..), StateT, runStateT, modify', gets, state)
import Control.Monad.Trans.State.Strict qualified as TSS
import Control.Monad.State.Lazy qualified as LS
import Control.Monad.Fix qualified as MFix
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Word
import Data.Map qualified as Map
import Data.HashMap.Strict qualified as M
import Control.Monad (void, forM_, forM, when)
import Data.Foldable (traverse_, foldlM)
import Data.Functor (($>), (<&>))
import Data.List (zip4, sortBy)
import GHC.Stack (HasCallStack)
import Control.Exception (assert)
import Data.Maybe (fromMaybe, fromJust)
import Data.String (fromString)
import Data.Function (on)
import Debug.Trace qualified as DT

import LLVM.Internal.FFI.DataLayout (getTypeAllocSize)
import LLVM.Internal.DataLayout (withFFIDataLayout)
import LLVM.Internal.Coding (EncodeM(..))
import LLVM.Internal.EncodeAST (EncodeAST, runEncodeAST)
import LLVM.IRBuilder.Internal.SnocList qualified as SL
import LLVM.AST.Typed qualified as AT
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad (named)
import LLVM.IRBuilder.Monad qualified as IR
import LLVM.IRBuilder.Constant qualified as IR
import LLVM.IRBuilder.Instruction qualified as IR
import LLVM.Internal.Context qualified as I
import LLVM.Internal.Type ()
import LLVM.AST.DataLayout qualified as A
import LLVM.AST.Global qualified as AG
import LLVM.AST.FunctionAttribute qualified as A
import LLVM.AST.IntegerPredicate qualified as IP
import LLVM.AST.Instruction qualified as A
import LLVM.AST.Constant qualified as A
import LLVM.AST qualified as A
import LLVM.AST.Type qualified as A
import LLVM.AST.AddrSpace qualified as A

-- TODO: I should look at why I never actually use the information stored in this.

-- | Information about how to build the closure object.
data ClosureInfo = ClosureInfo
  { closureRetType :: A.Type
  , closureArgTypes :: [A.Type]
  }

data GenCtx = GenCtx
  { llvmContext :: I.Context
  , specDecls :: M.HashMap MVar SpecDecl
  -- | The raw types not using named types for each type.
  , rawLlvmTypes :: M.HashMap MVar A.Type
  -- | The data layout we're using for this module.
  --
  -- Specifically this is the layout used to compute union sizes.
  , dataLayout :: A.DataLayout
  , moduleState :: ModuleBuilderState
  , closureInfo :: M.HashMap MVar ClosureInfo
  }

data GenErr
  -- | The type was not an applied type constructor.
  = NotTyCon Ty
  -- | Could not find the type for the name.
  --
  -- I guess maybe out of order?
  | NoTypeForName A.Name
  -- | No spec data type for that MVar.
  | NoSpecDataTypeNamed MVar
  -- | No spec fun for that MVar.
  | NoSpecFunNamed MVar
  deriving (Eq, Show)

newtype Gen a = MkGen { unGen :: StateT GenCtx (ExceptT GenErr IO) a }
  deriving newtype (Functor, Applicative, Monad, MonadState GenCtx, MonadIO, MonadError GenErr)

instance MonadModuleBuilder Gen where
  liftModuleState m = state \ctx ->
    let (a, s) = LS.runState m ctx.moduleState
    in (a, ctx{moduleState=s})

data BuildIRState = BuildIRState
  { buildIRLocal :: IR.IRBuilderState
  , buildIRModule  :: ModuleBuilderState
  , buildIRClosures :: M.HashMap MVar ClosureInfo
  }

newtype BuildIR a = MkBuildIR { unBuildIR :: LS.State BuildIRState a }
  deriving newtype (Functor, Applicative, Monad, MonadState BuildIRState, MFix.MonadFix)


instance MonadModuleBuilder BuildIR where
  liftModuleState m = state \ctx ->
    let (a, s) = LS.runState m ctx.buildIRModule
    in (a, ctx{buildIRModule=s})

instance IR.MonadIRBuilder BuildIR where
  liftIRState m = state \ctx ->
    let (a, s) = TSS.runState m ctx.buildIRLocal
    in (a, ctx{buildIRLocal=s})

-- | Run the IR builder with the module builder info.
--
-- Because Gen has IO in it, we can't use recursive do if we run
-- `IRBuilderT Gen`. So we run a pure version and then update
-- `Gen` with any changes to the module builder state.
runBuildIR :: BuildIR a -> Gen (a, [A.BasicBlock])
runBuildIR act = state \genCtx ->
  let act' = act <* IR.block
      irState = BuildIRState {
        buildIRLocal = IR.emptyIRBuilder,
        buildIRModule = genCtx.moduleState,
        buildIRClosures = genCtx.closureInfo }
      (result, BuildIRState{..}) = flip LS.runState irState $ act'.unBuildIR
      genCtx' = genCtx{moduleState=buildIRModule}
  in ((result, SL.getSnocList buildIRLocal.builderBlocks), genCtx')

{-
-- | Get the closure info for a function.
--
-- Generates the function if it doesn't already exist.
closureInfoFor :: MVar -> Gen ClosureInfo
closureInfoFor var = do
  m <- gets (.closureInfo)
  case M.lookup var m of
    Just i -> pure i
    Nothing -> do
      error "following the order the decls were generated in should make this unneeded"
      sd <- gets (.specDecls)
      case M.lookup var sd of
        Just (SpecFun cenv mbFix params body) ->
          genFun var cenv mbFix params body
        _ -> throwError $ NoSpecFunNamed var
-}

irClosureInfo :: MVar -> BuildIR ClosureInfo
irClosureInfo mvar = do
  m <- gets (.buildIRClosures)
  case M.lookup mvar m of
    Just i -> pure i
    Nothing ->
      error $ "following the order the decls were generated in should make this unneeded: " <> show mvar

-- | Add closure information for a given function.
addClosureInfo :: MVar -> ClosureInfo -> Gen ()
addClosureInfo mvar ci = modify' \ctx ->
  ctx{closureInfo=M.insert mvar ci ctx.closureInfo}

-- | Looks up the type corresponding to an llvm name in the
-- module builder state.
typeForName :: A.Name -> Gen A.Type
typeForName name = do
  mb <- gets (.moduleState)
  case Map.lookup name mb.builderTypeDefs of
    Nothing -> throwError $ NoTypeForName name
    Just ty -> pure ty

-- | Lookup the datatype corresponding to the mangled variable.
lookupSpecDataType :: HasCallStack => MVar -> Gen SpecDataType
lookupSpecDataType mvar = do
  sd <- gets (.specDecls)
  case M.lookup mvar sd of
    Just (SpecDataType sdt)-> pure sdt
    _ -> throwError $ NoSpecDataTypeNamed mvar

-- | Convert text to a short byte string.
textToSBS :: Text -> ShortByteString
textToSBS = toShort . encodeUtf8

-- | Convert an MVar to a llvm name.
mvarToName :: MVar -> A.Name
mvarToName = A.Name . textToSBS . mvarToText

-- | Convert a variable to a llvm name.
varToName :: Var -> A.Name
varToName = A.Name . textToSBS . (.name)

-- | Convert a `MVar` into a reference to it in the global functions.
refGlobalFun :: MVar -> A.Operand
refGlobalFun mv = A.ConstantOperand $ A.GlobalReference $ mvarToName mv

-- | Perform an encoding action inside the `Gen` monad
-- using the llvm context.
encode :: EncodeAST a -> Gen a
encode act = do
  ctx <- gets (.llvmContext)
  liftIO $ runEncodeAST ctx act

-- | Get the size in bytes of the type.
getTypeSize :: A.Type -> Gen Word64
getTypeSize ty = do
  dl <- gets (.dataLayout)
  tyPtr <- encode $ encodeM ty
  liftIO $ withFFIDataLayout dl \dlPtr ->
    -- This is apparently actually a call to ABISizeOfType, which is
    -- what I want. Still weird.
    getTypeAllocSize dlPtr tyPtr

-- | Generate an `MVar` for a data type.
mvarForDataTy :: Ty -> Maybe MVar
mvarForDataTy ty = f <$> parseTyCon ty where
  f (v, tys) = mangleDataType v.name tys

-- | Version of `AT.typeOf` that just immediately throws the error.
typeOf :: (HasCallStack, AT.Typed a) => a -> BuildIR A.Type
typeOf arg = AT.typeOf arg <&> \case
  Left s -> error s
  Right t -> t

-- | This is the closure pointer and then the entry function
-- pointer.
funValueType :: A.Type
funValueType = A.NamedTypeReference "FunValueType"

tmpNullPtr = A.ConstantOperand $ A.Null $ A.ptr

-- | Get the closure pointer from the function value.
getClosurePtr :: A.Operand -> BuildIR A.Operand
getClosurePtr op = IR.extractValue op [0]

-- | Get the entry function pointer from the function value.
getEntryFunPtr :: HasCallStack => A.Operand -> BuildIR A.Operand
getEntryFunPtr op = IR.extractValue op [1]

-- | Free the closure pointer in a function value.
freeClosurePtrIn :: A.Operand -> BuildIR ()
freeClosurePtrIn funVal = do
  closurePtr <- getClosurePtr funVal
  freePtr closurePtr

-- | This is the type for an entry function.
--
-- An entry function is what unpacks arguments from the
-- closure to call the main function.
--
-- It takes the closure pointer, then the stack args pointer,
-- then the number of arguments on the stack, then the pointer
-- that the return value will be sent to.
entryFunType :: A.Type
entryFunType = A.FunctionType A.void args False
  where args = [A.ptr, A.ptr, A.i32, A.ptr]

-- | Build typed struct IR.
buildTypedStructIR :: A.Type -> [A.Operand] -> BuildIR A.Operand
buildTypedStructIR structTy args = do
  let undef = A.ConstantOperand $ A.Undef structTy
      f tmp (arg, i) = IR.insertValue tmp arg [i]
  foldlM f undef $ zip args [0..]

-- | Build struct IR with an MVar name.
buildNamedStructIR :: MVar -> [A.Operand] -> BuildIR A.Operand
buildNamedStructIR mvar = buildTypedStructIR ty
  where ty = A.NamedTypeReference $ mvarToName mvar

-- | Build an anonymous structure value out of dynamic operands.
--
-- Note that this is different than `IR.struct` because
-- that only works with constants.
buildStructIR :: [A.Operand] -> BuildIR A.Operand
buildStructIR args = do
  tys <- traverse typeOf args
  let structTy = A.StructureType False tys
      undef = A.ConstantOperand $ A.Undef structTy
      f tmp (arg, i) = IR.insertValue tmp arg [i]
  foldlM f undef $ zip args [0..]

-- | Build a function value from a closure pointer and function pointer.
buildFunValueFor :: MVar -> A.Operand -> BuildIR A.Operand
buildFunValueFor funMVar closurePtr = do
  let entryFun = refGlobalFun $ mangleEntryFun funMVar
  buildTypedStructIR funValueType [closurePtr, entryFun]

-- | Create the closure pointer, load free variables into a context
-- arg and store it there, and then build the function value.
prepareFunValue :: MVar -> ClosureEnv -> A.Type -> BuildIR A.Operand
prepareFunValue funMVar cenv cenvTy = do
  contextVal <- createClosureEnv cenv cenvTy `named` "context"
  closurePtr <- mallocType cenvTy `named` "closurePtr"
  IR.store closurePtr 1 contextVal
  buildFunValueFor funMVar closurePtr

-- | Try to convert RLL types that aren't data types to LLVM types.
-- data types.
simpleTyToLlvm :: Ty -> Maybe A.Type
simpleTyToLlvm Ty{tyf=FunTy{}} = pure funValueType
simpleTyToLlvm Ty{tyf=RefTy _ Ty{tyf=FunTy{}}} = pure funValueType
simpleTyToLlvm Ty{tyf=RefTy _ _} = pure A.ptr
simpleTyToLlvm Ty{tyf=I64Ty} = pure A.i64
simpleTyToLlvm _ = Nothing

-- | Get the raw llvm representation of a RLL type.
--
-- Will call `genType` if it hasn't already been generated.
toRawLlvmType :: HasCallStack => Ty -> Gen A.Type
toRawLlvmType ty = case simpleTyToLlvm ty of
  Just llvmTy -> pure llvmTy
  Nothing -> do
    mvar <- case mvarForDataTy ty of
      Just mvar -> pure mvar
      Nothing -> throwError $ NotTyCon ty
    rawLlvmTypes <- gets (.rawLlvmTypes)
    case M.lookup mvar rawLlvmTypes of
      Just ty -> pure ty
      Nothing -> do
        sdt <- lookupSpecDataType mvar
        genType mvar sdt

-- | Get the llvm type representation of a RLL reference type.
--
-- Should only be called on types known to be references.
typeForRef :: Ty -> A.Type
typeForRef Ty{tyf=RefTy _ base} = case base.tyf of
  FunTy _ _ _ _ -> funValueType
  _ -> A.ptr
typeForRef _ = error "given a non-reference type"

-- | Normally when we convert a type to an LLVM type,
-- we avoid using any opaque named types. This helps
-- us when calculating the sizes of types for enums.
--
-- However, inside the IR generation we can't access
-- that code because it needs the full `Gen` monad.
-- So instead we use an opaque type.
opaqueTypeFor :: Ty -> A.Type
opaqueTypeFor ty = case simpleTyToLlvm ty of
  Just llvmTy -> llvmTy
  Nothing -> case mvarForDataTy ty of
    Nothing -> error "shouldn't be possible"
    Just mvar -> A.NamedTypeReference $ mvarToName $ mvar

-- | Emits an llvm type definition into the module.
--
-- Convenience wrapper for `emitDefn`.
emitLlvmType :: MVar -> A.Type -> Gen ()
emitLlvmType mvar ty = do
  void $ typedef (mvarToName mvar) (Just ty)

registerRawType :: MVar -> A.Type -> Gen ()
registerRawType mvar ty = modify' \ctx ->
  ctx{rawLlvmTypes=M.insert mvar ty ctx.rawLlvmTypes}

-- | Generate and emit the named type if it doesn't already exist,
-- and store the full raw type for size calculations.
--
-- Returns the raw llvm type.
genType :: HasCallStack => MVar -> SpecDataType -> Gen A.Type
genType mvar sdt = do
  rawLlvmTypes <- gets (.rawLlvmTypes)
  case M.lookup mvar rawLlvmTypes of
    Just ty -> pure ty
    Nothing -> case sdt of
      SpecStruct con mems -> genStruct mvar [] mems
      -- for the enums, we'll generate a type for each individual
      -- constructor and then find the maximum size of a case with it's values,
      -- then create an overall enum type that's a discriminator and a memory
      -- chunk of the given size.
      SpecEnum cons -> do
        let toStruct tys = do
              rawTys <- traverse toRawLlvmType tys
              pure $ A.StructureType False rawTys
        conTys <- traverse toStruct $ M.elems cons
        maxSize <- maximum <$> traverse getTypeSize conTys
        let payloadType = A.VectorType (fromIntegral maxSize) A.i8
            enumTy = if maxSize == 0
              then A.StructureType False [A.i8]
              else A.StructureType False [A.i8, payloadType]
        -- Here we're creating types for each constructor that look like
        -- { i8, ...rest }
        forM_ (M.toList cons) \(con, mems) ->
          genStruct (mangleDataCon mvar $ Var con) [A.i8] mems
        emitLlvmType mvar enumTy
        registerRawType mvar enumTy
        pure enumTy
      SpecBuiltIn b -> case b of
        -- For these, we never need to generate a structure, so we just
        -- return the representative type.
        SpecString -> pure A.ptr
        SpecI64 -> pure A.i64
  where
  genStruct :: MVar -> [A.Type] -> [Ty] -> Gen A.Type
  genStruct mvar prefix mems = do
    let memTys = opaqueTypeFor <$> mems
    emitLlvmType mvar $ A.StructureType False $ prefix <> memTys
    rawTys <- traverse toRawLlvmType mems
    let rawTy = A.StructureType False $ prefix <> rawTys
    registerRawType mvar rawTy
    pure rawTy

-- | Build the opaque type representing a data constructor case.
enumConType :: MVar -> Var -> A.Type
enumConType dtMVar conVar = A.NamedTypeReference $
  mvarToName $ mangleDataCon dtMVar conVar

-- | Convert the closure usage annotations on a type into a
-- llvm type.
closureUseTy :: HasCallStack => ClosureUse Ty -> A.Type
closureUseTy use = case use of
  Moved ty -> opaqueTypeFor ty
  _ -> A.ptr

-- | This assigns an instruction directly to a specific name.
--
-- The normal monad operations will make sure the name is fresh,
-- which would mean I need to carry around a context of names.
addNamedInstr :: A.Name -> A.Instruction -> BuildIR ()
addNamedInstr name instr = IR.modifyBlock \bb -> bb
  { IR.partialBlockInstrs = bb.partialBlockInstrs `SL.snoc` (name A.:= instr)
  }

-- | Extract all of the variables from the closure environment
-- and load them as names.
extractClosureEnv :: ClosureEnv -> A.Operand -> BuildIR ()
extractClosureEnv cenv value = do
  t <- typeOf value
  forM_ (zip [0..] $ M.toList cenv.envMap) \(i,(var, use)) -> do
    val <- IR.extractValue value [i]
    introVarWithLoc var (isClosureUseOnStack use) val

-- | Load all of the variables from the environment and store
-- them in the closure structure.
createClosureEnv :: ClosureEnv -> A.Type -> BuildIR A.Operand
createClosureEnv cenv cenvTy = do
  buildStructIR $ zipWith A.LocalReference types vars
  where
  types = getStructFields cenvTy
  vars = varToName <$> M.keys cenv.envMap

-- | Build a structure with the given llvm types as fields
-- in addition to the initial argument counter.
--
-- This is strictly a type that only the entry functions and
-- things calling them need to worry about.
mkClosureType :: [A.Type] -> A.Type
mkClosureType fields = A.StructureType False $ A.i32:fields

-- | If the closure environment is empty, for right now
-- we just trust llvm to optimize away the empty type.
closureEnvToType :: ClosureEnv -> A.Type
closureEnvToType cenv = A.StructureType False $ closureUseTy <$> M.elems cenv.envMap

-- | Custom defaults for all functions.
baseFunctionDefaults :: A.Global
baseFunctionDefaults = AG.functionDefaults {
  AG.functionAttributes = funAttr}
  where
    funAttr :: [Either A.GroupID A.FunctionAttribute]
    funAttr = [Right A.NoUnwind]

-- | Generate a call to the given function value using the given
-- stack argument pointer.
callWithArgPtr :: HasCallStack => A.Operand -> A.Operand -> A.Operand -> A.Operand -> BuildIR ()
callWithArgPtr funValue returnPtr argCount argPtr = do
  closurePtr <- getClosurePtr funValue
  funPtr <- getEntryFunPtr funValue
  let args = (,[]) <$> [closurePtr, argPtr, argCount, returnPtr]
  -- all entry functions return void.
  void $ IR.call entryFunType funPtr args

-- | Generate a call to the given function value with the
-- argument list.
--
-- We generate this kind of call when we know that we have fully saturated
-- all possible arguments.
--
-- `retTy` is the expected type after all of the arguments have been applied.
funValCall :: HasCallStack => A.Type -> A.Operand -> [A.Operand] -> BuildIR A.Operand
funValCall retTy funValue argOps = do
  returnPtr <- IR.alloca retTy Nothing 1 `named` "returnPtr"
  argStruct <- buildStructIR argOps `named` "argStruct"
  argStructTy <- typeOf argStruct
  argPtr <- IR.alloca argStructTy Nothing 1 `named` "argPtr"
  let argCount = IR.int32 $ toInteger $ length argOps
  callWithArgPtr funValue returnPtr argCount argPtr
  IR.load retTy returnPtr 1

-- | Generate a call to a statically known function.
knownCall :: MVar -> A.Operand -> [A.Operand] -> BuildIR A.Operand
knownCall funMVar cenvOp argOps = do
  let funName = mvarToName $ mangleFastFun funMVar
      funRef = A.ConstantOperand $ A.GlobalReference funName
      args = cenvOp:argOps
  ClosureInfo{closureRetType, closureArgTypes} <- irClosureInfo funMVar
  let numPassedArgs = length args
      retTy = closureRetType
      numReqArgs = length closureArgTypes
      funType = A.FunctionType retTy closureArgTypes False
  if numPassedArgs < numReqArgs
    then do
      clPtr <- buildClosurePtr args
      buildFunValueFor funMVar clPtr
    else do
      let (needed, extra) = splitAt numReqArgs args
      result <- IR.call funType funRef $ (,[]) <$> needed
      case extra of
        [] -> pure result
        _ -> funValCall retTy result extra

-- | Use `GEP` to index into a field of a struct in a pointer.
indexStructPtr :: A.Type -> A.Operand -> Integer -> BuildIR A.Operand
indexStructPtr ty ptr idx = IR.gep ty ptr [IR.int32 0, IR.int32 idx]

-- | Generate the closure type and the structure of the pushed args
-- on the stack for the number of already applied arguments and
-- arguments already on the stack.
closureAndStackFor :: [A.Type] -> Integer -> Integer -> (A.Type, A.Type)
closureAndStackFor args inClosure onStack =
  (mkClosureType closure, st $ take (fromInteger onStack) stack)
  where
  st = A.StructureType False
  (closure, stack) = splitAt (fromInteger inClosure) args

-- | Get fields from a struct type.
getStructFields :: A.Type -> [A.Type]
getStructFields (A.StructureType _ fields) = fields
getStructFields _ = error "was not a struct type"

-- | This functions the same as `closureAndStackFor`, it just only
-- gives the structure of the closure.
closureTyFor :: [A.Type] -> Integer -> A.Type
closureTyFor args i = mkClosureType $ take (fromInteger i) args

-- | Copy struct members from one struct to another.
copyMembersToFrom :: A.Type -> A.Operand -> Integer -> A.Type -> A.Operand -> Integer -> BuildIR ()
copyMembersToFrom toTy toPtr firstToIdx fromTy fromPtr firstFromIdx = do
  let fromFields = drop (fromInteger firstFromIdx) $ getStructFields fromTy
      toFields = drop (fromInteger firstToIdx) $ getStructFields toTy
      fields = zip4 [firstFromIdx..] fromFields [firstToIdx..] toFields
  forM_ fields \(fromIdx, argTy, toIdx, toTy) -> do
    assert (argTy == toTy) $ pure ()
    fromArgPtr <- indexStructPtr fromTy fromPtr fromIdx `named` "fromArgPtr"
    toArgPtr <- indexStructPtr toTy toPtr toIdx `named` "toArgPtr"
    arg <- IR.load argTy fromArgPtr 1 `named` "arg"
    IR.store toArgPtr 1 arg

-- | Load members of a struct pointed to starting from a given index.
loadMembersFrom :: Integer -> A.Type -> A.Operand -> BuildIR [A.Operand]
loadMembersFrom startIdx fromTy fromPtr = do
  let fields = drop (fromInteger startIdx) $ getStructFields fromTy
  forM (zip [startIdx..] fields) \(idx, argTy) -> do
    fromArgPtr <- indexStructPtr fromTy fromPtr idx `named` "fromArgPtr"
    arg <- IR.load argTy fromArgPtr 1 `named` "arg"
    pure arg

-- | Build a closure pointer that holds the given arguments.
--
-- Note that the closure environment should be one of the arguments.
buildClosurePtr :: [A.Operand] -> BuildIR A.Operand
buildClosurePtr heldArgs = do
  argTys <- traverse typeOf heldArgs
  let closureTy = mkClosureType argTys
      size = IR.int32 $ toInteger $ length heldArgs
  newPtr <- mallocType closureTy
  IR.store newPtr 1 size
  forM_ (zip heldArgs [1..]) \(arg, idx) -> do
    argPtr <- indexStructPtr closureTy newPtr idx
    IR.store argPtr 1 arg
  pure newPtr

-- | Generate the entry function for a function.
genEntryFun :: MVar -> Ty -> A.Type -> [A.Type] -> Gen ()
genEntryFun funMVar fullReturnTy fastRetTy llvmArgs = do
  (_, entryBlocks) <- runBuildIR mdo
    entryk <- IR.block `named` "entry"
    -- this is the number of already applied arguments stored in our
    -- closure.
    closureArgCount <- IR.load A.i32 oldClosurePtr 1 `named` "closureArgCount"
    IR.switch closureArgCount impossible jumps

    impossible <- IR.block `named` "impossible"
    IR.unreachable

    -- All closures will have a context argument stored in them,
    -- even if that context argument is a zero width type.
    jumps <- forM [1..(arity-1)] \i -> mdo
      let argsLeft = arity - i
      label <- IR.block `named` "closureArg"

      -- NOTE: Do I need to use a `phi` to grab `closureArgCount`?

      -- Check our pushed args to see if there are enough.
      IR.switch stackArgCount makeCall stackJumps
      -- 1. If there aren't enough, we copy from the stack to a new closure.
      stackJumps <- forM [1..argsLeft-1] \numArgsOnStack -> do
        -- NOTE: in the future I might redo this as something that falls through
        -- to reduce code size? Not sure how I'd handle allocating the new thing though.
        let (oldClosureTy, stackArgsTy) = closureAndStackFor llvmArgs i numArgsOnStack
            newClosureTy = closureTyFor llvmArgs (i+numArgsOnStack)
        label <- IR.block `named` "stackArg"

        -- Load arguments from our old closure type.
        oldClosureArgs <- loadMembersFrom 1 oldClosureTy oldClosurePtr
        extraStackArgs <- loadMembersFrom 0 stackArgsTy stackArgs
        let newClosureArgs = oldClosureArgs <> extraStackArgs

        newClosurePtr <- buildClosurePtr newClosureArgs `named` "newClosurePtr"

        newFunValue <- buildFunValueFor funMVar newClosurePtr `named` "newFunValue"
        returnOp newFunValue
        pure (A.Int 32 numArgsOnStack, label)
      -- 2. If there are enough args, we call the fast function.
      makeCall <- IR.block `named` "makeCall"
      let (oldClosureTy, stackArgsTy) = closureAndStackFor llvmArgs i argsLeft
          loadArgsFrom i t o = fmap (fmap (,[])) $ loadMembersFrom i t o
      loadedClosureArgs <- loadArgsFrom 1 oldClosureTy oldClosurePtr
      loadedStackArgs <- loadArgsFrom 0 stackArgsTy stackArgs
      let fastArgs = loadedClosureArgs <> loadedStackArgs
      -- call the fast function with the loaded arguments
      result <- IR.call fastFunTy fastFunRef fastArgs `named` "result"

      -- 3. We check the return type to see if we need to generate
      -- code for handling extra arguments.
      case fullReturnTy.tyf of
        -- a. If the return type can be a function, we need to deal with possible
        -- extra arguments.
        FunTy mult _ _ _ -> mdo
          -- check if we have extra args
          cond <- IR.icmp IP.UGT stackArgCount $ IR.int32 argsLeft
          IR.condBr cond immediateReturn secondCall

          -- If we have no extra arguments, return immediately.
          immediateReturn <- IR.block `named` "immediateReturn"
          returnOp result

          -- If we have extra arguments, we do a second call.
          secondCall <- IR.block `named` "secondCall"
          -- we use GEP to calculate the right offset and then
          -- generate the calling code with the remaining arguments
          -- and offset stack pointer.
          restArgsPtr <- IR.gep stackArgsTy stackArgs [IR.int32 1] `named` "restArgsPtr"
          let argsLeftOp = IR.int32 $ argsLeft
          restArgsCount <- IR.sub stackArgCount argsLeftOp `named` "restArgCount"
          -- We call the returned function value, which stores the result in the return
          -- pointer.
          callWithArgPtr result returnPtr restArgsCount restArgsPtr
          -- Then since we're never returning the function value in result, we
          -- have to free the closure pointer.
          freeClosurePtrIn result
          -- Now we return void having already stored the result in the returnPtr given
          -- to this entry function.
          IR.retVoid

        -- b. If the return type is not a function, we know that we can
        -- always return the result.
        _ -> returnOp result
      pure $ (A.Int 32 $ fromInteger i, label)
    pure ()
  let entryBlockNames = entryBlocks <&> \(A.BasicBlock n _ _) -> n
  emitDefn $ A.GlobalDefinition $ baseFunctionDefaults
    { AG.name = mvarToName $ mangleEntryFun funMVar
    , AG.parameters =
      ([ A.Parameter A.ptr "oldClosurePtr" []
        , A.Parameter A.ptr "stackArgs" []
        , A.Parameter A.i32 "stackArgCount" []
        , A.Parameter A.ptr "returnPtr" []
        ], False)
    , AG.basicBlocks = entryBlocks
    , AG.returnType = A.void
    }
  where
  -- Arguments for inside the function
  oldClosurePtr = A.LocalReference A.ptr "oldClosurePtr"
  stackArgs = A.LocalReference A.ptr "stackArgs"
  stackArgCount = A.LocalReference A.i32 "stackArgCount"
  returnPtr = A.LocalReference A.ptr "returnPtr"
  -- information about the actual implementation of the function.
  fastFunRef = refGlobalFun $ mangleFastFun funMVar
  fastFunTy = A.FunctionType fastRetTy llvmArgs False
  arity = toInteger $ length llvmArgs
  -- | Utility function that assigns to the return pointer
  -- and then returns.
  returnOp :: A.Operand -> BuildIR ()
  returnOp op = do
    IR.store returnPtr 1 op
    IR.retVoid

-- | Build name for the recursive context from the
-- recursive function variable name.
mkRecContextVar :: Var -> Var
mkRecContextVar (Var txt) = Var $ txt <> ".context"

-- | Introduce a new local variable.
--
-- Updates the table of fresh names in the IR.
introVarName :: Var -> BuildIR A.Name
introVarName (Var txt) = IR.freshName $ textToSBS txt

-- | Get the latest version of a name.
--
-- This is a fairly hacky solution that relies on name shadowing
-- being a type error. Our problem is that let blocks disappear in
-- LLVM IR. However, because all usage of a type name is disjoint,
-- we can simply always use the latest version of a name.
localVarName :: Var -> BuildIR A.Name
localVarName (Var txt) = do
  usedNames <- IR.liftIRState $ gets IR.builderUsedNames
  let rawName = textToSBS txt
      nameCount = case Map.lookup rawName usedNames of
        Nothing -> error $ "Variable " <> show txt <> " had not been used."
        -- We subtract one because the state stores the next unused index.
        Just count -> count - 1
      name = rawName <> fromString ("_" <> show nameCount)
  pure $ A.Name name

-- | Load the raw value from the local variable without checking if
-- it's a pointer that needs to be loaded from the stack.
localVarRaw :: Var -> A.Type -> BuildIR A.Operand
localVarRaw var llvmTy = do
  name <- localVarName var
  pure $ A.LocalReference llvmTy name

-- | Assume that a local variable is a pointer to the stack and load
-- it from memory.
localVarLoad :: Var -> A.Type -> BuildIR A.Operand
localVarLoad var llvmTy = do
  name <- localVarName var
  let varPtr = A.LocalReference A.ptr name
  IR.load llvmTy varPtr 1

-- | Whether a variable's true value is on the stack and the variable
-- is just a pointer to that, or the variable is the actual value.
data VarLoc = OnStack | InReg

-- | A predicate determining whether a type is allocated
-- on the stack or not.
isTyOnStack :: Ty -> VarLoc
isTyOnStack ty = case ty.tyf of
  FunTy _ _ _ _ -> InReg
  RefTy _ _ -> InReg
  _ -> OnStack

-- | Determine whether we allocate a type in a closure use on the stack
-- or not.
isClosureUseOnStack :: ClosureUse Ty -> VarLoc
isClosureUseOnStack (Moved ty) = isTyOnStack ty
isClosureUseOnStack _ = InReg

-- | Takes a variable name and a value and returns an llvm
-- variable holding either a pointer to the stack allocation
-- of the value or the value itself.
introVarWithLoc :: Var -> VarLoc -> A.Operand -> BuildIR A.Operand
introVarWithLoc var varLoc value = do
  name <- introVarName var
  t <- typeOf value
  case varLoc of
    InReg -> do
      -- This is a hacky awful thing that just exists to let us alias a register
      -- level variable.
      tmpLoc <- IR.alloca t Nothing 1 `named` "tmpLoc"
      IR.store tmpLoc 1 value
      addNamedInstr name $ A.Load False t tmpLoc Nothing 1 []
      pure $ A.LocalReference t name
    OnStack -> do
      addNamedInstr name $ A.Alloca t Nothing 1 []
      let loc = A.LocalReference A.ptr name
      IR.store loc 1 value
      pure loc

-- | Introduce a variable name and store it on the stack or in register
-- based on the RLL type.
introVar :: Var -> Ty -> A.Operand -> BuildIR A.Operand
introVar var ty value = introVarWithLoc var (isTyOnStack ty) value

-- | Uses `localVarName` to build a local reference operand.
--
-- We use `isTyOnStack` to figure out from the Rll type whether or not
-- the value is on the stack or in the raw variable.
-- `onStack` indicates whether or not to load the variable from the
-- stack. If it's true, the variable is a pointer to the passed type.
-- If it's false, the variable is the passed type.
localVarOp :: Var -> Ty -> A.Type -> BuildIR A.Operand
localVarOp var varTy llvmTy = do
  name <- localVarName var
  case isTyOnStack varTy of
    OnStack -> localVarLoad var llvmTy
    InReg -> localVarRaw var llvmTy

-- | Build a structure containing all free variables in a closure.
buildClosureEnv :: ClosureEnv -> BuildIR A.Operand
buildClosureEnv cenv = traverse go (M.toList cenv.envMap) >>= buildStructIR
  where
  -- TODO: this is going to have a problem with function values
  go (var, Moved ty) = localVarOp var ty $ opaqueTypeFor ty
  go (var, Copied ty) = localVarRaw var $ typeForRef ty
  go (var, Refd ty) = localVarRaw var $ typeForRef ty

-- | Generate the LLVM IR for expressions.
genIR :: A.Type -> SpecIR -> BuildIR A.Operand
genIR cenvTy = go where
  -- | Where we handle all of the IR cases.
  go :: SpecIR -> BuildIR A.Operand
  go expr = case expr.specf of
    BuiltInFunSF fun -> builtInFunCall fun []
    ClosureSF funMVar cenv -> do
      cenvOp <- buildClosureEnv cenv
      closurePtr <- buildClosurePtr [cenvOp]
      buildFunValueFor funMVar closurePtr
    RecClosureSF funMVar contextVar -> do
      cenvOp <- localVarRaw (mkRecContextVar contextVar) cenvTy
      closurePtr <- buildClosurePtr [cenvOp]
      buildFunValueFor funMVar closurePtr
    AppSF funExpr args -> do
      case funExpr.specf of
        BuiltInFunSF fun -> do
          argOps <- traverse go args
          builtInFunCall fun argOps
        ClosureSF funMVar cenv -> do
          argOps <- traverse go args
          cenvOp <- buildClosureEnv cenv
          knownCall funMVar cenvOp argOps
        RecClosureSF funMVar contextVar -> do
          argOps <- traverse go args
          cenvOp <- localVarRaw (mkRecContextVar contextVar) cenvTy
          knownCall funMVar cenvOp argOps
        _ -> do
          let retTy = opaqueTypeFor expr.ty
              -- if it's a bare function type we know we're dropping it.
              isDropped = case funExpr.ty.tyf of
                FunTy _ _ _ _ -> True
                _ -> False
          funVal <- go funExpr
          argOps <- traverse go args
          result <- funValCall retTy funVal argOps
          when isDropped $ freeClosurePtrIn funVal
          pure result
    VarSF var -> localVarOp var expr.ty $ opaqueTypeFor expr.ty
    CopySF var -> case expr.ty.tyf of
      I64Ty -> localVarLoad var A.i64
      _ -> localVarRaw var $ typeForRef expr.ty
    DropSF svar varTy body -> do
      case varTy.tyf of
        FunTy Many _ _ _ -> do
          varOp <- localVarRaw svar.var funValueType
          freeClosurePtrIn varOp
        RefTy _ _ -> pure ()
        I64Ty -> pure ()
        _ -> error "shouldn't be able to drop this"
      go body
    LetSF svar t1 t2 -> do
      t1Val <- go t1
      introVar svar.var t1.ty t1Val
      -- NOTE: in the future I can probably use the lifetime intrinsics to
      -- start and end the alloc lifetime around `go t2`.
      go t2
    RefSF var -> localVarRaw var $ typeForRef expr.ty
    StructConSF dtMVar args -> traverse go args >>= buildNamedStructIR dtMVar
    EnumConSF tagValue dtMVar conVar args -> do
      let rawEnumTy = A.NamedTypeReference $ mvarToName dtMVar
      argOps <- traverse go args
      conVal <- buildNamedStructIR (mangleDataCon dtMVar conVar) $ (IR.int8 tagValue):argOps
      enumLoc <- IR.alloca rawEnumTy Nothing 1
      IR.store enumLoc 1 conVal
      IR.load rawEnumTy enumLoc 1
    CaseSF t1 branches -> mdo
      let getConTxt (CaseBranchTy svar _ _) = svar.var.name
          orderedBranches = sortBy (compare `on` getConTxt) branches
      (enumLoc, conTag, dtMVar) <- case t1.ty.tyf of
        RefTy _ dtTy -> do
          let dtMVar' = fromJust $ mvarForDataTy dtTy
              rawEnumTy = A.NamedTypeReference $ mvarToName dtMVar'
          enumLoc' <- go t1
          conTagLoc <- indexStructPtr rawEnumTy enumLoc' 0
          conTag' <- IR.load A.i8 conTagLoc 1 `named` "constructorTag"
          pure (enumLoc', conTag', dtMVar')
        _ -> do
          -- NOTE: I think I have to do this really annoying bitcast thing right now.
          -- hopefully I can find optimization passes or something to avoid this. Or
          -- a bitcast that works on structures.
          let dtMVar' = fromJust $ mvarForDataTy t1.ty
          rawEnumVal <- go t1
          conTag' <- IR.extractValue rawEnumVal [0] `named` "constructorTag"
          rawEnumTy <- typeOf rawEnumVal
          enumLoc' <- IR.alloca rawEnumTy Nothing 1
          IR.store enumLoc' 1 rawEnumVal
          pure (enumLoc', conTag', dtMVar')
      IR.switch conTag impossible $ dests <&> \(tagVal, label,_) -> (tagVal, label)
      dests <- forM (zip [0..] orderedBranches) \(i, CaseBranchTy conSVar memVarTys body) -> do
        conLabel <- IR.block `named` textToSBS conSVar.var.name
        let conTy = enumConType dtMVar conSVar.var
        conVal <- IR.load conTy enumLoc 1
        forM_ (zip [0..] memVarTys) \(i, (SVar{var}, varTy)) -> do
          mem <- IR.extractValue conVal [i]
          introVar var varTy mem
        conResult <- go body
        IR.br caseEnd
        pure (A.Int 8 i, conLabel, conResult)
      impossible <- IR.block `named` "impossible"
      IR.unreachable
      caseEnd <- IR.block `named` "caseEnd"
      IR.phi $ dests <&> \(_, label, res) -> (res, label)
    LetStructSF conVar memSVars t1 t2 -> do
      (structVal, dtMVar) <- case t1.ty.tyf of
        RefTy _ dtTy -> do
          let dtMVar' = fromJust $ mvarForDataTy dtTy
              structTy = A.NamedTypeReference $ mvarToName dtMVar'
          structPtr <- go t1
          structVal' <- IR.load structTy structPtr 1
          pure (structVal', dtMVar')
        _ -> do
          let dtMVar = fromJust $ mvarForDataTy t1.ty
          structVal' <- go t1
          pure (structVal', dtMVar)
      forM_ (zip [0..] memSVars) \(i, (SVar{var}, varTy)) -> do
        mem <- IR.extractValue structVal [i]
        introVar var varTy mem
      go t2
    LiteralSF (IntLit value) -> pure $ IR.int64 value
    LiteralSF (StringLit txt) -> error "TODO: strings not implemented"

-- | Introduce a function argument.
introArg :: Var -> A.Type -> VarLoc -> BuildIR (A.Name, A.Operand)
introArg var llvmTy varLoc = do
  name <- introVarName var
  let argRef = A.LocalReference llvmTy name
  -- We need to store it on the stack so that it can have references
  -- taken in the function body.
  case varLoc of
    OnStack -> void $ introVarWithLoc var OnStack argRef
    -- For in register stuff, we can just skip
    InReg -> pure ()
  pure (name, argRef)

-- | Get both the llvm and rll arguments and return type for a built-in function.
builtInFunLlvmInfo :: BuiltInFun -> ([Ty], [A.Type], Ty, A.Type)
builtInFunLlvmInfo fun = (rllArgs, args, rllRet, ret)
  where
  args = opaqueTypeFor <$> rllArgs
  ret = opaqueTypeFor rllRet
  (rllArgs, rllRet) = case parseFunTy $ getBuiltInFunTy fun of
    Just info -> info
    Nothing -> error "Compiler error: built-in functions should be monomorphic functions"

-- | Perform an operation for a built-in function if there are enough
-- operands.
builtInFunOp :: BuiltInFun -> [A.Operand] -> BuildIR (Maybe A.Operand)
builtInFunOp AddI64 [a1, a2] = Just <$> IR.add a1 a2
builtInFunOp _ _ = pure Nothing

-- | Generate a call to a built-in function/operation.
--
-- If there are enough arguments we'll inline the operation.
builtInFunCall :: BuiltInFun -> [A.Operand] -> BuildIR A.Operand
builtInFunCall fun args = do
  opResult <- builtInFunOp fun args
  case opResult of
    Just result -> pure result
    Nothing -> do
      -- We know that we don't have enough and need to build a closure
      -- pointer.
      --
      -- One advantage of this is that we don't need to generate or store
      -- any `ClosureInfo` because we can get that just from `fun`. Normally
      -- you can't figure out how many arguments the llvm function takes
      -- just from the type, but we don't have that problem.
      blankCenvOp <- buildClosureEnv $ ClosureEnv M.empty
      clPtr <- buildClosurePtr $ blankCenvOp:args
      buildFunValueFor (mangleBuiltInFun fun) clPtr

-- | Generate the fast function wrapper and entry function for a built-in function.
genBuiltInFun :: BuiltInFun -> Gen ()
genBuiltInFun fun = do
  let (rllArgTys, llvmArgTys, rllRetTy, llvmRetTy) = builtInFunLlvmInfo fun
      cenvTy = closureEnvToType $ ClosureEnv M.empty
      argVars = [1..length llvmArgTys + 1] <&> \i -> Var $ "arg" <> T.pack (show i)
      cenvVar = Var "arg0"
      fullArgTys = cenvTy:llvmArgTys
  (argNames, llvmBlocks) <- runBuildIR do
    _entry <- IR.block `named` "entry"
    cenvName <- introVarName cenvVar
    let calcArgs a b c = fmap unzip $ sequence $ zipWith3 introArg a b c
    (argNames, args) <- calcArgs argVars llvmArgTys $ isTyOnStack <$> rllArgTys
    opResult <- builtInFunOp fun args
    case opResult of
      Nothing -> error "Compiler error: failed to generate operation"
      Just funRes -> IR.ret funRes
    pure $ cenvName:argNames
  let fastParams = zipWith (\name ty -> A.Parameter ty name []) argNames fullArgTys
      fastName = mvarToName $ mangleFastFun funMVar
      fastDef = baseFunctionDefaults
        { AG.name = fastName
        , AG.parameters = (fastParams, False) -- False means not varargs
        , AG.basicBlocks = llvmBlocks
        , AG.returnType = llvmRetTy
        }
      llvmArgTys = fastParams <&> \(A.Parameter ty _ _) -> ty
  emitDefn $ A.GlobalDefinition fastDef
  genEntryFun (mangleBuiltInFun fun) rllRetTy llvmRetTy fullArgTys
  where
  funMVar = mangleBuiltInFun fun

-- | Generate the entry and fast function.
genFun :: HasCallStack => MVar -> ClosureEnv -> (Maybe SVar) -> [(SVar, Ty, Mult)] -> SpecIR -> Gen ClosureInfo
genFun funMVar cenv mbFix params body = do
  cim <- gets (.closureInfo)
  case M.lookup funMVar cim of
    Just ci -> pure ci
    Nothing -> do
      let fastRetTy = opaqueTypeFor body.ty
          ctxTy = closureEnvToType cenv
          llvmParamTys = opaqueTypeFor <$> paramTys
      (allArgNames, fastBlocks) <- runBuildIR do
        _entry <- IR.block `named` "entry"
        (ctxName, ctxOp) <- introArg contextVar ctxTy InReg
        let calcArgs a b c = fmap unzip $ sequence $ zipWith3 introArg a b c
        (argNames, _) <- calcArgs paramVars llvmParamTys $ isTyOnStack <$> paramTys
        case mbFix of
          Nothing -> pure ()
          Just SVar{var} -> do
            val <- buildFunValueFor funMVar ctxOp
            void $ introVarWithLoc var InReg val
        extractClosureEnv cenv ctxOp
        bodyVal <- genIR ctxTy body
        IR.ret bodyVal
        pure $ ctxName:argNames
      let fastParams = zipWith (\name ty -> A.Parameter ty name []) allArgNames (ctxTy:llvmParamTys)
          fastName = mvarToName $ mangleFastFun funMVar
          fastDef = baseFunctionDefaults
            { AG.name = fastName
            , AG.parameters = (fastParams, False) -- False means not varargs
            , AG.basicBlocks = fastBlocks
            , AG.returnType = fastRetTy
            }
          llvmArgTys = fastParams <&> \(A.Parameter ty _ _) -> ty
      emitDefn $ A.GlobalDefinition fastDef
      genEntryFun funMVar body.ty fastRetTy llvmArgTys
      let closureInfo = ClosureInfo fastRetTy llvmArgTys
      addClosureInfo funMVar closureInfo
      pure closureInfo
  where
  (paramVars, paramTys) = unzip $ params <&> \(svar, ty, _) -> (svar.var, ty)
  contextVar = mkRecContextVar $ maybe (Var "emptyCtx") (.var) mbFix

-- | Declare an entry main that the JIT can interact with.
declareEntryMain :: Gen ()
declareEntryMain = do
  void $ function "entryMain" [(A.i64, "val")] A.i64 \[val] -> do
    let emptyVal = IR.struct Nothing False []
        args = fmap (,[]) [emptyVal, val]
        emptyStructTy = A.StructureType False []
        mainTy = A.FunctionType A.i64 [emptyStructTy, A.i64] False
        mainRef = funRef "main%.fast"
    result <- IR.call mainTy mainRef args `named` "result"
    IR.ret result
  void $ function "main" [] A.void \[] -> do
    let entryMainRef = funRef "entryMain"
        args = fmap (,[]) [IR.int64 1]
        entryMainTy = A.FunctionType A.i64 [A.i64] False
        printfTy = A.FunctionType A.void [A.ptr] True
        printfRef = funRef "printf"
    result <- IR.call entryMainTy entryMainRef args `named` "result"
    formatStr <- IR.globalStringPtr "%lld\n" "print_answer"
    let pargs = fmap (,[]) [A.ConstantOperand formatStr, result]
    IR.call printfTy printfRef pargs
    IR.retVoid
  where
  funRef = A.ConstantOperand . A.GlobalReference

-- | Declare the external functions for all the important calls like malloc.
llvmDeclarations :: Gen ()
llvmDeclarations = do
  void $ typedef "FunValueType" $ Just $ A.StructureType False [A.ptr, A.ptr]
  void $ extern "malloc" [A.i32] A.ptr
  void $ extern "free" [A.ptr] A.void
  void $ externVarArgs "printf" [A.ptr] A.void

-- | Perform a get element pointer on the type to get its size
-- and then malloc a space on the heap.
mallocType :: A.Type -> BuildIR A.Operand
mallocType ty = do
  let mallocTy = A.FunctionType A.ptr [A.i32] False
      mallocFunPtr = A.ConstantOperand $ A.GlobalReference "malloc"
      size = A.ConstantOperand $ A.sizeof 32 ty
  let args = (,[]) <$> [size]
  IR.call mallocTy mallocFunPtr args

-- | Free the pointer operand.
freePtr :: A.Operand -> BuildIR ()
freePtr ptrVal = do
  let freeTy = A.FunctionType A.void [A.ptr] False
      freeRef = A.ConstantOperand $ A.GlobalReference "free"
      args = (,[]) <$> [ptrVal]
  void $ IR.call freeTy freeRef args

-- | Generate llvm IR for the declaration.
genDecl :: MVar -> SpecDecl -> Gen ()
genDecl mvar decl = case decl of
  SpecDataType sdt -> do
    void $ genType mvar sdt
  SpecBuiltInFun fun -> do
    genBuiltInFun fun
  SpecFun cenv mbFix args bodyIR -> void $ genFun mvar cenv mbFix args bodyIR

-- | Generate a list of LLVM definitions.
--
-- Takes a map of declarations and a list of declarations in the correct load order.
runGen :: SpecResult -> I.Context -> A.DataLayout -> IO (Either GenErr [A.Definition])
runGen SpecResult{..} llvmCtx dl = do
  let genCtx = GenCtx {
        llvmContext=llvmCtx,
        rawLlvmTypes=M.empty,
        dataLayout=dl,
        specDecls=declMap,
        moduleState=emptyModuleBuilder,
        closureInfo=M.empty
        }
      act = do
        llvmDeclarations
        let isTyDecl (_, SpecDataType _) = True
            isTyDecl _ = False
            specDecls' = reverse declOrder
            tyDecls = filter isTyDecl specDecls'
            funDecls = filter (not . isTyDecl) specDecls'
        traverse_ (uncurry genDecl) $ tyDecls
        traverse_ (uncurry genDecl) $ funDecls
        declareEntryMain
        defs <- gets (.moduleState.builderDefs)
        pure $ SL.unSnocList defs
  fmap (fst <$>) $ runExceptT $ flip runStateT genCtx $ unGen act
