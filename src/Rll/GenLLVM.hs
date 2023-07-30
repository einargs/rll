{-# LANGUAGE RecursiveDo #-}
module Rll.GenLLVM
  ( runGen
  , GenErr(..)
  ) where

import Rll.SpecIR
import Rll.Ast

import Data.Text (Text)
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
import Debug.Trace qualified as D
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

-- TODO: I should look at why I never actually use the information stored in this.

-- | Information about how to build the closure object.
data ClosureInfo = ClosureInfo
  { closureRetType :: A.Type
  , closureArgTypes :: [A.Type]
  }

data GenCtx = GenCtx
  { llvmContext :: I.Context
  -- | The data layout we're using for this module.
  --
  -- Specifically this is the layout used to compute union sizes.
  , specDecls :: M.HashMap MVar SpecDecl
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
  let irState = BuildIRState {
        buildIRLocal = IR.emptyIRBuilder,
        buildIRModule = genCtx.moduleState,
        buildIRClosures = genCtx.closureInfo }
      (result, BuildIRState{..}) = flip LS.runState irState $ act.unBuildIR
      genCtx' = genCtx{moduleState=buildIRModule}
  in ((result, SL.getSnocList buildIRLocal.builderBlocks), genCtx')

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
funValueType = A.StructureType False [A.ptr, A.ptr]

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

-- | Build a structure value out of dynamic operands.
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
  buildStructIR [closurePtr, entryFun]

-- | Create the closure pointer, load free variables into a context
-- arg and store it there, and then build the function value.
prepareFunValue :: MVar -> ClosureEnv -> A.Type -> BuildIR A.Operand
prepareFunValue funMVar cenv cenvTy = do
  contextVal <- createClosureEnv cenv cenvTy `named` "context"
  closurePtr <- mallocType cenvTy `named` "closurePtr"
  IR.store closurePtr 1 contextVal
  buildFunValueFor funMVar closurePtr

-- TODO: documentation
toLlvmType :: HasCallStack => Ty -> Gen A.Type
toLlvmType Ty{tyf=FunTy _ _ _ _} = pure funValueType
toLlvmType Ty{tyf=RefTy _ _} = pure A.ptr
toLlvmType ty = do
  mvar <- case mvarForDataTy ty of
    Just mvar -> pure mvar
    Nothing -> throwError $ NotTyCon ty
  let name = mvarToName mvar
  typeDefs <- gets (.moduleState.builderTypeDefs)
  case Map.lookup name typeDefs of
    Just ty -> pure ty
    Nothing -> do
      sdt <- lookupSpecDataType mvar
      genType mvar sdt

-- | Normally when we convert a type to an LLVM type,
-- we avoid using any opaque named types. This helps
-- us when calculating the sizes of types for enums.
--
-- However, inside the IR generation we can't access
-- that code because it needs the full `Gen` monad.
-- So instead we use an opaque type.
opaqueTypeFor :: Ty -> A.Type
opaqueTypeFor Ty{tyf=FunTy _ _ _ _} = funValueType
opaqueTypeFor Ty{tyf=RefTy _ _} = A.ptr
opaqueTypeFor ty = case mvarForDataTy ty of
  Nothing -> error "shouldn't be possible"
  Just mvar -> A.NamedTypeReference $ mvarToName $ mvar

-- | Emits an llvm type definition into the module.
--
-- Convenience wrapper for `emitDefn`.
emitLlvmType :: MVar -> A.Type -> Gen ()
emitLlvmType mvar ty = do
  D.traceM $ "adding type " <> show mvar <> " is " <> show ty
  void $ typedef (mvarToName mvar) (Just ty)
  -- TODO: remove
  -- test <- typeForName (mvarToName mvar)
  -- D.traceM $ "stored: " <> show test

-- | Generate and emit the type if it doesn't already exist.
--
-- Returns the full type data.
genType :: HasCallStack => MVar -> SpecDataType -> Gen A.Type
genType mvar sdt = do
  typeDefs <- gets (.moduleState.builderTypeDefs)
  case Map.lookup (mvarToName mvar) typeDefs of
    Just ty -> pure ty
    Nothing -> case sdt of
      SpecStruct con mems -> genStruct mems >>= def mvar
      -- for the enums, we'll generate a type for each individual
      -- constructor and then do bitcasts.
      SpecEnum cons -> do
        conTys <- traverse genStruct $ M.elems cons
        maxSize <- maximum <$> traverse getTypeSize conTys
        let payloadType = A.VectorType (fromIntegral maxSize) A.i8
            enumTy = A.StructureType False $ [A.i8, payloadType]
        -- Here we're creating types for each constructor that look like
        -- { i8, ...rest }
        forM_ (M.toList cons) \(con, mems) -> do
          DT.traceM $ "!enum mems: " <> show mems
          memTys <- traverse toLlvmType mems
          let conTy = A.StructureType False $ A.i8:memTys
          emitLlvmType (mangleDataCon mvar $ Var con) conTy
        def mvar enumTy
      SpecBuiltIn b -> case b of
        -- For these, we never need to generate a structure, so we just
        -- return the representative type.
        SpecString -> pure A.ptr
        SpecI64 -> pure A.i64
  where
  def mvar ty = emitLlvmType mvar ty $> ty
  genStruct :: [Ty] -> Gen A.Type
  genStruct mems = do
    DT.traceM $ "!mems: " <> show mems
    memTys <- traverse toLlvmType mems
    pure $ A.StructureType False memTys

-- | Build the opaque type representing a data constructor case.
enumConType :: MVar -> Var -> A.Type
enumConType dtMVar conVar = A.NamedTypeReference $
  mvarToName $ mangleDataCon dtMVar conVar

-- | Convert the closure usage annotations on a type into a
-- llvm type.
closureUseTy :: HasCallStack => ClosureUse Ty -> Gen A.Type
closureUseTy use = case use of
  Moved ty -> toLlvmType ty
  _ -> pure A.ptr

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
  forM_ (zip [0..] $ M.keys cenv.envMap) \(i,v) -> do
    val <- IR.extractValue value [i]
    introVar v val

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
mkClosureType :: [A.Type] -> A.Type
mkClosureType fields = A.StructureType False $ A.i32:fields

-- | If the closure environment is empty, for right now
-- we just trust llvm to optimize away the empty type.
closureEnvToType :: ClosureEnv -> Gen A.Type
closureEnvToType cenv = mkClosureType
  <$> traverse closureUseTy (M.elems cenv.envMap)

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
    let impos' = D.trace "referencing impos" impos
        jumps' = D.trace "jumps" jumps
    IR.switch closureArgCount impos' jumps'

    impos <- IR.block `named` "impossible1"
    addr <- IR.alloca fastRetTy Nothing 1
    val <- IR.load fastRetTy addr 1
    IR.ret val
    -- IR.unreachable

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
      entryBlocks' = entryBlocks <&> \(A.BasicBlock n a b) ->
        A.BasicBlock (D.trace ("block: " <> show n) n) a b
  D.traceM $ "entryBlocks: " <> show entryBlockNames
  emitDefn $ A.GlobalDefinition $ baseFunctionDefaults
    { AG.name = mvarToName $ mangleEntryFun funMVar
    , AG.parameters =
      ([ A.Parameter A.ptr "oldClosurePtr" []
        , A.Parameter A.ptr "stackArgs" []
        , A.Parameter A.i32 "stackArgCount" []
        , A.Parameter A.ptr "returnPtr" []
        ], False)
    , AG.basicBlocks = entryBlocks'
    , AG.returnType = funValueType
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
mkRecContextName :: Var -> A.Name
mkRecContextName (Var txt) = A.Name $ textToSBS $ txt <> ".context"

-- | Introduce a new local variable.
--
-- Updates the table of fresh names in the IR.
introVarName :: Var -> BuildIR A.Name
introVarName (Var txt) = IR.freshName $ textToSBS txt

-- | Takes a variable and a value and returns a pointer to
-- that value allocated on the stack.
introVar :: Var -> A.Operand -> BuildIR A.Operand
introVar var value = do
  name <- introVarName var
  t <- typeOf value
  addNamedInstr name $ A.Alloca t Nothing 1 []
  let loc = A.LocalReference A.ptr name
  IR.store loc 1 value
  pure loc

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
      nameCount = fromMaybe 0 $ Map.lookup rawName usedNames
      name = rawName <> fromString ("_" <> show nameCount)
  pure $ A.Name name

-- | A predicate determining whether a type is allocated
-- on the stack or not.
isOnStack :: Ty -> Bool
isOnStack ty = case ty.tyf of
  FunTy _ _ _ _ -> False
  RefTy _ _ -> False
  _ -> True

-- | Uses `localVarName` to build a local reference operand.
--
-- `onStack` indicates whether or not to load the variable from the
-- stack. If it's true, the variable is a pointer to the passed type.
-- If it's false, the variable is the passed type.
localVarOp :: Var -> Bool -> A.Type -> BuildIR A.Operand
localVarOp var onStack llvmTy = do
  name <- localVarName var
  if onStack
    then do
      let varPtr = A.LocalReference A.ptr name
      IR.load llvmTy varPtr 1
    else pure $ A.LocalReference llvmTy name

-- | Build a structure containing all free variables in a closure.
buildClosureEnv :: ClosureEnv -> BuildIR A.Operand
buildClosureEnv cenv = traverse go (M.toList cenv.envMap) >>= buildStructIR
  where
  go (var, Moved ty) = localVarOp var True $ opaqueTypeFor ty
  go (var, _) = localVarOp var False A.ptr

-- | Generate the LLVM IR for expressions.
genIR :: A.Type -> SpecIR -> BuildIR A.Operand
genIR cenvTy = go where
  -- | Where we handle all of the IR cases.
  go :: SpecIR -> BuildIR A.Operand
  go expr = case expr.specf of
    ClosureSF funMVar cenv -> do
      cenvOp <- buildClosureEnv cenv
      closurePtr <- buildClosurePtr [cenvOp]
      buildFunValueFor funMVar closurePtr
    RecClosureSF funMVar contextVar -> do
      let cenvName = mkRecContextName contextVar
          cenvOp = A.LocalReference cenvTy $ cenvName
      closurePtr <- buildClosurePtr [cenvOp]
      buildFunValueFor funMVar closurePtr
    AppSF funExpr args -> do
      argOps <- traverse go args
      case funExpr.specf of
        ClosureSF funMVar cenv -> do
          cenvOp <- buildClosureEnv cenv
          knownCall funMVar cenvOp argOps
        RecClosureSF funMVar contextVar -> do
          let cenvName = mkRecContextName contextVar
              cenvOp = A.LocalReference cenvTy $ cenvName
          knownCall funMVar cenvOp argOps
        _ -> do
          let retTy = opaqueTypeFor expr.ty
              -- if it's a bare function type we know we're dropping it.
              isDropped = case funExpr.ty.tyf of
                FunTy _ _ _ _ -> True
                _ -> False
          funValRaw <- go funExpr
          funVal <- case funExpr.ty.tyf of
            FunTy _ _ _ _ -> pure funValRaw
            RefTy _ Ty{tyf=FunTy _ _ _ _} -> IR.load funValueType funValRaw 1
            _ -> error "should only be a function or function ref"
          result <- funValCall retTy funVal argOps
          when isDropped $ freeClosurePtrIn funVal
          pure result
    VarSF var -> localVarOp var (isOnStack expr.ty) $ opaqueTypeFor expr.ty
    CopySF var -> localVarOp var False A.ptr
    DropSF svar varTy body -> do
      case varTy.tyf of
        FunTy Many _ _ _ -> do
          varOp <- localVarOp svar.var False funValueType
          freeClosurePtrIn varOp
        RefTy _ _ -> pure ()
        _ -> error "shouldn't be able to drop this"
      go body
    LetSF svar t1 t2 -> do
      t1Val <- go t1
      introVar svar.var $ t1Val
      -- NOTE: in the future I can probably use the lifetime intrinsics to
      -- start and end the alloc lifetime around `go t2`.
      go t2
    RefSF var -> localVarOp var False A.ptr
    StructConSF dtMVar args -> traverse go args >>= buildStructIR
    EnumConSF tagValue dtMVar conVar args -> do
      let rawEnumTy = A.NamedTypeReference $ mvarToName dtMVar
      argOps <- traverse go args
      conVal <- buildStructIR $ (IR.int8 tagValue):argOps
      enumLoc <- IR.alloca rawEnumTy Nothing 1
      IR.store enumLoc 1 conVal
      IR.load rawEnumTy enumLoc 1
    CaseSF t1 branches -> mdo
      let getConTxt (CaseBranch svar _ _) = svar.var.name
          orderedBranches = sortBy (compare `on` getConTxt) branches
      (enumLoc, conTag, dtMVar) <- case t1.ty.tyf of
        RefTy _ dtTy -> do
          let dtMVar' = fromJust $ mvarForDataTy dtTy
              rawEnumTy = A.NamedTypeReference $ mvarToName dtMVar'
          enumLoc' <- go t1
          conTagLoc <- indexStructPtr rawEnumTy enumLoc' 0
          conTag' <- IR.load A.i8 conTagLoc 1
          pure (enumLoc', conTag', dtMVar')
        _ -> do
          -- NOTE: I think I have to do this really annoying bitcast thing right now.
          -- hopefully I can find optimization passes or something to avoid this. Or
          -- a bitcast that works on structures.
          let dtMVar' = fromJust $ mvarForDataTy t1.ty
          rawEnumVal <- go t1
          conTag' <- IR.extractValue rawEnumVal [0]
          rawEnumTy <- typeOf rawEnumVal
          enumLoc' <- IR.alloca rawEnumTy Nothing 1
          IR.store enumLoc' 1 rawEnumVal
          pure (enumLoc', conTag', dtMVar')
      IR.switch conTag impossible2 $ dests <&> \(tagVal, label,_) -> (tagVal, label)
      dests <- forM (zip [0..] orderedBranches) \(i, CaseBranch conSVar memSVars body) -> do
        conLabel <- IR.block `named` textToSBS conSVar.var.name
        let conTy = enumConType dtMVar conSVar.var
        conVal <- IR.load conTy enumLoc 1
        forM_ (zip [0..] memSVars) \(i, SVar{var}) -> do
          mem <- IR.extractValue conVal [i]
          introVar var mem
        conResult <- go body
        IR.br caseEnd
        pure (A.Int 8 i, conLabel, conResult)
      impossible2 <- IR.block `named` "impossible2"
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
      forM_ (zip [0..] memSVars) \(i, SVar{var}) -> do
        mem <- IR.extractValue structVal [i]
        introVar var mem
      go t2
    LiteralSF lit -> error "TODO"

-- | Generate the entry and fast function.
genFun :: HasCallStack => MVar -> ClosureEnv -> (Maybe SVar) -> [(SVar, Ty, Mult)] -> SpecIR -> Gen ClosureInfo
genFun funMVar cenv mbFix params body = do
  D.traceM $ "!genFun: " <> show funMVar
  cim <- gets (.closureInfo)
  case M.lookup funMVar cim of
    Just ci -> pure ci
    Nothing -> do
      -- DT.traceM $ "!body: " <> show body
      DT.traceM $ "!body.ty: " <> show body.ty
      fastRetTy <- toLlvmType body.ty
      ctxTy <- closureEnvToType cenv
      llvmParams <- traverse mkLlvmParam params
      let ctxOp = A.LocalReference ctxTy contextName
      (_, fastBlocks) <- runBuildIR do
        _entry <- IR.block `named` "entry"
        case mbFix of
          Nothing -> pure ()
          Just SVar{var} -> do
            buildFunValueFor funMVar ctxOp
            error "TODO create function value that calls this function and store it"
        extractClosureEnv cenv ctxOp
        genIR ctxTy body
      let fastParams = (A.Parameter ctxTy contextName []):llvmParams
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
  contextName = case mbFix of
    Nothing -> A.Name "nothing.context"
    Just svar -> mkRecContextName svar.var
  mkLlvmParam (svar, ty, _) = do
    DT.traceM $ "!param ty: " <> show ty
    ty' <- toLlvmType ty
    pure $ A.Parameter ty' (varToName svar.var) []

-- | Declare the external functions for all the important calls like malloc.
llvmDeclarations :: Gen ()
llvmDeclarations = do
  void $ extern (A.Name "malloc") [A.i32] A.ptr
  void $ extern (A.Name "free") [A.ptr] A.void

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
  SpecDataType sdt -> void $ genType mvar sdt
  SpecFun cenv mbFix args bodyIR -> void $ genFun mvar cenv mbFix args bodyIR

-- | Generate a list of LLVM definitions.
--
-- Takes a map of declarations and a list of declarations in the correct load order.
runGen :: M.HashMap MVar SpecDecl -> [(MVar, SpecDecl)]
  -> I.Context -> A.DataLayout -> IO (Either GenErr [A.Definition])
runGen specDeclMap specDecls llvmCtx dl = do
  forM_ specDecls \(v, sd) -> do
    print $ show v <> ": " <> show sd
  let genCtx = GenCtx {
        llvmContext=llvmCtx,
        dataLayout=dl,
        specDecls=specDeclMap,
        moduleState=emptyModuleBuilder,
        closureInfo=M.empty
        }
      f = fmap \(_,ctx) -> SL.unSnocList $ ctx.moduleState.builderDefs
      act = do
        llvmDeclarations
        traverse_ (uncurry genDecl) $ reverse specDecls
  fmap f $ runExceptT $ flip runStateT genCtx $ unGen act
