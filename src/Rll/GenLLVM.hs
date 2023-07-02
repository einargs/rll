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
import Control.Monad.State (MonadState(..), runState, StateT, runStateT, modify', gets, state)
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Word
import Data.Map qualified as Map
import Data.HashMap.Strict qualified as M
import Control.Monad (void, forM_, forM)
import Data.Foldable (traverse_, foldlM)
import Data.Functor (($>), (<&>))
import GHC.Stack (HasCallStack)
import Debug.Trace qualified as D

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
import LLVM.AST.ParameterAttribute qualified as A
import LLVM.AST.IntegerPredicate qualified as IP
import LLVM.AST.Instruction qualified as A
import LLVM.AST.Constant qualified as A
import LLVM.AST qualified as A
import LLVM.AST.Type qualified as A

-- | Information about how to build the closure object.
data ClosureInfo = ClosureInfo
  { returnType :: A.Type
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
    let (a, s) = runState m ctx.moduleState
    in (a, ctx{moduleState=s})

-- | Get the closure info for a function.
--
-- Generates the function if it doesn't already exist.
closureInfoFor :: MVar -> Gen ClosureInfo
closureInfoFor var = do
  m <- gets (.closureInfo)
  case M.lookup var m of
    Just i -> pure i
    Nothing -> do
      sd <- gets (.specDecls)
      case M.lookup var sd of
        Just (SpecFun cenv mbFix params body) ->
          genFun var cenv mbFix params body
        _ -> throwError $ NoSpecFunNamed var

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
lookupSpecDataType :: MVar -> Gen SpecDataType
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

-- | Since all of our types will eventually be generated, we can just
-- refer to them.
mvarForTy :: Ty -> Gen MVar
mvarForTy ty = case parseTyCon ty of
  Nothing -> throwError $ NotTyCon ty
  Just (v, tys) -> pure $ mangleDataType v.name tys

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
getEntryFunPtr :: A.Operand -> BuildIR A.Operand
getEntryFunPtr op = IR.extractValue op [1]

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

toLlvmType :: Ty -> Gen A.Type
toLlvmType (Ty _ (FunTy _ _ _ _)) = pure funValueType
toLlvmType ty = do
  mvar <- mvarForTy ty
  let name = mvarToName mvar
  typeDefs <- gets (.moduleState.builderTypeDefs)
  case Map.lookup name typeDefs of
    Just ty -> pure ty
    Nothing -> do
      sdt <- lookupSpecDataType mvar
      genType mvar sdt

-- | Emits an llvm type definition into the module.
--
-- Convenience wrapper for `emitDefn`.
emitLlvmType :: MVar -> A.Type -> Gen ()
emitLlvmType mvar ty = do
  D.traceM $ "adding type " <> show mvar <> " is " <> show ty
  typedef (mvarToName mvar) (Just ty)
  test <- typeForName (mvarToName mvar)
  D.traceM $ "stored: " <> show test

-- | Generate and emit the type if it doesn't already exist.
--
-- Returns the full type data.
genType :: MVar -> SpecDataType -> Gen A.Type
genType mvar sdt = do
  typeDefs <- gets (.moduleState.builderTypeDefs)
  case Map.lookup (mvarToName mvar) typeDefs of
    Just ty -> pure ty
    Nothing -> case sdt of
      SpecStruct con mems -> genStruct mvar mems
      -- for the enums, we'll generate a type for each individual
      -- constructor and then do bitcasts.
      SpecEnum cons -> do
        conTys <- traverse (uncurry genCon) $ M.toList cons
        maxSize <- maximum <$> traverse getTypeSize conTys
        let payloadType = A.VectorType (fromIntegral maxSize) A.i8
            enumTy = A.StructureType False $ [A.i32, payloadType]
        def mvar enumTy
      SpecBuiltIn b -> case b of
        -- For these, we never need to generate a structure, so we just
        -- return the representative type.
        SpecString -> pure A.ptr
        SpecI64 -> pure A.i64
  where
  def mvar ty = emitLlvmType mvar ty $> ty
  genCon :: Text -> [Ty] -> Gen A.Type
  genCon con mems = genStruct (mangleDataCon mvar $ Var con) mems
  genStruct :: MVar -> [Ty] -> Gen A.Type
  genStruct mvar mems = do
    memTys <- traverse toLlvmType mems
    let structTy = A.StructureType False memTys
    def mvar structTy

-- | Convert the closure usage annotations on a type into a
-- llvm type.
closureUseTy :: ClosureUse Ty -> Gen A.Type
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
  forM_ vars \(i,n) ->
    addNamedInstr n $ A.ExtractValue value [i] []
  where
  vars = zip [0..] $ varToName <$> M.keys cenv.envMap

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

type BuildIR = IR.IRBuilderT ModuleBuilder

-- | Run the IR builder with the module builder info.
--
-- Because Gen has IO in it, we can't use recursive do if we run
-- `IRBuilderT Gen`. So we run a pure version and then update
-- `Gen` with any changes to the module builder state.
runBuildIR :: BuildIR a -> Gen (a, [A.BasicBlock])
runBuildIR act = state \genCtx ->
  let (result, modState') = run genCtx.moduleState IR.emptyIRBuilder act
      genCtx' = genCtx{moduleState=modState'}
  in (result, genCtx')
  where
  run modState irState =
    flip runState modState . unModuleBuilderT . IR.runIRBuilderT irState

-- | Generate a call to the given function value using the given
-- stack argument pointer.
genCallWithArgPtr :: A.Operand -> A.Operand -> A.Operand -> A.Operand -> BuildIR A.Operand
genCallWithArgPtr funValue returnPtr argCount argPtr = do
  closurePtr <- getClosurePtr funValue
  funPtr <- getEntryFunPtr funValue
  let args = (,[]) <$> [closurePtr, argPtr, argCount, returnPtr]
  IR.call entryFunType funPtr args

-- | Generate a call to the given function value with the
-- argument list.
--
-- We generate this kind of call when we know that we have fully saturated
-- all possible arguments.
--
-- `retTy` is the expected type after all of the arguments have been applied.
genCall :: A.Type -> A.Operand -> [A.Operand] -> BuildIR A.Operand
genCall retTy funValue argOps = do
  returnPtr <- IR.alloca retTy Nothing 1 `named` "returnPtr"
  argStruct <- buildStructIR argOps `named` "argStruct"
  argStructTy <- typeOf argStruct
  argPtr <- IR.alloca argStructTy Nothing 1 `named` "argPtr"
  let argCount = IR.int32 $ toInteger $ length argOps
  genCallWithArgPtr returnPtr funValue argCount argPtr

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
closureTyFor args i = A.StructureType False $ take (fromInteger i) args

-- | Generate the entry function for a function.
genEntryFun :: MVar -> Ty -> A.Type -> [A.Type] -> [Mult] -> Gen ()
genEntryFun funMVar fullReturnTy fastRetTy llvmArgs mults = do
  (_, entryBlocks) <- runBuildIR mdo
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
          -- The multiplicity of the closure pointer.
          closureMult = mults !! (fromInteger i-1)
          -- | Clean up the old closure pointer if necessary.
          handleOldClosure = case closureMult of
            -- If the closure is single use, we clean up the pointer.
            Single -> freePtr oldClosurePtr
            -- If it's multi-use, it'll be cleaned up when we drop it.
            Many -> pure ()
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
            stackArgConstant = IR.int32 numArgsOnStack
        label <- IR.block `named` "stackArg"

        -- Store the updated number of arguments in the closure.
        newClosurePtr <- mallocType newClosureTy
        newClosureArgCount <- IR.add closureArgCount stackArgConstant `named` "newClosureArgCount"
        IR.store newClosurePtr 1 newClosureArgCount

        let copyArgsFromTo :: Integer -> A.Type -> A.Operand -> Integer -> BuildIR ()
            copyArgsFromTo firstFromIdx fromTy fromPtr firstToIdx = do
              let fromFields = drop (fromInteger firstFromIdx) $ getStructFields fromTy
                  fields = zip3 [firstFromIdx..] fromFields [firstToIdx..]
              forM_ fields \(fromIdx, argTy, toIdx) -> do
                fromArgPtr <- indexStructPtr fromTy fromPtr fromIdx `named` "fromArgPtr"
                toArgPtr <- indexStructPtr newClosureTy newClosurePtr toIdx `named` "toArgPtr"
                arg <- IR.load argTy fromArgPtr 1 `named` "arg"
                IR.store toArgPtr 1 arg
        copyArgsFromTo 1 oldClosureTy oldClosurePtr 1 -- [0..i-1]
        copyArgsFromTo 0 stackArgsTy stackArgs i -- [i..i+numArgsOnStack-1]
        handleOldClosure
        newFunValue <- buildFunValueFor funMVar newClosurePtr `named` "newFunValue"
        returnOp newFunValue
        pure (A.Int 32 numArgsOnStack, label)
      -- 2. If there are enough args, we call the fast function.
      makeCall <- IR.block `named` "makeCall"
      let (oldClosureTy, stackArgsTy) = closureAndStackFor llvmArgs i argsLeft
          -- | Utility for loading the arguments from memory.
          loadArgsFrom :: Integer -> A.Type -> A.Operand -> BuildIR [(A.Operand, [A.ParameterAttribute])]
          loadArgsFrom startIdx fromTy fromPtr = do
            let fields = drop (fromInteger startIdx) $ getStructFields fromTy
            forM (zip [startIdx..] fields) \(idx, argTy) -> do
              fromArgPtr <- indexStructPtr fromTy fromPtr idx `named` "fromArgPtr"
              arg <- IR.load argTy fromArgPtr 1 `named` "arg"
              pure (arg, [])
      loadedClosureArgs <- loadArgsFrom 1 oldClosureTy oldClosurePtr
      loadedStackArgs <- loadArgsFrom 0 stackArgsTy stackArgs
      -- call the fast function with the loaded arguments
      result <- IR.call fastFunTy fastFunRef $ loadedClosureArgs <> loadedStackArgs
                `named` "result"
      handleOldClosure

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
          restStackArgs <- IR.gep stackArgsTy stackArgs [IR.int32 1] `named` "restStackArgs"
          restStackArgCount <- IR.sub 
          genCallWithArgPtr result returnPtr nextStackArgs
          -- check if the next closure would be single or multi-use.
          case mult of
            -- If it's multi-use we then free it ourselves since there's no
            -- drop to free it.
            Many -> do
              secondClosure <- getClosurePtr result
              freePtr secondClosure
            Single -> pure ()
          IR.retVoid
        -- b. If the return type is not a function, we know that we can
        -- always return the result.
        _ -> returnOp result
      pure $ (A.Int 32 $ fromInteger i, label)
    pure ()
  emitDefn $ baseFunctionDefaults
    { AG.name = mvarToName $ mangleEntryFun funMVar
    , AG.parameters =
      ([ A.Parameter A.ptr "oldClosurePtr" []
        , A.Parameter A.ptr "stackArgs" []
        , A.Parameter A.i32 "stackArgCount" []
        , A.Parameter A.ptr "returnPtr" []
        ], False)
    , AG.basicBlocks = entryBlocks
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

genFun :: MVar -> ClosureEnv -> (Maybe SVar) -> [(SVar, Ty, Mult)] -> SpecIR -> Gen ClosureInfo
genFun funMVar cenv mbFix params body = do
  cenvTys <- traverse closureUseTy cenv.envMap
  cim <- gets (.closureInfo)
  case M.lookup funMVar cim of
    Just ci -> pure ci
    Nothing -> do
      fastRetTy <- toLlvmType body.ty
      ctxTy <- closureEnvToType cenv
      llvmParams <- traverse mkLlvmParam params
      (_, fastBlocks) <- runBuildIR do
        extractClosureEnv cenv $ A.LocalReference ctxTy contextName
        genIR body
      let fastParams = (A.Parameter ctxTy contextName []):llvmParams
          fastName = mvarToName $ mangleFastFun funMVar
          fastDef = baseFunctionDefaults
            { AG.name = fastName
            , AG.parameters = (fastParams, False) -- False means not varargs
            , AG.basicBlocks = fastBlocks
            , AG.returnType = fastRetTy
            }
          llvmArgTys = fastParams <&> \(A.Parameter ty _ _) -> ty
          genClosure = do
            mallocType $ error "build closure type"
      emitDefn $ A.GlobalDefinition fastDef
      let closureInfo = ClosureInfo $ error "TODO"
      addClosureInfo funMVar closureInfo
      pure closureInfo
  where
  contextName = A.Name "fun.context"
  mkLlvmParam (svar, ty, _) = do
    ty' <- toLlvmType ty
    pure $ A.Parameter ty' (varToName svar.var) []
  -- | We generate all of the IR here so that we can access `mbFixName`.
  genIR :: SpecIR -> BuildIR A.Operand
  genIR exp = error "unimplemented"

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
  SpecFun cenv mbFix args bodyIR -> pure () -- not yet implemented

runGen :: M.HashMap MVar SpecDecl -> I.Context -> A.DataLayout -> IO (Either GenErr [A.Definition])
runGen specDecls llvmCtx dl = do
  forM_ (M.toList specDecls) \(v, sd) -> do
    print $ show v <> ": " <> show sd
  let genCtx = GenCtx {
        llvmContext=llvmCtx,
        dataLayout=dl,
        specDecls=specDecls,
        moduleState=emptyModuleBuilder,
        closureInfo=M.empty
        }
      f = fmap \(_,ctx) -> SL.unSnocList $ ctx.moduleState.builderDefs
      act = do
        llvmDeclarations
        traverse_ (uncurry genDecl) $ M.toList specDecls
        let unitTy = A.NamedTypeReference "Two%"
        global "testG" unitTy $ A.Struct Nothing False []
  fmap f $ runExceptT $ flip runStateT genCtx $ unGen act
