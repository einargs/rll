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
import Data.Foldable (traverse_)
import Data.Functor (($>), (<&>))
import Debug.Trace qualified as D

import LLVM.Internal.FFI.DataLayout (getTypeAllocSize)
import LLVM.Internal.DataLayout (withFFIDataLayout)
import LLVM.Internal.Coding (EncodeM(..))
import LLVM.Internal.EncodeAST (EncodeAST, runEncodeAST)
import LLVM.IRBuilder.Internal.SnocList qualified as SL
import LLVM.AST.Typed (typeOf)
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
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

-- | This is the closure pointer and then function pointer.
funValueType :: A.Type
funValueType = A.StructureType False [A.ptr, A.ptr]

-- | Get the closure pointer from the function value.
getClosurePtr :: A.Operand -> BuildIR A.Operand
getClosurePtr op = IR.extractValue op [0]

-- | Get the slow function pointer from the function value.
getFunctionPtr :: A.Operand -> BuildIR A.Operand
getFunctionPtr op = IR.extractValue op [1]

-- | This generates the type for a slow function based
-- on the return type. A slow function is what unpacks
-- arguments from the closure to call the main function.
unpackingFunType :: A.Type -> A.Type
unpackingFunType retTy = A.FunctionType retTy args False
  where args = [funValueType, A.ptr, A.i32]

-- | Build a function value from a closure pointer and function pointer.
buildFunValue :: A.Operand -> A.Operand -> BuildIR A.Operand
buildFunValue closurePtr funPtr = do
  let zeroed = A.ConstantOperand $ A.AggregateZero funValueType
  tmp <- IR.insertValue zeroed closurePtr [0]
  IR.insertValue tmp funPtr [1]

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
addNamedInstr name instr = modifyBlock \bb -> bb
  { partialBlockInstrs = bb.partialBlockInstrs `SL.snoc` (name A.:= instr)
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

-- TODO: thing to convert a closureUse into an operand that
-- builds a structure.

-- | If the closure environment is empty, for right now
-- we just trust llvm to optimize away the empty type.
closureEnvToType :: ClosureEnv -> Gen A.Type
closureEnvToType cenv = A.StructureType False
  <$> traverse closureUseTy (M.elems cenv.envMap)

-- | Custom defaults for all functions.
baseFunctionDefaults :: A.Global
baseFunctionDefaults = AG.functionDefaults {
  AG.functionAttributes = funAttr}
  where
    funAttr :: [Either A.GroupID A.FunctionAttribute]
    funAttr = [Right A.NoUnwind]

type BuildIR = IRBuilderT ModuleBuilder

-- | Run the IR builder with the module builder info.
--
-- Because Gen has IO in it, we can't use recursive do if we run
-- `IRBuilderT Gen`. So we run a pure version and then update
-- `Gen` with any changes to the module builder state.
runBuildIR :: BuildIR a -> Gen (a, [A.BasicBlock])
runBuildIR act = state \genCtx ->
  let (result, modState') = run genCtx.moduleState emptyIRBuilder act
      genCtx' = genCtx{moduleState=modState'}
  in (result, genCtx')
  where
  run modState irState =
    flip runState modState . unModuleBuilderT . runIRBuilderT irState

-- | Generate a call to the given function value with the
-- argument list.
genCall :: A.Type -> A.Operand -> [A.Operand] -> BuildIR A.Operand
genCall retTy funValue argOps = do
  funPtr <- getFunctionPtr funValue
  let args = (,[]) <$> (funValue:argOps)
  IR.call (unpackingFunType retTy) funptr args

-- | Use `GEP` to index into a field of a struct in a pointer.
indexStructPtr :: A.Type -> A.Operand -> Integer -> BuildIR A.Operand
indexStructPtr ty ptr idx = IR.gep ty ptr [IR.int32 0, IR.int32 idx]

-- | Generate the closure type and the structure of the pushed args
-- on the stack for the number of already applied arguments and
-- arguments already on the stack.
closureAndStackFor :: [A.Type] -> Integer -> Integer -> (A.Type, A.Type)
closureAndStackFor args inClosure onStack =
  (st closure, st $ take (fromInteger onStack) stack)
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

genFun :: MVar -> ClosureEnv -> (Maybe SVar) -> [(SVar, Ty, Mult)] -> SpecIR -> Gen ClosureInfo
genFun funMVar cenv mbFix params body = do
  cenvTys <- traverse closureUseTy cenv.envMap
  cim <- gets (.closureInfo)
  case M.lookup funMVar cim of
    Just ci -> pure ci
    Nothing -> do
      llvmRetTy <- toLlvmType body.ty
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
            , AG.returnType = llvmRetTy
            }
          llvmArgTys = fastParams <&> \(A.Parameter ty _ _) -> ty
          fastFunTy = A.FunctionType llvmRetTy llvmArgTys False
          fastFunRef = A.ConstantOperand $ A.GlobalReference fastName
      (_, slowBlocks) <- runBuildIR mdo
        -- this is the number of already applied arguments stored in our
        -- closure.
        oldClosurePtr <- getClosurePtr funValue
        funPtr <- getFunctionPtr funValue
        closureArgCount <- IR.load A.i32 oldClosurePtr 1 `named` "closureArgCount"
        IR.switch closureArgCount impossible jumps
        jumps <- forM [0..(arity-1)] \i -> mdo
          let argsLeft = arity - i
              -- The multiplicity of the closure pointer.
              (_, _, closureMult) = params !! (fromInteger i-1)
              handleOldClosure = case closureMult of
                -- If the closure is single use, we clean up the pointer.
                Single -> freePtr oldClosurePtr
                -- If it's multi-use, it'll be cleaned up when we drop it.
                Many -> pure ()
          label <- block `named` "arg"
          -- TODO: I think I need to use a `phi` to grab `argCount`.
          -- Check our pushed args to see if there are enough.
          IR.switch stackArgCount makeCall $ stackJumps
          -- 1. If there aren't enough, we copy from the stack to a new closure.
          stackJumps <- forM [1..argsLeft-1] \numArgsOnStack -> do
            -- NOTE: in the future I might redo this as something that falls through
            -- to reduce code size? Not sure how I'd handle allocating the new thing though.
            let (oldClosureTy, stackArgsTy) = closureAndStackFor llvmArgTys i numArgsOnStack
                newClosureTy = closureTyFor llvmArgTys (i+numArgsOnStack)
            label <- block `named` "stackArg"
            newClosurePtr <- mallocType newClosureTy
            let copyArgsFromTo :: [Integer] -> A.Type -> A.Operand -> BuildIR ()
                copyArgsFromTo toIdxs fromTy fromPtr = do
                  let fromFields = getStructFields fromTy
                  forM_ (zip3 [0..] fromFields toIdxs) \(fromIdx, argTy, toIdx) -> do
                    fromArgPtr <- indexStructPtr fromTy fromPtr fromIdx `named` "fromArgPtr"
                    toArgPtr <- indexStructPtr newClosureTy newClosurePtr toIdx `named` "toArgPtr"
                    arg <- IR.load argTy fromArgPtr 1 `named` "arg"
                    IR.store toArgPtr 1 arg
            copyArgsFromTo [0..i-1] oldClosureTy oldClosurePtr
            copyArgsFromTo [i..i+numArgsOnStack-1] stackArgsTy stackArgs
            handleOldClosure
            newFunValue <- buildFunValue newClosurePtr funPtr
            IR.ret newFunValue
            pure (A.Int 32 numArgsOnStack, label)
          -- 2. If there are enough args, we call the fast function.
          makeCall <- block `named` "makeCall"
          let (oldClosureTy, stackArgsTy) = closureAndStackFor llvmArgTys i argsLeft
              loadArgsFrom :: A.Type -> A.Operand -> BuildIR [(A.Operand, [A.ParameterAttribute])]
              loadArgsFrom fromTy fromPtr =
                forM (zip [0..] $ getStructFields fromTy) \(idx, argTy) -> do
                  fromArgPtr <- indexStructPtr fromTy fromPtr idx `named` "fromArgPtr"
                  arg <- IR.load argTy fromArgPtr 1 `named` "arg"
                  pure (arg, [])
          callAgain <- IR.phi [(IR.bit )]
          loadedClosureArgs <- loadArgsFrom oldClosureTy oldClosurePtr
          loadedStackArgs <- loadArgsFrom stackArgsTy stackArgs
          result <- IR.call fastFunTy fastFunRef $ loadedClosureArgs <> loadedStackArgs
          handleOldClosure
          -- 3. We check the return type to see if we need to generate
          -- code for handling extra arguments.
          case body.ty.tyf of
            -- a. If the return type can be a function, we need to deal with possible
            -- extra arguments.
            FunTy _ _ _ _ -> mdo
              -- TODO: check if we have extra args
              cond <- IR.icmp IP.UGT stackArgCount $ IR.int32 argsLeft
              IR.br cond immediateReturn secondCall
              immediateReturn <- IR.block `named` "immediateReturn"
              IR.ret result
              secondCall <- IR.block `named` "secondCall"
              -- we use GEP to calculate the right offset and then
              -- generate the calling code with the remaining arguments
              -- and offset stack pointer.
              let secondFunTy = unpackingFunType 
              nextStackArgs <- IR.gep stackArgsTy stackArgs [IR.int32 1] `nextStackArgs`
              -- TODO
            -- b. If the return type is not a function, we know that we can
            -- always return the result.
            _ -> IR.ret result
          pure $ (A.Int 32 i, label)
        impossible <- block `named` "impossible"
        IR.unreachable
      let slowDef = baseFunctionDefaults
            { AG.name = mvarToName funMVar
            , AG.parameters =
              ([ A.Parameter funValueType "funValue" []
               , A.Parameter A.ptr "stackArgs" []
               , A.Parameter A.i32 "stackArgCount" []
               ], False)
            , AG.basicBlocks = slowBlocks
            , AG.returnType = llvmRetTy
            }
          genClosure = do
            mallocType $ error "build closure type"
      emitDefn $ A.GlobalDefinition fastDef
      emitDefn $ A.GlobalDefinition slowDef
      let closureInfo = ClosureInfo $ error "TODO"
      addClosureInfo funMVar closureInfo
      pure closureInfo
  where
  contextName = A.Name "fun.context"
  funValue = A.LocalReference funValueType "funValue"
  stackArgs = A.LocalReference A.ptr "stackArgs"
  stackArgCount = A.LocalReference A.i32 "stackArgCount"
  mkLlvmParam (svar, ty, _) = do
    ty' <- toLlvmType ty
    pure $ A.Parameter ty' (varToName svar.var) []
  arity :: Integer
  arity = toInteger $ length params
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
