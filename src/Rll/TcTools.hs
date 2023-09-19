-- | Tools for type checking.
--
-- Basically, as much type checking stuff that can be moved into
-- here without needing to import `Core.hs`.
module Rll.TcTools
  ( addDataType, addModuleFun
  , alterBorrowCount, addVar, deleteVar, withKind
  , endVarScopes
  , kindOf, sanityCheckType
  , verifyCtxSubset
  , incrementLts, decrementLts, variablesBorrowing
  , dropVar, useRef, incRef
  , rawIndexTyVars, indexTyVars, indexTyVarsInTm
  ) where

import Rll.Ast
import Rll.Context
import Rll.TypeError
import Rll.TcMonad
import Rll.LtSet
import Rll.TypeSub

import Control.Monad (unless, when, forM_, forM)
import Data.Text (Text)
import Data.Text qualified as T
import qualified Data.HashMap.Strict as M
import Control.Arrow (first, second)
import Data.List (foldl')
import Data.Maybe (mapMaybe)
import Control.Exception (assert)

-- | Get the kind of the type. Also checks that the type is well formed.
kindOf :: Ty -> Tc Kind
kindOf ty@Ty{span=s, tyf} = case tyf of
  TyVar tv -> lookupKind tv s
  TyCon name -> lookupDataType name s >>= \case
    StructType _ tyParams _ _ -> pure $ kindFrom tyParams
    BuiltInType b -> pure $ case b of
      BuiltInI64 -> TyKind
      BuiltInString -> TyKind
    EnumType _ tyParams _ _ -> pure $ kindFrom tyParams
  LtOf v -> lookupEntry v s *> pure LtKind
  FunTy _ aTy lts bTy -> do
    kindCheck TyKind aTy
    kindCheck LtKind lts
    kindCheck TyKind bTy
    pure TyKind
  LtJoin tys -> do
    forM_ tys (kindCheck LtKind)
    pure LtKind
  RefTy lt aTy -> do
    kindCheck LtKind lt
    kindCheck TyKind aTy
    pure TyKind
  Univ _ lts _ tyVarKind bodyTy -> do
    kindCheck LtKind lts
    withKind tyVarKind $ kindCheck TyKind bodyTy
    pure TyKind
  TyApp ty1 ty2 -> do
    k1 <- kindOf ty1
    case k1 of
      TyOpKind ak bk -> do
        kindCheck ak ty2
        pure bk
      _ -> throwError $ IsNotTyOp k1 $ getSpan ty1
  where
    kindFrom :: [TypeParam] -> Kind
    kindFrom tyParams = foldr TyOpKind TyKind $ (.kind) <$> tyParams

-- | Check that the type has the given kind and that the type
-- is overall well formed.
kindCheck :: Kind -> Ty -> Tc ()
kindCheck k ty = do
  k' <- kindOf ty
  unless (k==k') $ do
    throwError $ ExpectedKind k k' $ getSpan ty

-- | Used to implement checkForRank2 and `checkForPoly`.
checkTyForm :: (Ty -> TyErr) -> Bool -> Ty -> Tc ()
checkTyForm err = go False where
  go polyInRet activateErr ty@Ty{tyf} = case tyf of
    FunTy _ aTy lts bTy ->
      go polyInRet True aTy *> go polyInRet activateErr bTy
    Univ _ lts _ tyVarKind bodyTy
      | activateErr -> throwError $ err ty
      | polyInRet -> throwError $ NoPolyInRet ty
      | otherwise -> f bodyTy
    _ -> mapM_ f tyf
    where f = go polyInRet activateErr

-- | Throw an error if the type is a rank 2 type.
checkForRank2 :: Ty -> Tc ()
checkForRank2 = checkTyForm NoRank2 False

-- | Check for polymorphic functions in a data type.
--
-- We call this on the functions that are added to the terms,
-- not the individual member types.
checkForPoly :: Ty -> Tc ()
checkForPoly = checkTyForm NoPolyInField False

-- | Check that the type is a proper type and isn't rank 2.
sanityCheckType :: Ty -> Tc ()
sanityCheckType ty = do
  kindCheck TyKind ty
  checkForRank2 ty

-- | Add a data type with the given name to the context.
addDataType :: Var -> DataType -> Tc ()
addDataType tyName dt = do
  ctx <- get
  (terms, s) <- case dt of
    EnumType _ tyArgs caseM s -> pure $ (f s tyArgs <$> M.toList caseM, s)
    StructType v tyArgs args s -> pure $ ([f s tyArgs (v,args)], s)
    BuiltInType _ -> throwError $
      CompilerLogicError "Cannot add a built-in type to the context" Nothing
  case M.lookup tyName ctx.dataTypes of
    Just _ -> throwError $ DataTypeAlreadyExists tyName s
    Nothing -> pure ()
  terms' <- forM terms \(v,ty) -> (\ty -> (v, (dt,ty))) <$> indexTyVars ty
  forM_ terms' \(v,_) -> case M.lookup v ctx.moduleDataCons of
    Just _ -> throwError $ DefAlreadyExists v s
    Nothing -> pure ()
  put $ ctx
    { moduleDataCons = foldl' (flip $ uncurry M.insert) ctx.moduleDataCons terms'
    , dataTypes = M.insert tyName dt ctx.dataTypes
    }
  forM_ terms' $ check . snd . snd
  where
    check ty = do
      kindCheck TyKind ty
      checkForPoly ty
    f :: Span -> [TypeParam] -> (Text, [Ty]) -> (Var, Ty)
    f s tyArgs (name, args) = (Var name, result) where
      finalTy = foldl' g (Ty s $ TyCon tyName) $ zip tyArgs [0..] where
        g base (TypeParam{name},i) = Ty s $ TyApp base (Ty s $ TyVar (MkTyVar name i))
      result = buildArgs s tyArgs $ buildTy s finalTy $ reverse args
    buildArgs :: Span -> [TypeParam] -> Ty -> Ty
    buildArgs s tyArgs body = foldr f body tyArgs where
      f (TypeParam{name, kind}) body = Ty s $ Univ Many (Ty s $ LtJoin []) (TyVarBinding name) kind body
    buildTy :: Span -> Ty -> [Ty] -> Ty
    buildTy s ty [] = ty
    buildTy s result [input] = Ty s $ FunTy Many input (Ty s $ LtJoin []) result
    buildTy s result (input:args) = buildTy s fTy args
      where fTy = Ty s $ FunTy Single input (Ty s $ LtJoin []) result

-- NOTE: abstract out the "insert if it doesn't already exist" pattern.

addModuleFun :: Span -> Var -> Ty -> Tc ()
addModuleFun s name ty = do
  ctx <- get
  let doesNotExistIn map =
        case M.lookup name map of
          Just _ -> throwError $ DefAlreadyExists name s
          Nothing -> pure ()
  doesNotExistIn ctx.moduleFuns
  put $ ctx {moduleFuns=M.insert name ty ctx.moduleFuns}

alterBorrowCount :: Int -> Var -> Span -> Tc ()
alterBorrowCount i v s = do
  -- TODO
  (sc,_) <- lookupEntry v s
  -- D.traceM $ "altering " <> show v <> " by " <> show i <> " from " <> show sc
  modify' $ onTermVars $ M.adjust (first (+i)) v
  when (sc + i < 0) $ do
    let ts :: Show a => a -> Text
        ts = T.pack . show
        msg = "subzero borrow count " <> ts (sc+i) <> " for " <> ts v
    throwError $ CompilerLogicError msg (Just s)
  -- where f' i = let i' = f i in if i' < 0 then T.trace ("less than zero for " <> show v) i' else i'

-- | Add a term variable to the context.
addVar :: Var -> Span -> Ty -> Tc ()
addVar v s ty = do
  ctx <- get
  case M.lookup v ctx.termVars of
    Just _ -> do
      def <- case M.lookup v ctx.varLocs of
        Nothing -> error "varLocs was not properly synched to varTerms"
        Just (def,_) -> pure def
      throwError $ VarAlreadyInScope v s def
    Nothing -> do
      -- NOTE: this may be redundant
      sanityCheckType ty
      put $ ctx{termVars=M.insert v (0,ty) ctx.termVars
               ,varLocs=M.insert v (s,Nothing) ctx.varLocs}

-- | Marks the removal of a list of variables from the scope.
--
-- Currently the error checking part of this is handled by
-- `verifyCtxSubset`, so this is just to remove entries from
-- `varLocs` that are no longer in scope.
endVarScopes :: [Var] -> Tc ()
endVarScopes vars = modify' \ctx -> ctx{varLocs=f ctx.varLocs} where
  f m = foldl' (flip M.delete) m vars

-- | Utility function that keeps varLocs in synch with termVars.
deleteVar :: Var -> Span -> Tc ()
deleteVar v s = modify' \c ->
  c{termVars=M.delete v c.termVars
  ,varLocs=M.adjust addDropLoc v c.varLocs}
  where addDropLoc (s1,_) = (s1, Just s)

-- | Utility function to add and drop kinds from the type context automatically.
withKinds :: [Kind] -> Tc a -> Tc a
withKinds [] m = m
withKinds ks m = do
  ctx <- get
  let tvList = ctx.localTypeVars
      kindLen = length ks
      shiftedTermVars = shiftTermTypes kindLen ctx.termVars
  put $ ctx { termVars=shiftedTermVars, localTypeVars=ks <> tvList }
  val <- m
  ctx2 <- get
  let unshiftedTermVars = shiftTermTypes (-kindLen) ctx2.termVars
  unless (ks <> tvList == ctx2.localTypeVars) $ error "failed to drop a type variable"
  put $ ctx2{termVars=unshiftedTermVars, localTypeVars=tvList}
  pure val
  where shiftTermTypes i = M.map (second $ typeShift i)

-- | Utility function to add and drop kinds from the type context automatically.
--
-- Specialized version of `withKinds` that only takes one kind.
withKind :: Kind -> Tc a -> Tc a
withKind k = withKinds [k]

-- | Get a list of all variables that reference the argument
-- in their type.
variablesBorrowing :: Var -> Tc [Var]
variablesBorrowing v = do
  tv <- gets (.termVars)
  let f (v', (bc, ty))
        | isTyBorrowing v ty = Just v'
        | otherwise = Nothing
      vars = mapMaybe f $ M.toList tv
  pure $ vars

-- | Verify that no variables that should be handled inside a scope are escaping.
--
-- The span should be the span of the entire scope.
verifyCtxSubset :: Span -> Tc a -> Tc a
verifyCtxSubset s m = do
  ctx1 <- get
  v <- m
  ctx2 <- get
  unless (ctx2 `subsetOf` ctx1) $
    let diff = M.difference ctx2.termVars ctx1.termVars
        vars = fst <$> M.toList diff
    in throwError $ VarsEscapingScope vars s
  pure v

-- | Drop the variable.
--
-- Works on references and other trivial types like integers.
dropVar :: Var -> Span -> Tc ()
dropVar v s = do
  (borrowCount, ty) <- lookupEntry v s
  unless (borrowCount == 0) $ do
    borrowers <- variablesBorrowing v
    throwError $ CannotDropBorrowedVar v borrowers s
  case ty.tyf of
    RefTy l _ -> decrementLts l
    Univ Many l _ _ _ -> decrementLts l
    FunTy Many _ l _ -> decrementLts l
    I64Ty -> pure ()
    _ -> throwError $ CannotDropTy ty s
  deleteVar v s

-- | Add the value to the variables referenced in the type.
--
-- This means that it doesn't include the input and output of functions.
adjustRef :: Int -> Ty -> Tc ()
adjustRef i ty = do
  ctx <- get
  forM_ (ltSetToSVars $ ltsInTy ctx ty) $ uncurry $ alterBorrowCount i

-- | Modify the borrow count for the variables in the mentioned lifetime variables.
adjustLts :: Int -> Ty -> Tc ()
adjustLts i lty = lifetimeSVars lty >>= mapM_ (uncurry $ alterBorrowCount i)

decrementLts :: Ty -> Tc ()
decrementLts = adjustLts (-1)

incrementLts :: Ty -> Tc ()
incrementLts = adjustLts 1

-- | Utility function for decrementing the borrow count of the referenced variable
-- when we consume a reference term.
useRef :: Ty -> Tc ()
useRef = adjustRef (-1)

-- | Increments the borrow counts of all lifetimes referenced in the type.
--
-- This means it does not include lifetimes in the input or output of functions.
incRef :: Ty -> Tc ()
incRef = adjustRef 1

-- | Creates de-brujin indices for the type variables.
--
-- Algorithm works by keeping count of how many binders we've descended
-- beneath and then a map of at which binder a variable is introduced.
-- Then we just take the difference to get the de-brujin index.
rawIndexTyVars :: Int -> M.HashMap Text Int -> Ty -> Tc Ty
rawIndexTyVars i idxMap typ@Ty{span=s, tyf} = fmap (Ty s) $ case tyf of
  TyVar tv@(MkTyVar name _) -> case M.lookup name idxMap of
    Just i' -> assert (i-i' >= 0) $ pure $ TyVar (MkTyVar name $ i-i')
    Nothing -> throwError $ UnknownTypeVar tv s
  Univ m lts bind@(TyVarBinding name) k bodyTy -> do
    lts' <- f' lts
    let idxMap' = M.insert name (i+1) idxMap
    bodyTy' <- rawIndexTyVars (i+1) idxMap' bodyTy
    pure $ Univ m lts' bind k bodyTy'
  _ -> traverse f' tyf
  where f' = rawIndexTyVars i idxMap

-- | Creates de-brujin indices for the type variables.
indexTyVars :: Ty -> Tc Ty
indexTyVars = rawIndexTyVars 0 M.empty

-- | Fixes type variable indices across the term, including managing
-- the incrementation due to Poly.
indexTyVarsInTm :: Tm -> Tc Tm
indexTyVarsInTm = g 0 M.empty where
  g :: Int -> M.HashMap Text Int -> Tm -> Tc Tm
  g i idxMap term@Tm{span=s, tmf} = fmap (Tm s) $ case tmf of
    FunTm fix polyB argB t1 -> do
      let add m (j, (TyVarBinding name, kind)) = M.insert name (i+j) m
          idxMap' = foldl' add idxMap (zip [1..] polyB)
          i' = i + length polyB
          toArg (v, Just vTy) = (v,) . Just <$> rawIndexTyVars i' idxMap' vTy
          toArg b = pure b
      argB' <- mapM toArg argB
      t1' <- g i' idxMap' t1
      pure $ FunTm fix polyB argB' t1'
    AppTy t1 tys -> do
      t1' <- f t1
      tys' <- mapM (rawIndexTyVars i idxMap) tys
      pure $ AppTy t1' tys'
    Anno t1 ty -> do
      t1' <- f t1
      ty' <- rawIndexTyVars i idxMap ty
      pure $ Anno t1' ty'
    _ -> traverse f tmf
    where f = g i idxMap
