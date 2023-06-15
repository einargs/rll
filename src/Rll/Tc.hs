module Rll.Tc
  ( Tc(..), runTc, evalTc
  , expectedTermVar, lookupEntry, lookupVar, lookupKind
  , lookupDataType, lookupDataCon, addDataType, addModuleFun
  , alterBorrowCount , addVar, deleteVar, withKind
  , kindOf, sanityCheckType
  , rawTypeSub, typeSub
  , lifetimeVars, lifetimeSet
  , ltSetToTypes, ltsForClosure, ltSetToVars
  , incrementLts, decrementLts, variablesBorrowing
  , dropVar, useRef, incRef
  , rawIndexTyVars, indexTyVars, indexTyVarsInTm
  , applyTypeParams
  ) where

import Rll.Ast
import Rll.Context
import Rll.TypeError

import Control.Monad (unless, when, forM_, forM)
import Data.Text (Text)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Control.Monad.State (MonadState(..), StateT, modify', runStateT, gets)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Control.Arrow (first, second)
import Data.List (foldl')
import Safe (atMay)
import Data.Maybe (mapMaybe)

newtype Tc a = MkTc { unTc :: StateT Ctx (Except TyErr) a }
  deriving (Functor, Applicative, Monad, MonadError TyErr, MonadState Ctx)

runTc :: Ctx -> Tc a -> Either TyErr (a, Ctx)
runTc ctx = runExcept . flip runStateT ctx . unTc

evalTc :: Ctx -> Tc a -> Either TyErr a
evalTc ctx = fmap fst . runTc ctx

-- | Throws either `UnknownTermVar` or `RemovedTermVar`.
expectedTermVar :: Var -> Span -> Tc a
expectedTermVar v s = do
  vl <- gets (.varLocs)
  throwError $ case M.lookup v vl of
    Just (_,Nothing) -> CompilerLogicError "varLocs not in synch with termVars" (Just s)
    Just (_,Just removedSpan) -> RemovedTermVar s removedSpan
    Nothing -> UnknownTermVar v s

lookupEntry :: Var -> Span -> Tc (Int, Ty)
lookupEntry v s = do
  tm <- gets (.termVars)
  case M.lookup v tm of
    Nothing -> expectedTermVar v s
    Just e -> pure e

lookupVar :: Var -> Span -> Tc Ty
lookupVar v s = snd <$> lookupEntry v s

lookupKind :: TyVar -> Span -> Tc Kind
lookupKind v@(MkTyVar name i) s = do
  l <- gets (.localTypeVars)
  case atMay l i of
    Just k -> pure k
    Nothing -> throwError $ UnknownTypeVar v s

lookupDataType :: Var -> Span -> Tc DataType
lookupDataType v s = do
  dtm <- gets (.dataTypes)
  case M.lookup v dtm of
    Nothing -> throwError $ UnknownDataType v s
    Just dt -> pure dt

lookupDataCon :: Var -> Span -> Tc (DataType, Ty)
lookupDataCon v s = do
  m <- gets (.moduleDataCons)
  case M.lookup v m of
    Nothing -> throwError $ UnknownDataCon v s
    Just (dt, ty) -> pure (dt, ty)

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
  unless (k==k') $ throwError $ ExpectedKind k k' $ getSpan ty

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
  case M.lookup name ctx.moduleFuns of
    Just _ -> throwError $ DefAlreadyExists name s
    Nothing -> pure ()
  put $ ctx {moduleFuns=M.insert name ty ctx.moduleFuns}

alterBorrowCount :: Var -> (Int -> Int) -> Tc ()
alterBorrowCount v f = modify' $ onTermVars $ M.adjust (first f) v
  -- where f' i = let i' = f i in if i' < 0 then T.trace ("less than zero for " <> show v) i' else i'

addVar :: Var -> Span -> Ty -> Tc ()
addVar v s ty = do
  ctx <- get
  case M.lookup v ctx.termVars of
    Just _ -> do
      varLocs <- gets (.varLocs)
      def <- case M.lookup v varLocs of
        Nothing -> error "varLocs was not properly synched to varTerms"
        Just (def,_) -> pure def
      throwError $ VarAlreadyInScope v s def
    Nothing -> do
      -- NOTE: this may be redundant
      sanityCheckType ty
      put $ ctx{termVars=M.insert v (0,ty) ctx.termVars
               ,varLocs=M.insert v (s,Nothing) ctx.varLocs}

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
  where shiftTermTypes i = M.map (second $ rawTypeShift i 0)

-- | Utility function to add and drop kinds from the type context automatically.
--
-- Specialized version of `withKinds` that only takes one kind.
withKind :: Kind -> Tc a -> Tc a
withKind k = withKinds [k]

-- | Get a list of explicitly mentioned variables in the lifetime.
-- Ignores lifetime variables.
lifetimeVars :: Ty -> Tc [Var]
lifetimeVars = fmap ltSetToVars . lifetimeSet

-- | A lifetime type reduced down to its essence.
type LtSet = S.HashSet (Span, Either TyVar Var)

-- | Convenience function for getting a list of variables from a lifetime set
ltSetToVars :: LtSet -> [Var]
ltSetToVars = mapMaybe f . fmap snd . S.toList where
  f (Right v) = Just v
  f _ = Nothing

-- | Convert a lifetime set to a list of the lifetimes.
ltSetToTypes :: LtSet -> [Ty]
ltSetToTypes ltSet = fmap f $ S.toList ltSet where
  f (s, Left x) = Ty s $ TyVar x
  f (s, Right v) = Ty s $ LtOf v

-- | Get a set of all unique variables and lifetime variables mentioned in
-- the lifetime. This is the most granular set of lifetimes.
lifetimeSet :: Ty -> Tc LtSet
lifetimeSet Ty{span, tyf} = case tyf of
  LtOf v -> pure $ S.singleton $ (span, Right v)
  LtJoin ls -> S.unions <$> traverse lifetimeSet ls
  TyVar x -> do
    k <- lookupKind x span
    case k of
      LtKind -> pure $ S.singleton $ (span, Left x)
      _ -> throwError $ ExpectedKind LtKind k span
  _ -> throwError $ ExpectedKind LtKind TyKind span

-- | Get a set of all lifetimes mentioned in a type relative to the context.
--
-- It's important that the context type variable indices line up with those
-- in the type.
ltsInTy :: Ctx -> Ty -> LtSet
ltsInTy ctx typ = S.fromList $ f typ [] where
  f Ty{span=s, tyf} l = case tyf of
    LtOf v -> (s, Right v):l
    TyVar tv -> case getKind tv of
      LtKind -> (s, Left tv):l
      TyKind -> l
      TyOpKind _ _ -> l
    _ -> foldr f l tyf
  getKind (MkTyVar _ i) = case atMay ctx.localTypeVars i of
    Just k -> k
    Nothing -> error "Should have been caught already"

-- | Get all lifetimes implied by borrows and copies inside a closure.
--
-- Context is the closure entrance context. Used to make sure
-- we only return lifetimes external to the closure.
ltsBorrowedIn :: Ctx -> Tm -> LtSet
ltsBorrowedIn ctx tm = S.fromList $ g 0 tm [] where
  -- | `i` is the threshold counter used for telling which type variable is local.
  g i tm@Tm{span=s, tmf} l = case tmf of
    FunTm fix polyB argB t1 -> g (i + length polyB) t1 l
    Copy v -> case M.lookup v ctx.termVars of
      Just (_, Ty _ (RefTy (Ty _ (LtOf v)) _)) | M.member v ctx.termVars -> (s, Right v ):l
      Just (_, Ty _ (RefTy (Ty _ (TyVar x)) _)) | x.index >= i -> (s, Left x ):l
      _ -> l
    RefTm v -> if M.member v ctx.termVars then (s, Right v ):l else l
    _ -> foldr (g i) l tmf

-- | Infer the lifetimes mentioned in the types of all consumed values.
ltsInConsumed :: Ctx -> Ctx -> LtSet
ltsInConsumed c1 c2 = S.unions ltSets where
  diff = M.difference c1.termVars c2.termVars
  ltSets = ltsInTy c1 . snd <$> M.elems diff

-- | Infer the lifetimes for a closure type.
ltsForClosure :: Ctx -> Ctx -> Tm -> LtSet
ltsForClosure c1 c2 tm = S.union (ltsInConsumed c1 c2) $ ltsBorrowedIn c1 tm

-- | Modify the borrow count for the variables in the mentioned lifetime variables.
adjustLts :: (Int -> Int) -> Ty -> Tc ()
adjustLts f lty = lifetimeVars lty >>= mapM_ (flip alterBorrowCount f)

decrementLts :: Ty -> Tc ()
decrementLts = adjustLts $ subtract 1

incrementLts :: Ty -> Tc ()
incrementLts = adjustLts (+1)

-- | Does the type use the lifetime of this variable?
isTyBorrowing :: Var -> Ty -> Bool
isTyBorrowing v1 Ty{tyf} = case tyf of
  LtOf v -> v == v1
  _ -> or $ isTyBorrowing v1 <$> tyf

-- | Get a list of all variables that reference the argument
-- in their type.
variablesBorrowing :: Var -> Tc [Var]
variablesBorrowing v = do
  tv <- gets (.termVars)
  let f (_, (bc, ty)) = isTyBorrowing v ty
      vars = fmap fst $ filter f $ M.toList tv
  pure $ vars

-- | Drop the variable.
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
    _ -> throwError $ CannotDropTy ty s
  deleteVar v s

-- | Utility function for decrementing the borrow count of the referenced variable
-- when we consume a reference term.
useRef :: Ty -> Tc ()
useRef ty = do
  case ty.tyf of
    RefTy l _ -> decrementLts l
    -- NOTE: figure out why this doesn't need to decrement function lts borrows and
    -- write a test.
    -- OLD: This should be decrementing function borrows right?
    _ -> pure ()

-- | Used to increment borrow counts if the return of a function increments them.
incRef :: Ty -> Tc ()
incRef ty = case ty.tyf of
  RefTy l _ -> incrementLts l
  FunTy _ _ lts _ -> incrementLts lts
  Univ _ lts _ _ _ -> incrementLts lts
  _ -> pure ()

rawTypeShift :: Int -> Int -> Ty -> Ty
rawTypeShift i c ty@Ty{span=s, tyf} = Ty s $ case tyf of
  TyVar (MkTyVar t n) -> TyVar (MkTyVar t $ if n < c then n else n+i)
  Univ m lts v k body -> Univ m (f lts) v k (rawTypeShift i (c+1) body)
  _ -> f <$> tyf
  where f = rawTypeShift i c

typeShift :: Ty -> Ty
typeShift = rawTypeShift 1 0

rawTypeSub :: Int -> Ty -> Ty -> Ty
rawTypeSub xi arg target@Ty{span=s, tyf} = case tyf of
  TyVar v@(MkTyVar _ vi) -> if vi == xi then arg else Ty s $ TyVar v
  Univ m lts v k body -> Ty s $ Univ m (f lts) v k (rawTypeSub (xi+1) (rawTypeShift 1 0 arg) body)
  _ -> Ty s $ f <$> tyf
  where f = rawTypeSub xi arg

-- | Do type substitution on the body of a Univ type.
--
-- Argument, body
typeSub :: Ty -> Ty -> Ty
typeSub = rawTypeSub 0

-- | Creates de-brujin indices for the type variables.
--
-- Algorithm works by keeping count of how many binders we've descended
-- beneath and then a map of at which binder a variable is introduced.
-- Then we just take the difference to get the de-brujin index.
rawIndexTyVars :: Int -> M.HashMap Text Int -> Ty -> Tc Ty
rawIndexTyVars i idxMap typ@Ty{span=s, tyf} = fmap (Ty s) $ case tyf of
  TyVar tv@(MkTyVar name _) -> case M.lookup name idxMap of
    Just i' -> pure $ TyVar (MkTyVar name $ i-i')
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
      pure $ FunTm fix polyB argB t1'
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

-- | Substitute for the type parameter variables inside the fields of a
-- data type.
--
-- Type arguments, params, data type fields.
applyTypeParams :: [Ty] -> [TypeParam] -> [Ty] -> [Ty]
applyTypeParams args params members = go (length args - 1) args params members where
  go i [] [] members = members
  go i (a:as) (p:ps) members = go (i-1) as ps $
    rawTypeSub i a <$> members
  go i _ _ _ = error "Should be caught by kind check"
