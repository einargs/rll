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

lookupDataCon :: Var -> Span -> Tc Ty
lookupDataCon v s = do
  m <- gets (.moduleTerms)
  case M.lookup v m of
    Nothing -> throwError $ UnknownDataCon v s
    Just ty -> pure ty

-- | Get the kind of the type. Also checks that the type is well formed.
kindOf :: Ty -> Tc Kind
kindOf ty = case ty of
  TyVar tv s -> lookupKind tv s
  TyCon name s -> lookupDataType name s >>= \case
    StructType _ tyParams _ _ -> pure $ kindFrom tyParams
    BuiltinType _ tyParams -> pure $ kindFrom tyParams
    EnumType tyParams _ _ -> pure $ kindFrom tyParams
  LtOf v s -> lookupEntry v s *> pure LtKind
  FunTy _ aTy lts bTy _ -> do
    kindCheck TyKind aTy
    kindCheck LtKind lts
    kindCheck TyKind bTy
    pure TyKind
  LtJoin tys _ -> do
    forM_ tys (kindCheck LtKind)
    pure LtKind
  RefTy lt aTy _ -> do
    kindCheck LtKind lt
    kindCheck TyKind aTy
    pure TyKind
  Univ _ lts _ tyVarKind bodyTy _ -> do
    kindCheck LtKind lts
    withKind tyVarKind $ kindCheck TyKind bodyTy
    pure TyKind
  TyApp ty1 ty2 s -> do
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
  go polyInRet activateErr ty = case ty of
    TyVar _ _ -> pure ()
    TyCon _ _ -> pure ()
    LtOf _ _ -> pure ()
    LtJoin _ _ -> pure ()
    RefTy _ aTy _ -> f aTy
    FunTy _ aTy lts bTy _ ->
      go polyInRet True aTy *> go polyInRet activateErr bTy
    Univ _ lts _ tyVarKind bodyTy _
      | activateErr -> throwError $ err ty
      | polyInRet -> throwError $ NoPolyInRet ty
      | otherwise -> f bodyTy
    TyApp aTy bTy _ -> f aTy *> f bTy
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
    EnumType tyArgs caseM s -> pure $ (f s tyArgs <$> M.toList caseM, s)
    StructType v tyArgs args s -> pure $ ([f s tyArgs (v,args)], s)
    BuiltinType _ _ -> throwError $
      CompilerLogicError "Cannot add a built-in type to the context" Nothing
  case M.lookup tyName ctx.dataTypes of
    Just _ -> throwError $ DataTypeAlreadyExists tyName s
    Nothing -> pure ()
  terms' <- forM terms \(v,ty) -> (v,) <$> indexTyVars ty
  forM_ terms' \(v,ty) -> case M.lookup v ctx.moduleTerms of
    Just _ -> throwError $ DefAlreadyExists v s
    Nothing -> pure ()
  put $ ctx
    { moduleTerms = foldl' (flip $ uncurry M.insert) ctx.moduleTerms terms'
    , dataTypes = M.insert tyName dt ctx.dataTypes
    }
  forM_ terms' $ check . snd
  where
    check ty = do
      kindCheck TyKind ty
      checkForPoly ty
    f :: Span -> [TypeParam] -> (Text, [Ty]) -> (Var, Ty)
    f s tyArgs (name, args) = (Var name, result) where
      finalTy = foldl' g (TyCon tyName s) $ zip tyArgs [0..] where
        g base (TypeParam{name},i) = TyApp base (TyVar (MkTyVar name i) s) s
      result = buildArgs s tyArgs $ buildTy s finalTy $ reverse args
    buildArgs :: Span -> [TypeParam] -> Ty -> Ty
    buildArgs s tyArgs body = foldr f body tyArgs where
      f (TypeParam{name, kind}) body = Univ Many (LtJoin [] s) (TyVarBinding name) kind body s
    buildTy :: Span -> Ty -> [Ty] -> Ty
    buildTy s ty [] = ty
    buildTy s result [input] = FunTy Many input (LtJoin [] s) result s
    buildTy s result (input:args) = buildTy s fTy args
      where fTy = FunTy Single input (LtJoin [] s) result s

-- NOTE: abstract out the "insert if it doesn't already exist" pattern.

addModuleFun :: Span -> Var -> Ty -> Tc ()
addModuleFun s name ty = do
  ctx <- get
  case M.lookup name ctx.moduleTerms of
    Just _ -> throwError $ DefAlreadyExists name s
    Nothing -> pure ()
  put $ ctx {moduleTerms=M.insert name ty ctx.moduleTerms}

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
withKind :: Kind -> Tc a -> Tc a
withKind k m = do
  ctx <- get
  let tvList = ctx.localTypeVars
  let shiftedTermVars = shiftTermTypes 1 ctx.termVars
  put $ ctx { termVars=shiftedTermVars, localTypeVars=k:tvList }
  val <- m
  ctx2 <- get
  let unshiftedTermVars = shiftTermTypes (-1) ctx2.termVars
  unless (k:tvList == ctx2.localTypeVars) $ error "failed to drop a type variable"
  put $ ctx2{termVars=unshiftedTermVars, localTypeVars=tvList}
  pure val
  where shiftTermTypes i = M.map (second $ rawTypeShift i 0)

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
  f (s, Left x) = TyVar x s
  f (s, Right v) = LtOf v s

-- | Get a set of all unique variables and lifetime variables mentioned in
-- the lifetime. This is the most granular set of lifetimes.
lifetimeSet :: Ty -> Tc LtSet
lifetimeSet (LtOf v s) = pure $ S.singleton $ (s, Right v)
lifetimeSet (LtJoin ls s) = S.unions <$> traverse lifetimeSet ls
lifetimeSet ty@(TyVar x s) = do
  k <- lookupKind x s
  case k of
    LtKind -> pure $ S.singleton $ (s, Left x)
    _ -> throwError $ ExpectedKind LtKind k s
lifetimeSet ty = throwError $ ExpectedKind LtKind TyKind $ getSpan ty

-- | Get a set of all lifetimes mentioned in a type relative to the context.
--
-- It's important that the context type variable indices line up with those
-- in the type.
ltsInTy :: Ctx -> Ty -> LtSet
ltsInTy ctx typ = S.fromList $ f typ [] where
  f ty l = case ty of
    LtOf v s -> (s, Right v ):l
    TyVar tv s -> case getKind tv of
      LtKind -> (s, Left tv ):l
      TyKind -> l
      TyOpKind _ _ -> l
    RefTy t1 t2 _ -> f t1 $ f t2 l
    LtJoin tys _ -> foldl' (flip f) l tys
    FunTy _ t1 t2 t3 _ -> f t2 l
    Univ _ t1 _ _ t2 _ -> f t1 l
    _ -> l
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
  g i tm l = case tm of
    Case arg branches _ -> f arg $ foldl' (\l' (CaseBranch _ _ body) -> f body l') l branches
    LetStruct _ _ t1 t2 _ -> f t2 $ f t1 l
    Let _ t1 t2 _ -> f t2 $ f t1 l
    FunTm _ _ t1 _ -> f t1 l
    Poly _ t1 _ -> g (i+1) t1 l
    TmVar _ _ -> l
    TmCon _ _ -> l
    LiteralTm _ _ -> l
    Copy v s -> case M.lookup v ctx.termVars of
      Just (_,RefTy (LtOf v _) _ _) | M.member v ctx.termVars -> (s, Right v ):l
      Just (_,RefTy (TyVar x@(MkTyVar _ i') _) _ _) | i' >= i -> (s, Left x ):l
      _ -> l
    RefTm v s -> if M.member v ctx.termVars then (s, Right v ):l else l
    AppTy t1 _ _ -> f t1 l
    Drop _ t1 _ -> f t1 l
    AppTm t1 t2 _ -> f t2 $ f t1 l
    FixTm _ t1 _ -> f t1 l
    Anno t1 _ _ -> f t1 l
    where f = g i

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
isTyBorrowing v1 ty = case ty of
  LtOf v _ -> v == v1
  RefTy t1 t2 _ -> f t1 || f t2
  LtJoin tys _ -> any f tys
  FunTy _ t1 t2 t3 _ -> f t1 || f t2 || f t3
  Univ _ t1 _ _ t2 _ -> f t1 || f t2
  _ -> False
  where f = isTyBorrowing v1

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
  case ty of
    RefTy l _ _ -> decrementLts l
    Univ Many l _ _ _ _ -> decrementLts l
    FunTy Many _ l _ _ -> decrementLts l
    _ -> throwError $ CannotDropTy ty s
  deleteVar v s

-- | Utility function for decrementing the borrow count of the referenced variable
-- when we consume a reference term.
useRef :: Ty -> Tc ()
useRef ty = do
  case ty of
    RefTy l _ _ -> decrementLts l
    -- NOTE: figure out why this doesn't need to decrement function lts borrows and
    -- write a test.
    -- OLD: This should be decrementing function borrows right?
    _ -> pure ()

-- | Used to increment borrow counts if the return of a function increments them.
incRef :: Ty -> Tc ()
incRef ty = case ty of
  RefTy l _ _ -> incrementLts l
  FunTy _ _ lts _ _ -> incrementLts lts
  Univ _ lts _ _ _ _ -> incrementLts lts
  _ -> pure ()

rawTypeShift :: Int -> Int -> Ty -> Ty
rawTypeShift i c ty = case ty of
  TyVar (MkTyVar t n) s -> TyVar (MkTyVar t $ if n < c then n else n+i) s
  FunTy m a b c s -> FunTy m (f a) (f b) (f c) s
  LtJoin ts s -> LtJoin (f <$> ts) s
  RefTy a b s -> RefTy (f a) (f b) s
  Univ m lts v k body s -> Univ m (f lts) v k (rawTypeShift i (c+1) body) s
  _ -> ty
  where f = rawTypeShift i c

typeShift :: Ty -> Ty
typeShift = rawTypeShift 1 0

rawTypeSub :: Int -> Ty -> Ty -> Ty
rawTypeSub xi arg target = case target of
  TyVar v@(MkTyVar _ vi) s -> if vi == xi then arg else TyVar v s
  FunTy m a b c s -> FunTy m (f a) (f b) (f c) s
  LtJoin ts s -> LtJoin (f <$> ts) s
  RefTy a b s -> RefTy (f a) (f b) s
  Univ m lts v k body s -> Univ m (f lts) v k (rawTypeSub (xi+1) (rawTypeShift 1 0 arg) body) s
  TyApp a b s -> TyApp (f a) (f b) s
  TyCon _ _ -> target
  LtOf _ _ -> target
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
rawIndexTyVars i idxMap typ = case typ of
  TyVar tv@(MkTyVar name _) s -> case M.lookup name idxMap of
    Just i' -> pure $ TyVar (MkTyVar name $ i-i') s
    Nothing -> throwError $ UnknownTypeVar tv s
  FunTy m aTy lts bTy s -> do
    aTy' <- f' aTy
    lts' <- f' lts
    bTy' <- f' bTy
    pure $ FunTy m aTy' lts' bTy' s
  LtJoin tys s -> do
    tys' <- traverse f' tys
    pure $ LtJoin tys' s
  RefTy lt aTy s -> do
    lt' <- f' lt
    aTy' <- f' aTy
    pure $ RefTy lt' aTy' s
  Univ m lts bind@(TyVarBinding name) k bodyTy s -> do
    lts' <- f' lts
    let idxMap' = M.insert name (i+1) idxMap
    bodyTy' <- rawIndexTyVars (i+1) idxMap' bodyTy
    pure $ Univ m lts' bind k bodyTy' s
  TyApp aTy bTy s -> do
    aTy' <- f' aTy
    bTy' <- f' bTy
    pure $ TyApp aTy' bTy' s
  _ -> pure typ
  where f' = rawIndexTyVars i idxMap

-- | Creates de-brujin indices for the type variables.
indexTyVars :: Ty -> Tc Ty
indexTyVars = rawIndexTyVars 0 M.empty

-- | Fixes type variable indices across the term, including managing
-- the incrementation due to Poly.
indexTyVarsInTm :: Tm -> Tc Tm
indexTyVarsInTm = g 0 M.empty where
  g :: Int -> M.HashMap Text Int -> Tm -> Tc Tm
  g i idxMap term = case term of
    Case arg branches s -> do
      let fBranch (CaseBranch sv svs t1) = CaseBranch sv svs <$> f t1
      arg' <- f arg
      branches' <- traverse fBranch branches
      pure $ Case arg' branches' s
    LetStruct v vs t1 t2 s -> do
      t1' <- f t1
      t2' <- f t2
      pure $ LetStruct v vs t1' t2' s
    Let v t1 t2 s -> do
      t1' <- f t1
      t2' <- f t2
      pure $ Let v t1' t2' s
    FunTm m mbAnno t1 s -> do
      mbAnno' <- traverse (rawIndexTyVars i idxMap) mbAnno
      t1' <- f t1
      pure $ FunTm m mbAnno' t1' s
    Poly mbAnno t1 s -> do
      let idxMap' = case mbAnno of
            Just (TyVarBinding name, _) -> M.insert name (i+1) idxMap
            Nothing -> idxMap
      t1' <- g (i+1) idxMap' t1
      pure $ Poly mbAnno t1' s
    AppTy t1 ty s -> do
      t1' <- f t1
      ty' <- rawIndexTyVars i idxMap ty
      pure $ AppTy t1' ty' s
    Drop v t1 s -> do
      t1' <- f t1
      pure $ Drop v t1' s
    AppTm t1 t2 s -> do
      t1' <- f t1
      t2' <- f t2
      pure $ AppTm t1' t2' s
    FixTm fv t1 s -> do
      t1' <- g (i+1) idxMap t1
      pure $ FixTm fv t1' s
    Anno t1 ty s -> do
      t1' <- f t1
      ty' <- rawIndexTyVars i idxMap ty
      pure $ Anno t1' ty' s
    TmVar _ _ -> pure term
    TmCon _ _ -> pure term
    Copy _ _ -> pure term
    RefTm _ _ -> pure term
    LiteralTm _ _ -> pure term
    where f = g i idxMap
