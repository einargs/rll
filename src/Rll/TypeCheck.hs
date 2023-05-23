{-# LANGUAGE OverloadedStrings, OverloadedRecordDot, BlockArguments #-}
module Rll.TypeCheck where

import Rll.Ast
import Rll.TypeError
import Rll.Context

import Control.Monad (unless, when, forM_)
import Data.Text (Text, pack, unpack)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Control.Monad.State (MonadState(..), StateT, modify', runStateT, gets)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Data.Maybe (fromMaybe)
import Control.Arrow (first, second)
import Data.Function (on)
import Data.Functor (($>))
import qualified Data.List as L
import qualified Debug.Trace as T
import Data.List (find, foldl')
import Safe (atMay)

newtype Tc a = MkTc { unTc :: StateT Ctx (Except TyErr) a }
  deriving (Functor, Applicative, Monad, MonadError TyErr, MonadState Ctx)

-- | Creates de-brujin indices for the type variables.
indexTyVars :: Ty -> Tc Ty
indexTyVars = f 0 M.empty where
  -- | Algorithm works by keeping count of how many binders we've descended
  -- beneath and then a map of at which binder a variable is introduced.
  -- Then we just take the difference to get the de-brujin index.
  f :: Int -> M.HashMap Text Int -> Ty -> Tc Ty
  f i idxMap typ = case typ of
    TyVar (MkTyVar name _) s -> case M.lookup name idxMap of
      Just i' -> pure $ TyVar (MkTyVar name $ i-i') s
      Nothing -> throwError $ UnknownTypeVar name s
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
      bodyTy' <- f (i+1) idxMap' bodyTy
      pure $ Univ m lts' bind k bodyTy' s
    _ -> pure typ
    where f' = f i idxMap

emptyCtx :: Ctx
emptyCtx = Ctx M.empty [] M.empty M.empty

runTc :: Ctx -> Tc a -> Either TyErr (a, Ctx)
runTc ctx = runExcept . flip runStateT ctx . unTc

evalTc :: Ctx -> Tc a -> Either TyErr a
evalTc ctx = fmap fst . runTc ctx

lookupEntry :: Var -> Span -> Tc (Int, Ty)
lookupEntry v s = do
  tm <- gets (.termVars)
  case M.lookup v tm of
    Nothing -> throwError $ UnknownTermVar v s
    Just e -> pure e

lookupVar :: Var -> Span -> Tc Ty
lookupVar v s = snd <$> lookupEntry v s

lookupKind :: TyVar -> Span -> Tc Kind
lookupKind v@(MkTyVar name i) s = do
  l <- gets (.localTypeVars)
  case atMay l i of
    Just k -> pure k
    Nothing -> throwError $ UnknownTypeVar name s

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

addDataType :: Var -> DataType -> Tc ()
addDataType tyName dt = do
  let s = getSpan dt
  ctx <- get
  case M.lookup tyName ctx.dataTypes of
    Just _ -> throwError $ DataTypeAlreadyExists tyName s
    Nothing -> pure ()
  let f :: (Text, [Ty]) -> (Var, Ty)
      f (name, args) = (Var name, buildTy (TyCon tyName s) $ reverse args)
      buildTy :: Ty -> [Ty] -> Ty
      buildTy ty [] = ty
      buildTy result [input] = FunTy Many input (LtJoin [] s) result s
      buildTy result (input:args) = buildTy fTy args
        where fTy = FunTy Single input (LtJoin [] s) result s
      terms = case dt of
        EnumType caseM _ -> f <$> M.toList caseM
        StructType v args _ -> [f (v,args)]
  forM_ terms \(v,ty) -> case M.lookup v ctx.moduleTerms of
    Just _ -> throwError $ DefAlreadyExists v s
    Nothing -> pure ()
  put $ ctx
    { moduleTerms = foldl' (flip $ uncurry M.insert) ctx.moduleTerms terms
    , dataTypes = M.insert tyName dt ctx.dataTypes
    }

-- TODO: abstract out the "insert if it doesn't already exist" pattern.

addModuleFun :: Span -> Var -> Ty -> Tc ()
addModuleFun s name ty = do
  ctx <- get
  case M.lookup name ctx.moduleTerms of
    Just _ -> throwError $ DefAlreadyExists name s
    Nothing -> pure ()
  put $ ctx {moduleTerms=M.insert name ty ctx.moduleTerms}

alterBorrowCount :: Var -> (Int -> Int) -> Tc ()
alterBorrowCount v f = modify' $ onTermVars $ M.adjust (first f) v

-- | Use this to construct the type of a reference type.
borrowVar :: Var -> Span -> Tc Ty
borrowVar v s = do
  -- TODO: I think this is only used like once, so maybe just replace
  -- with doing it at call site. Better span manip then too.
  t <- lookupVar v s
  alterBorrowCount v (+1)
  -- TODO I'm pretty sure using this span makes sense, but check.
  pure $ RefTy (LtOf v s) t s

addVar :: Var -> Span -> Ty -> Tc ()
addVar v s ty = do
  ctx <- get
  case M.lookup v ctx.termVars of
    Just _ -> throwError $ VarAlreadyInScope v s
    Nothing -> put $ ctx{termVars=M.insert v (0,ty) ctx.termVars}

-- | Get a list of explicitly mentioned variables in the lifetime.
-- Ignores lifetime variables.
lifetimeVars :: Ty -> Tc [Var]
lifetimeVars (LtOf v s) = pure [v]
lifetimeVars (LtJoin ls s) = concat <$> traverse lifetimeVars ls
lifetimeVars ty@(TyVar x s) = do
  k <- lookupKind x s
  case k of
    -- TODO: make sure there's no problem with ignoring variables.
    LtKind -> pure []
    TyKind -> throwError $ ExpectedKind LtKind ty TyKind
lifetimeVars ty = throwError $ ExpectedKind LtKind ty TyKind

decrementLts :: Ty -> Tc ()
decrementLts lty = lifetimeVars lty >>= mapM_ (flip alterBorrowCount (subtract 1))

dropVar :: Var -> Span -> Tc ()
dropVar v s = do
  (borrowCount, ty) <- lookupEntry v s
  unless (borrowCount == 0) $ throwError $ CannotDropBorrowedVar v s
  case ty of
    RefTy l _ _ -> decrementLts l
    Univ Many l _ _ _ _ -> decrementLts l
    FunTy Many _ l _ _ -> decrementLts l
    _ -> throwError $ CannotDropTy ty s
  modify' $ onTermVars $ M.delete v

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

-- | This is used to "use" a term var. If it cannot find a term
-- var in termVars to consume, it looks in moduleTerms.
useVar :: Var -> Span -> Tc Ty
useVar v s = do
  ctx <- get
  case M.lookup v ctx.termVars of
    Just (borrowCount, ty) -> do
      unless (borrowCount == 0) $ do
        borrowers <- variablesBorrowing v
        throwError $ CannotUseBorrowedVar v borrowers s
      modify' $ onTermVars $ M.delete v
      pure ty
    Nothing -> case M.lookup v ctx.moduleTerms of
      Just ty -> pure ty
      Nothing -> throwError $ UnknownTermVar v s

-- | Utility function for decrementing the borrow count of the referenced variable
-- when we consume a reference term.
useRef :: Ty -> Tc ()
useRef ty = do
  case ty of
    RefTy l _ _ -> decrementLts l
    _ -> pure ()

-- | Utility function to add and drop kinds from the type context automatically.
withKind :: Kind -> Tc a -> Tc a
withKind k m = do
  ctx <- get
  let tvList = ctx.localTypeVars
  put $ ctx {localTypeVars=k:tvList }
  val <- m
  ctx2 <- get
  unless (k:tvList == ctx2.localTypeVars) $ error "failed to drop a type variable"
  put $ ctx2{localTypeVars=tvList}
  pure val

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

data TyOp a where
  Check :: TyOp ()
  Synth :: TyOp Ty

class Eq a => TyOpResult a where
  getTyOp :: TyOp a

instance TyOpResult Ty where
  getTyOp = Synth

instance TyOpResult () where
  getTyOp = Check

-- | Join type checking actions on multiple branches of a case statement.
--
-- We parameterize over equality for switching between synthesis and checking.
--
-- The span is the span of the overall case statement.
joinBranches :: forall a. TyOpResult a => Span -> [Tc a] -> Tc a
joinBranches s [] = throwError $ NoCaseBranches s
joinBranches s [b] = b
joinBranches s (b:bs) = do
  ctx <- get
  ty <- b
  ctx1 <- get
  let f b = do
        put ctx
        bTy <- b
        ctx' <- get
        pure $ (bTy, ctx')
  (tys,ctxs) <- unzip <$> traverse f bs
  unless (all (localEq ctx1) ctxs) $ throwError $ CannotJoinCtxs (ctx1:ctxs) s
  () <- case getTyOp @a of
    Check -> pure ()
    Synth -> unless (all (ty==) tys) $ throwError $ CannotJoinTypes (ty:tys) s
  pure ty

toRef :: Span -> Ty -> Ty -> Ty
toRef s lt ty@(RefTy _ _ _) = ty
toRef s lt ty = RefTy lt ty s

-- TODO rewrite a bunch of this using recursion schemes.
-- | Do type substitution on the body of a Univ type.
typeSub :: Ty -> Ty -> Ty
typeSub = sub 0
  where
    sub :: Int -> Ty -> Ty -> Ty
    sub xi arg target = case target of
      TyVar v@(MkTyVar _ vi) s -> if vi == xi then arg else TyVar v s
      FunTy m a b c s -> FunTy m (f a) (f b) (f c) s
      LtJoin ts s -> LtJoin (f <$> ts) s
      RefTy a b s -> RefTy (f a) (f b) s
      Univ m lts v k body s -> Univ m (f lts) v k (sub (xi+1) (shift 1 0 arg) body) s
      _ -> target
      where f = sub xi arg
    shift :: Int -> Int -> Ty -> Ty
    shift i c ty = case ty of
      TyVar (MkTyVar t n) s -> TyVar (MkTyVar t $ if n < c then n else n+i) s
      FunTy m a b c s -> FunTy m (f a) (f b) (f c) s
      LtJoin ts s -> LtJoin (f <$> ts) s
      RefTy a b s -> RefTy (f a) (f b) s
      Univ m lts v k body s -> Univ m (f lts) v k (shift i (c+1) body) s
      _ -> ty
      where f = shift i c

-- | Borrow part of a data structure.
--
-- Uses toRef to ensure that if the member we borrow is a reference, we
-- just get that reference as a type instead of a reference to a reference.
addPartialBorrowVar :: Var -> Span -> Ty -> Ty -> Tc ()
addPartialBorrowVar v s lt bTy = do
  let ty = toRef s lt bTy
  addVar v s ty
  case ty of
    RefTy (LtOf v' _) _ _ -> alterBorrowCount v' (+1)
    RefTy (TyVar _ _) _ _ -> pure ()
    RefTy lt@(LtJoin _ _) _ _ -> throwError $ RefLtIsComposite lt s
    RefTy lt _ _ -> throwError $ ExpectedKind LtKind lt TyKind
    _ -> error "toRef should ensure type is always a RefTy"

caseClause :: forall a. TyOpResult a => Span -> Tm -> [CaseBranch] -> (Tm -> Tc a) -> Tc a
caseClause caseSpan t1 branches method = do
  t1Ty <- synth t1
  case t1Ty of
    TyCon tyName conSpan -> do
      conMap <- ensureEnum t1Ty tyName conSpan
      let f var ty = addVar var caseSpan ty
      joinBranches caseSpan $ handleBranch f tyName conMap <$> branches
    RefTy lt (TyCon tyName conSpan) _ -> do
      useRef t1Ty
      conMap <- ensureEnum t1Ty tyName conSpan
      let f var ty = addPartialBorrowVar var caseSpan lt ty
      joinBranches caseSpan $ handleBranch f tyName conMap <$> branches
    _ -> throwError $ TypeIsNotEnum t1Ty $ getSpan t1
  where
    handleBranch :: (Var -> Ty -> Tc ()) -> Var -> M.HashMap Text [Ty] -> CaseBranch -> Tc a
    handleBranch addMember tyName conMap (CaseBranch conVar vars body) = do
      case M.lookup conVar.name conMap of
        -- TODO: add spans to CaseBranch so I can pass that along instead of the case span.
        Nothing -> throwError $ UnknownEnumCase tyName conVar caseSpan
        Just varTys -> do
          unless (length varTys == length vars) $ throwError
            $ BadEnumCaseVars vars varTys caseSpan
          let members = zip vars varTys
          forM_ members $ uncurry addMember
          method body
    ensureEnum :: Ty -> Var -> Span -> Tc (M.HashMap Text [Ty])
    ensureEnum t1Ty v conSpan = do
      dt <- lookupDataType v conSpan
      case dt of
        StructType _ _ _ -> throwError $ TypeIsNotEnum t1Ty (getSpan t1)
        EnumType conMap _ -> do
          let hasCon t (CaseBranch v _ _) = t == v.name
              count t = (t, filter (hasCon t) branches)
              occurances = count <$> M.keys conMap
              noBranches (_, brs) = 0 == length brs
              multBranches (_, brs) = 1 < length brs
          case find noBranches occurances of
            Just (name,_) -> throwError $ NoBranchForCase name caseSpan
            Nothing -> pure ()
          case find multBranches occurances of
            Just (name,_) -> throwError $ MultBranchesForCase name caseSpan
            Nothing -> pure ()
          pure conMap

letStructClause :: forall a. Span -> Var -> [Var] -> Tm -> Tm -> (Tm -> Tc a) -> Tc a
letStructClause letSpan structCon memberVars t1 body method = do
  t1Ty <- synth t1
  case t1Ty of
    TyCon tyName tySpan -> do
      let f var ty = addVar var letSpan ty
      handle f t1Ty tyName tySpan
    RefTy lt (TyCon tyName tySpan) _ -> do
      useRef t1Ty
      let f var ty = addPartialBorrowVar var letSpan lt ty
      handle f t1Ty tyName tySpan
    _ -> throwError $ TypeIsNotStruct t1Ty $ getSpan t1
  where
    handle :: (Var -> Ty -> Tc ()) -> Ty -> Var -> Span -> Tc a
    handle addMember t1Ty tyName tySpan = do
      -- TODO In the future I might remove the struct name since it's redundant.
      dt <- lookupDataType tyName tySpan
      case dt of
        EnumType _ _ -> throwError $ TypeIsNotStruct t1Ty $ getSpan t1
        StructType structCon' memberTys _ -> do
          unless (structCon.name == structCon') $ throwError $
            WrongConstructor structCon structCon' tyName letSpan
          unless (length memberTys == length memberVars) $ throwError $
            BadLetStructVars memberVars memberTys letSpan
          let members = zip memberVars memberTys
          forM_ members $ uncurry addMember
          method body

letClause :: Span -> Var -> Tm -> Tm -> (Tm -> Tc a) -> Tc a
letClause s x t1 t2 f = do
  xTy <- synth t1
  addVar x s xTy
  f t2

-- | Context is the closure entrance context. Used to make sure
-- we only return variables external to the closure.
varsBorrowedIn :: Ctx -> Tm -> [Var]
varsBorrowedIn ctx tm = L.nub $ f tm [] where
  f tm l = case tm of
    Case arg branches _ -> f arg $ foldl' (\l' (CaseBranch _ _ body) -> f body l') l branches
    LetStruct _ _ t1 t2 _ -> f t2 $ f t1 l
    Let _ t1 t2 _ -> f t2 $ f t1 l
    FunTm _ _ t1 _ -> f t1 l
    Poly _ _ t1 _ -> f t1 l
    TmVar _ _ -> l
    TmCon _ _ -> l
    Copy _ _ -> l
    RefTm v _ -> if M.member v ctx.termVars then v:l else l
    AppTy t1 _ _ -> f t1 l
    Drop _ t1 _ -> f t1 l
    AppTm t1 t2 _ -> f t2 $ f t1 l
    RecFun _ _ _ t1 _ -> f t1 l
    Anno t1 _ _ -> f t1 l

-- | Given an entrance and exit context, we see which variables in the
-- entrance are no longer in the exit context (and thus have been consumed).
consumedVars :: Ctx -> Ctx -> [Var]
consumedVars c1 c2 = M.keys $ M.difference c1.termVars c2.termVars
{-
consumedVars c1 c2 = if M.isSubmapOfBy (const $ const True) m c1.varNames
  then fmap (uncurry $ flip Var) $ M.assocs $ M.difference c1.varNames m
  else error "Variable names map did not contain name for consumed variable"
  where m = M.difference c1.termCtx c2.termCtx
-}

findMult :: Ctx -> Ctx -> Mult
findMult c1 c2 = if [] /= cv then Single else Many where
  cv = consumedVars c1 c2

-- | We take the span for the whole closure.
verifyMult :: Span -> Mult -> Ctx -> Ctx -> Tc ()
verifyMult s Many c1 c2 | consumed /= [] = throwError $ MultiFnCannotConsume consumed s
  where consumed = consumedVars c1 c2
verifyMult _ _ _ _ = pure ()

-- | Checks to make sure borrows and drops are balanced in a function definition.
--
-- Any borrowing of a variable in startCtx needs to have same borrow count at the end.
checkStableBorrowCounts :: Span -> Ctx -> Ctx -> Tc ()
checkStableBorrowCounts s c1 c2 = unless ([] == unstableBorrowedVars) err
  where
  err = throwError $ UnstableBorrowCounts unstableBorrowedVars s
  unstableBorrowedVars :: [Var]
  unstableBorrowedVars = M.keys m where
    m = M.mapMaybe id $ M.intersectionWith f c1.termVars c2.termVars
    f (i1, _) (i2, _) | i1 /= i2 = Just ()
                      | otherwise = Nothing

-- | Helper function for doing common work related to synthesizing
-- closure types.
mkClosureSynth :: Span -> Tm -> Tc a -> Tc (Ty, Mult, a)
mkClosureSynth s body m = do
  startCtx <- get
  out <- m
  endCtx <- get
  let vars = varsBorrowedIn startCtx body
      lts = LtJoin (flip LtOf s <$> vars) s
      mult = findMult startCtx endCtx
  checkStableBorrowCounts s startCtx endCtx
  forM_ vars $ flip alterBorrowCount (+1)
  pure $ (lts, mult, out)

synthFun :: Span -> Var -> Ty -> Tm -> Tc Ty
synthFun s v vTy body = do
  (lts, mult, bodyTy) <- mkClosureSynth s body do
    addVar v s vTy
    synth body
  pure $ FunTy mult vTy lts bodyTy s

synthPoly :: Span -> TyVarBinding -> Kind -> Tm -> Tc Ty
synthPoly s b kind body = do
  (lts, mult, bodyTy) <- mkClosureSynth s body $
    withKind kind $ synth body
  pure $ Univ mult lts b kind bodyTy s

-- | Helper for verifying that borrowed variables are correct for the closure.
verifyBorrows :: Span -> Ctx -> Ty -> Tm -> Tc ()
verifyBorrows s ctx lts body = do
  ltsSet <- S.fromList <$> lifetimeVars lts
  -- TODO: upgrade to list variables.
  unless (ltsSet == varSet) $ throwError $ IncorrectBorrowedVars lts vars s
  forM_ vars $ flip alterBorrowCount (+1)
  where
    vars = varsBorrowedIn ctx body
    varSet = S.fromList vars

-- | Helper for building closure checks.
mkClosureCheck :: Span -> Tm -> Mult -> Ty -> Tc () -> Tc ()
mkClosureCheck s body mult lts m = do
  startCtx <- get
  m
  endCtx <- get

  -- Check specified lifetimes
  verifyBorrows s startCtx lts body

  -- Check multiplicity if Many is specified
  verifyMult s mult startCtx endCtx

  checkStableBorrowCounts s startCtx endCtx

checkFun :: Span -> Var -> Tm -> Mult -> Ty -> Ty -> Ty -> Tc ()
checkFun s v body mult aTy lts bTy = mkClosureCheck s body mult lts do
  addVar v s aTy
  check bTy body

checkPoly :: Span -> TyVarBinding -> Kind -> Tm -> Mult -> Ty -> Ty -> Tc ()
checkPoly s b kind body mult lts bodyTy = mkClosureCheck s body mult lts do
  withKind kind $ check bodyTy body

checkRecFun :: Span -> Var -> TyVarBinding -> Var -> Tm -> Ty -> Ty -> Ty -> Tc ()
checkRecFun s x funLtVar funVar body xTy lts bodyTy = mkClosureCheck s body Many lts do
  addVar x s xTy
  withKind LtKind do
    let fTy = FunTy Many xTy lts bodyTy s
        rTy = RefTy (TyVar (MkTyVar funLtVar.name 0) s) fTy s
    addVar funVar s rTy
    check bodyTy body

synth :: Tm -> Tc Ty
synth tm = verifyCtxSubset (getSpan tm) $ case tm of
  Drop v t s -> do
    dropVar v s
    synth t
  LetStruct con vars t1 t2 s -> letStructClause s con vars t1 t2 synth
  TmCon v s -> lookupDataCon v s
  Anno t ty _ -> check ty t >> pure ty
  TmVar v s -> useVar v s
  Copy v s -> do
    vTy <- lookupVar v s
    case vTy of
      RefTy (LtOf v' _ ) _ _ -> borrowVar v' s
      RefTy _ _ _ -> pure vTy
      _ -> throwError $ TypeIsNotRef vTy s
  RefTm v s -> borrowVar v s
  Let x t1 t2 s -> letClause s x t1 t2 synth
  Case t1 branches s -> caseClause s t1 branches synth
  FunTm v (Just vTy) body s -> synthFun s v vTy body
  FunTm _ Nothing _ s -> throwError $ FunTySynthRequiresAnno s
  Poly v kind body s -> synthPoly s v kind body
  AppTy t1 tyArg s -> do
    t1Ty <- synth t1
    case t1Ty of
      Univ _ lts v k body _ -> do
        decrementLts lts
        pure $ typeSub tyArg body
      RefTy l (Univ Many lts v k body _) _ -> do
        useRef t1Ty
        pure $ typeSub tyArg body
      _ -> throwError $ TyIsNotUniv t1Ty s
  AppTm t1 t2 s -> do
    -- Roughly we synthesize t1 and use that to check t2.
    t1Ty <- synth t1
    case t1Ty of
      FunTy Single aTy lts bTy _ -> do
        check aTy t2
        useRef aTy
        decrementLts lts
        pure bTy
      -- TODO: original plan called for only being able to call multi-use functions
      -- through references, but is that really a useful distinction?
      FunTy Many aTy lts bTy _ -> do
        check aTy t2
        useRef aTy
        decrementLts lts
        pure bTy
      RefTy lt (FunTy Many aTy lts bTy _) _ -> do
        check aTy t2
        useRef aTy
        useRef t1Ty
        pure bTy
      _ -> throwError $ TyIsNotFun t1Ty s
  -- ltOfFVar is the name of the variable used for the lifetime of the variable f, which is
  -- a reference to this function itself.
  RecFun _ _ _ _ s -> throwError $ CannotSynthRecFun s

check :: Ty -> Tm -> Tc ()
check ty tm = verifyCtxSubset (getSpan tm) $ case tm of
  Let x t1 t2 s -> letClause s x t1 t2 $ check ty
  Case t1 branches s -> caseClause s t1 branches $ check ty
  LetStruct con vars t1 t2 s -> letStructClause s con vars t1 t2 $ check ty
  Drop v t s -> do
    dropVar v s
    check ty t
  FunTm v mbVTy body s ->
    case ty of
      FunTy m aTy lts bTy _ -> do
        case mbVTy of
          Just vTy -> unless (vTy == aTy) $ throwError $ ExpectedType aTy vTy
          Nothing -> pure ()
        checkFun s v body m aTy lts bTy
      _ -> throwError $ ExpectedFunType ty s
  Poly b1 k1 body s1 ->
    case ty of
      Univ m lts b2 k2 bodyTy s2 -> do
        -- TODO I don't know if this should check text name.
        unless (b1.name == b2.name) $ throwError $ TypeVarBindingMismatch b1 s1 b2 s2
        unless (k1 == k2) $ throwError $ TypeKindBindingMismatch k1 s1 k2 s2
        checkPoly s1 b1 k1 body m lts bodyTy
      _ -> throwError $ ExpectedUnivType ty s1
  RecFun x funLtVar funVar body s1 ->
    case ty of
      FunTy m xTy lts bodyTy s2 -> do
        when (m == Single) $ throwError $ RecFunIsNotSingle s1 s2
        checkRecFun s1 x funLtVar funVar body xTy lts bodyTy
      _ -> throwError $ ExpectedFunType ty s1
  _ -> do
    ty' <- synth tm
    if ty == ty'
      then pure ()
      else throwError $ ExpectedButInferred ty ty' $ getSpan tm

processDecl :: Decl -> Tc ()
processDecl decl = case decl of
  FunDecl name ty body s -> do
    check ty body
    -- TODO: add check to make sure they're all multi-use
    addModuleFun s (Var name) ty
  StructDecl name args s -> do
    addDataType (Var name) $ StructType name args s
  EnumDecl tyName enumCons s -> do
    let caseM = M.fromList $ (\(EnumCon x y) -> (x,y)) <$> enumCons
    addDataType (Var tyName) $ EnumType caseM s
