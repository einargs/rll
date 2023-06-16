{-# LANGUAGE OverloadedStrings, OverloadedRecordDot, BlockArguments #-}
module Rll.TypeCheck where

import Rll.Ast
import Rll.TypeError
import Rll.Context
import Rll.Tc
import Rll.Core

import Control.Monad (unless, when, forM_, forM)
import Data.Text (Text)
import Data.Text qualified as T
import qualified Data.HashMap.Strict as M
import Control.Monad.State (MonadState(..), gets)
import Control.Monad.Except (MonadError(..))
import Data.List (find, unzip4, foldl')
import Data.Maybe (catMaybes)
import Debug.Trace qualified as D

-- | Use this to construct the type of a reference type.
createVarRef :: Var -> Span -> Tc Ty
createVarRef v s = do
  t <- lookupVar v s
  case t.tyf of
    RefTy _ _ -> throwError $ CannotRefOfRef t s
    _ -> pure ()
  alterBorrowCount v (+1)
  -- NOTE I'm pretty sure using this span makes sense, but check.
  pure $ Ty s $ RefTy (Ty s $ LtOf v) t

-- | This is used to "use" a term var. If it cannot find a term
-- var in termVars to consume, it looks in moduleTerms.
--
-- Returns the appropriate Core if it's a module variable or local
-- to the function.
useVar :: Var -> Span -> Tc Core
useVar v s = do
  ctx <- get
  case M.lookup v ctx.termVars of
    Just (borrowCount, ty) -> do
      when (borrowCount < 0) $ throwError $ CompilerLogicError "subzero borrow count" (Just s)
      unless (borrowCount == 0) $ do
        borrowers <- variablesBorrowing v
        throwError $ CannotUseBorrowedVar v borrowers s
      deleteVar v s
      pure $ Core ty s $ LocalVarCF v
    Nothing -> case M.lookup v ctx.moduleFuns of
      Just ty -> pure $ Core ty s $ ModuleVarCF v
      Nothing -> expectedTermVar v s

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

data TcMethod = Check Ty | Synth

useTcMethod :: TcMethod -> Tm -> Tc Core
useTcMethod (Check ty) = check ty
useTcMethod Synth = synth

-- | Join type checking actions on multiple branches of a case statement.
--
-- We parameterize over TcMethodResult for switching between synthesis and checking.
--
-- The span is the span of the overall case statement. Each branch has a span for the
-- body of that branch.
joinBranches :: TcMethod -> Span -> [Tc Core] -> Tc [Core]
joinBranches _ s [] = throwError $ NoCaseBranches s
joinBranches _ s [b] = pure <$> b
joinBranches method s (b:bs) = do
  ctx <- get
  core1@Core{ty=ty1, span=s1} <- b
  ctx1 <- get
  let f b = do
        put ctx
        bCore <- b
        let s = getSpan bCore
        ctx' <- get
        pure $ ((s,bCore.ty),s,ctx',bCore)
  (sTys,spans,ctxs, cores) <- unzip4 <$> traverse f bs
  let cores' = core1:cores
  unless (all (localEq ctx1) ctxs) $
    let ctxs' = diffCtxTerms $ ctx1:ctxs
        sCtxs = zip (s1:spans) ctxs'
    in throwError $ CannotJoinCtxs sCtxs s
  case method of
    Check _ -> pure cores'
    Synth -> do
      unless (all ((ty1==) . snd) sTys) $ throwError $ CannotJoinTypes ((s1,ty1):sTys) s
      pure cores'

toRef :: Span -> Ty -> Ty -> Ty
toRef s lt ty@(Ty _ (RefTy _ _)) = ty
toRef s lt ty = Ty s $ RefTy lt ty

-- | Borrow part of a data structure.
--
-- Uses toRef to ensure that if the member we borrow is a reference, we
-- just get that reference as a type instead of a reference to a reference.
addPartialBorrowVar :: Var -> Span -> Ty -> Ty -> Tc ()
addPartialBorrowVar v s lt bTy = do
  let ty = toRef s lt bTy
  addVar v s ty
  case ty.tyf of
    RefTy (Ty _ (LtOf v')) _ -> alterBorrowCount v' (+1)
    RefTy (Ty _ (TyVar _)) _ -> pure ()
    RefTy lt@(Ty _ (LtJoin _)) _ -> throwError $ RefLtIsComposite lt s
    RefTy lt _ -> throwError $ ExpectedKind LtKind TyKind $ getSpan lt
    _ -> error "toRef should ensure type is always a RefTy"

-- | Pull apart a fully applied type constructor.
--
-- Takes an error builder function and the type. Returns the type con name,
-- the type con type, and the list of arguments to it.
getTyConArgs :: (Ty -> Tc (Var, Ty, [Ty])) -> Ty -> Tc (Var, Ty, [Ty])
getTyConArgs mkErr ty = do
  tyKind <- kindOf ty
  unless (tyKind == TyKind) $ throwError $ ExpectedKind TyKind tyKind $ getSpan ty
  getArgs ty
  where
    getArgs t = case t.tyf of
      TyCon name -> pure (name, t, [])
      TyApp ty1 ty2 -> do
        (name, t, args) <- getArgs ty1
        pure $ (name, t, ty2:args)
      _ -> mkErr t

caseClause :: Span -> Tm -> [CaseBranch Tm] -> TcMethod -> Tc Core
caseClause caseSpan t1 branches tcMethod = do
  t1Core@Core{ty=t1Ty} <- synth t1
  cores <- case t1Ty.tyf of
    RefTy lt enumTy -> do
      useRef t1Ty
      (tyName,conMap) <- ensureEnum enumTy
      let f sv ty = addPartialBorrowVar sv.var sv.span lt ty
      joinBranches tcMethod caseSpan $ handleBranch f tyName conMap <$> branches
    _ -> do
      (tyName,conMap) <- ensureEnum t1Ty
      let f sv ty = addVar sv.var sv.span ty
      joinBranches tcMethod caseSpan $ handleBranch f tyName conMap <$> branches
  unless (length cores == length branches) $ throwError $
    CompilerLogicError ("cores length " <> T.pack (show (length cores)) <>
                       " branches length " <> T.pack (show (length branches)))
      (Just caseSpan)
  let f (CaseBranch con members _) core = CaseBranch con members core
      coreBranches = zipWith f branches cores
  pure $ Core (head cores).ty caseSpan $ CaseCF t1Core coreBranches
  where
    method = useTcMethod tcMethod
    ensureEnum :: Ty -> Tc (Var, M.HashMap Text [Ty])
    ensureEnum enumTy = do
      (tyName, conMap) <- getEnumCaseMap enumTy
      let hasCon t (CaseBranch v _ _) = t == v.var.name
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
      pure (tyName, conMap)
    getEnumCaseMap :: Ty -> Tc (Var, M.HashMap Text [Ty])
    getEnumCaseMap enumTy = do
      let err t = throwError $ TypeIsNotEnum t $ getSpan t1
      (tyName, conTy, args) <- getTyConArgs err enumTy
      dt <- lookupDataType tyName $ getSpan conTy
      case dt of
        EnumType _ tyParams conMap _ -> do
          pure $ (tyName, M.map (applyTypeParams args tyParams) conMap)
        _ -> throwError $ TypeIsNotEnum enumTy (getSpan t1)
    -- | Type check a branch of the case expression.
    handleBranch :: (SVar -> Ty -> Tc ()) -> Var -> M.HashMap Text [Ty] -> CaseBranch Tm -> Tc Core
    handleBranch addMember tyName conMap (CaseBranch conVar vars body) = do
      case M.lookup conVar.var.name conMap of
        Nothing -> throwError $ UnknownEnumCase tyName conVar
        Just varTys -> do
          unless (length varTys == length vars) $ throwError
            $ BadEnumCaseVars vars varTys caseSpan
          let members = zip vars varTys
          forM_ members $ uncurry addMember
          method body

-- | Take a type that should be for a fully applied struct and get the types
-- of the members with all type arguments applied.
--
-- Returns the constructor name, the struct type name, and fully applied member
-- types.
getStructMembers :: Ty -> Span -> Tc (Text, Var, [Ty])
getStructMembers ty termSpan = do
  (name, conTy, args) <- getTyConArgs (\t -> throwError $ TypeIsNotStruct t termSpan) ty
  dt <- lookupDataType name $ getSpan conTy
  case dt of
    StructType structCon' tyParams memberTys _ -> do
      pure $ (structCon', name, applyTypeParams args tyParams memberTys)
    _ -> throwError $ TypeIsNotStruct conTy termSpan

letStructClause :: Span -> SVar -> [SVar] -> Tm -> Tm -> (Tm -> Tc Core) -> Tc Core
letStructClause letSpan structCon memberVars t1 body method = do
  t1Core@Core{ty=t1Ty} <- synth t1
  bodyCore <- case t1Ty.tyf of
    RefTy lt structTy -> do
      useRef t1Ty
      let f svar ty = addPartialBorrowVar svar.var svar.span lt ty
      handle f structTy
    _ -> do
      let f svar ty = addVar svar.var svar.span ty
      handle f t1Ty
  pure $ Core bodyCore.ty letSpan $ LetStructCF structCon memberVars t1Core bodyCore
  where
    handle :: (SVar -> Ty -> Tc ()) -> Ty -> Tc Core
    handle addMember t1Ty = do
      (structCon', tyName, memberTys) <- getStructMembers t1Ty $ getSpan t1
      unless (structCon.var.name == structCon') $ throwError $
        WrongConstructor structCon.var structCon' tyName structCon.span
      unless (length memberTys == length memberVars) $
        throwError $ BadLetStructVars memberVars memberTys
      let members = zip memberVars memberTys
      forM_ members $ uncurry addMember
      method body

letClause :: Span -> SVar -> Tm -> Tm -> (Tm -> Tc Core) -> Tc Core
letClause s x t1 t2 f = do
  t1Core <- synth t1
  addVar x.var s t1Core.ty
  t2Core <- f t2
  pure $ Core t2Core.ty s $ LetCF x t1Core t2Core

-- | Given an entrance and exit context, we see which variables in the
-- entrance are no longer in the exit context (and thus have been consumed).
consumedVars :: Ctx -> Ctx -> [Var]
consumedVars c1 c2 = M.keys $ M.difference c1.termVars c2.termVars

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
  let lts = Ty s $ LtJoin $ ltSetToTypes $ ltsForClosure startCtx endCtx body
      mult = findMult startCtx endCtx
  checkStableBorrowCounts s startCtx endCtx
  incrementLts lts
  pure $ (lts, mult, out)

-- | Calculate what variables a closure needs from the context.
inferClosureEnv :: Ctx -> Ctx -> Tm -> ClosureEnv
inferClosureEnv c1 c2 body = ClosureEnv $ M.union moved refAndCopy where
  moved = (Moved . snd) <$> M.difference c1.termVars c2.termVars
  refAndCopy = M.fromList $ go body [] where
    add usage v l = case M.lookup v c1.termVars of
      Just (_, ty) -> (v, usage ty):l
      Nothing -> l
    go tm ls = case tm.tmf of
      Copy v -> add Copied v ls
      RefTm v -> add Refd v ls
      tmf -> foldr go ls tmf

-- | Synthesize a full function type for a multi-argument lambda.
synthFunTm :: Span -> Maybe SVar -> [(TyVarBinding, Kind)] -> [(SVar, Maybe Ty)]
  -> Tm -> Tc Core
synthFunTm s mbFix polyB argB body = do
  case mbFix of
    Just _ -> throwError $ CannotSynthFixTm s
    Nothing -> pure ()
  args <- mapM requireAnno argB
  let initWrap core = ([], core)
      funM = foldr foldArg (initWrap <$> synth body) args
      initPoly (funInfo, core) = ([], funInfo, core)
  ctx1 <- get
  (polyInfo, funInfo, bodyCore) <- foldr foldPoly (initPoly <$> funM) polyB
  ctx2 <- get
  let env = inferClosureEnv ctx1 ctx2 body
      funTy = foldr foldFunTy bodyCore.ty funInfo
      polyTy = foldr foldPolyTy funTy polyInfo
  pure $ Core funTy s $ LamCF mbFix polyB args env bodyCore
  where
    foldFunTy (m, aTy, lts) bTy = Ty s $ FunTy m aTy lts bTy
    foldPolyTy (m, lts, b, k) ty = Ty s $ Univ m lts b k ty
    foldArg :: (SVar, Ty) -> Tc ([(Mult, Ty, Ty)], Core) -> Tc ([(Mult, Ty, Ty)], Core)
    foldArg (v, vTy) act = do
      (lts, mult, (info, bodyCore)) <- mkClosureSynth s body do
        addVar v.var v.span vTy
        act
      pure $ ((mult, vTy, lts):info, bodyCore)
    foldPoly (b, k) act = do
      (lts, mult, (polyInfo, funInfo, bodyCore)) <- mkClosureSynth s body $
        withKind k $ act
      pure ((mult, lts, b, k):polyInfo, funInfo, bodyCore)
    requireAnno (sv, Nothing) = throwError $ SynthRequiresAnno $ sv.span
    requireAnno (sv, Just ty) = pure (sv, ty)

{-
synthFun :: Span -> SVar -> Ty -> Tm -> Tc Core
synthFun s v vTy body = do
  (lts, mult, bodyCore) <- mkClosureSynth s body do
    addVar v.var v.span vTy
    synth body
  let ty = FunTy mult vTy lts bodyCore.ty s
  pure $ Core ty s $ extendLam v vTy bodyCore

synthPoly :: Span -> TyVarBinding -> Kind -> Tm -> Tc Core
synthPoly s b kind body = do
  (lts, mult, bodyCore) <- mkClosureSynth s body $
    withKind kind $ synth body
  let ty = Univ mult lts b kind bodyCore.ty s
  pure $ Core ty s $ extendPoly b kind bodyCore
-}

-- | This is an additional check to catch compiler logic errors. It is
-- not enough on it's own.
--
-- Essentially, when using a function of any kind, this checks to make sure
-- all of the variables in the borrow list exist.
checkBorrowList :: Ty -> Span -> Tc ()
checkBorrowList ty s = do
  vars <- lifetimeVars ty
  vm <- gets (.termVars)
  unless (all (flip M.member vm) vars) $ throwError $
    CompilerLogicError "not all variables in borrow list are in scope" (Just s)

-- | Helper for verifying that borrowed variables are correct for the closure.
verifyBorrows :: Span -> Ctx -> Ctx -> Ty -> Tm -> Tc ()
verifyBorrows s startCtx endCtx lts body = do
  ltsSet <- lifetimeSet lts
  let vars = ltSetToVars inferredLtSet
  unless (ltsSet == inferredLtSet) $ throwError $
    IncorrectBorrowedVars lts (ltSetToTypes inferredLtSet) s
  incrementLts lts
  -- forM_ vars $ flip alterBorrowCount (+1)
  where
    inferredLtSet = ltsForClosure startCtx endCtx body

-- | Helper for building closure checks.
mkClosureCheck :: Span -> Tm -> Mult -> Ty -> Tc a -> Tc a
mkClosureCheck s body mult lts m = do
  startCtx <- get
  val <- m
  endCtx <- get

  -- Check specified lifetimes
  verifyBorrows s startCtx endCtx lts body

  -- Check multiplicity if Many is specified
  verifyMult s mult startCtx endCtx

  checkStableBorrowCounts s startCtx endCtx

  pure val

  {-
  FunTm v mbVTy body s ->
    case ty of
      FunTy m aTy lts bTy _ -> do
        checkBorrowList lts s
        case mbVTy of
          Just vTy -> unless (vTy == aTy) $ throwError $ ExpectedType aTy vTy
          Nothing -> pure ()
        bodyCore <- checkFun s v body m aTy lts bTy
        cf $ extendLam v aTy bodyCore
      _ -> throwError $ ExpectedFunType ty s
  Poly mbBind body s1 ->
    case ty of
      Univ m lts b2 k2 bodyTy s2 -> do
        checkBorrowList lts s1
        forM_ mbBind \(b1,k1) -> do
          -- NOTE I don't know if this should check text name.
          unless (b1.name == b2.name) $ throwError $ TypeVarBindingMismatch b1 s1 b2 s2
          unless (k1 == k2) $ throwError $ TypeKindBindingMismatch k1 s1 k2 s2
        bodyCore <- checkPoly s1 b2 k2 body m lts bodyTy
        cf $ extendPoly b2 k2 bodyCore
      _ -> throwError $ ExpectedUnivType ty s1
  FixTm funVar body s1 -> do
    bodyCore <- case ty of
      FunTy m xTy lts bodyTy s2 -> do
        checkBorrowList lts s1
        checkFixTm s1 m funVar body ty
      Univ m lts bind kind bodyTy s2 -> do
        checkBorrowList lts s1
        checkFixTm s1 m funVar body ty
      _ -> throwError $ ExpectedFixableType ty s1
    cf $ extendFix funVar bodyCore
  -}

checkFunTm :: Span -> Maybe SVar -> [(TyVarBinding, Kind)]
  -> [(SVar, Maybe Ty)] -> Tm -> Ty -> Tc Core
checkFunTm s mbFix polyB argB body ty = withFix mbFix $
  withPoly polyB ty $ withArgs argB $ flip check body
  where
    withPoly :: [(TyVarBinding, Kind)] -> Ty -> (Ty -> Tc ([(SVar, Ty)], Core)) -> Tc Core
    withPoly tyArgs fullTy cont = do
      let (baseTy, polyLayers) = extractPolyLayers fullTy
      -- We check that the type information lines up with our type arguments.
      -- If we have no type arguments in the lambda, we're doing full inference.
      when (length tyArgs > 0) do
        unless (length tyArgs == length polyLayers) $
          throwError $ PartialTyArgsInLam fullTy s
        forM_ (zip tyArgs polyLayers) \((b1,k1), (_,_,b2,k2,s2)) -> do
            unless (b1.name == b2.name) $ throwError $ TypeVarBindingMismatch b1 s b2 s2
            unless (k1 == k2) $ throwError $ TypeKindBindingMismatch k1 s k2 s2
      ctx1 <- get
      (args, bodyCore) <- foldr foldLayer (cont baseTy) polyLayers
      ctx2 <- get
      let env = inferClosureEnv ctx1 ctx2 body
          tyArgs' = (\(_,_,b,k,_) -> (b,k)) <$> polyLayers
      pure $ Core fullTy s $ LamCF mbFix tyArgs' args env bodyCore
      where
        foldLayer :: (Mult, Ty, TyVarBinding, Kind, Span)
          -> Tc ([(SVar, Ty)], Core) -> Tc ([(SVar, Ty)], Core)
        foldLayer (m, lts, b, k, s2) act =
          mkClosureCheck s body m lts $ withKind k act
        -- | We pull out a list of all the important information about layered
        -- Univ types.
        extractPolyLayers :: Ty -> (Ty, [(Mult, Ty, TyVarBinding, Kind, Span)])
        extractPolyLayers ty@Ty{span, tyf} = case tyf of
          Univ m lts b k bodyTy ->
            let (ty', layers) = extractPolyLayers bodyTy
            in (ty', (m, lts, b, k, span):layers)
          _ -> (ty, [])

    withArgs :: [(SVar, Maybe Ty)] -> (Ty -> Tc Core) -> Ty -> Tc ([(SVar, Ty)], Core)
    withArgs args cont funTy = do
      let (baseTy, tyLayers) = extractTyLayers (length args) funTy
      unless (length tyLayers == length args) $ throwError $
        TooManyArgsInLam funTy s
      layers <- forM (zip args tyLayers) \((v,mbTy), (m,aTy,lts,tySpan)) -> do
        case mbTy of
          Just vTy -> unless (vTy == aTy) $ throwError $ ExpectedType aTy vTy
          Nothing -> pure ()
        pure (v,m,aTy,lts,tySpan)
      bodyCore <- foldr foldLayer (cont baseTy) layers
      let args' = fmap (\(v,_,vTy,_,_) -> (v,vTy)) layers
      pure (args', bodyCore)
      where
        foldLayer (v, m, vTy, lts, tySpan) act =
          mkClosureCheck s body m lts do
            addVar v.var v.span vTy
            act
        extractTyLayers :: Int -> Ty -> (Ty, [(Mult, Ty, Ty, Span)])
        extractTyLayers i ty@Ty{span, tyf}
          | i > 0 = case tyf of
            FunTy m aTy lts bTy ->
              let (baseTy, layers) = extractTyLayers (i-1) bTy
              in (baseTy, (m,aTy,lts,span):layers)
            _ -> (ty, [])
          | otherwise = (ty, [])

    withFix :: Maybe SVar -> Tc Core -> Tc Core
    withFix Nothing act = act
    withFix (Just funVar) act = do
      mult <- case ty.tyf of
        Univ m _ _ _ _ -> pure m
        FunTy m _ _ _ -> pure m
        _ -> throwError $ ExpectedFixableType ty s
      when (mult == Single) $ throwError $ CannotFixSingle s $ ty.span
      let fLt = Ty funVar.span $ LtJoin []
          refTy = Ty funVar.span $ RefTy fLt ty
      addVar funVar.var funVar.span refTy
      bodyCore <- act
      dropVar funVar.var funVar.span
      pure bodyCore

{-
checkFun :: Span -> SVar -> Tm -> Mult -> Ty -> Ty -> Ty -> Tc Core
checkFun s v body mult aTy lts bTy = mkClosureCheck s body mult lts do
  addVar v.var v.span aTy
  check bTy body

checkPoly :: Span -> TyVarBinding -> Kind -> Tm -> Mult -> Ty -> Ty -> Tc Core
checkPoly s b kind body mult lts bodyTy = mkClosureCheck s body mult lts do
  withKind kind $ check bodyTy body

checkFixTm :: Span -> Mult -> SVar -> Tm -> Ty -> Tc Core
checkFixTm s mult funVar body bodyTy = do
  when (mult == Single) $ throwError $ CannotFixSingle s $ getSpan bodyTy
  withKind LtKind do
    -- fLt is essentially static. Even if the reference escapes, the lts
    -- stuff will keep it from being used wrong.
    let fLt = Ty funVar.span $ LtJoin []
        refTy = Ty funVar.span $ RefTy fLt bodyTy
    addVar funVar.var funVar.span refTy
    bodyCore <- check bodyTy body
    dropVar funVar.var funVar.span
    pure bodyCore
-}

-- | Synthesize the type of a type application.
synthAppTy :: Tm -> [Ty] -> Span -> Tc Core
synthAppTy t1 tys s = do
  t1Core <- synth t1
  ty <- foldl' applyTy (pure t1Core.ty) tys
  case ty.tyf of
    Univ _ _ _ _ _ -> throwError $ NotFullyApplied ty s
    _ -> pure ()
  pure $ Core ty s $ AppTyCF t1Core tys
  where
  applyTy baseTyM tyArg = do
    baseTy <- baseTyM
    (k, body) <- case baseTy.tyf of
      Univ _ lts v k body -> do
        decrementLts lts
        pure (k, body)
      RefTy l (Ty _ (Univ Many lts v k body)) -> do
        useRef baseTy
        pure (k, body)
      _ -> throwError $ TyIsNotUniv baseTy s
    k' <- kindOf tyArg
    unless (k == k') $ throwError $ ExpectedKind k k' $ getSpan tyArg
    incRef body
    pure $ typeSub tyArg body

synth :: Tm -> Tc Core
synth tm@Tm{span=s, tmf} = verifyCtxSubset (getSpan tm) $ case tmf of
  Drop sv t -> do
    dropVar sv.var sv.span
    tCore <- synth t
    pure $ Core tCore.ty s $ DropCF sv tCore
  LetStruct con vars t1 t2 -> letStructClause s con vars t1 t2 synth
  TmCon v -> do
    (dt, ty) <- lookupDataCon v s
    pure $ Core ty s $ ConCF dt v
  Anno t ty -> do
    sanityCheckType ty
    check ty t
  TmVar v -> useVar v s
  Copy v -> do
    vTy <- lookupVar v s
    case vTy.tyf of
      RefTy (Ty _ (LtOf v')) _ -> do
        alterBorrowCount v' (+1)
        pure $ Core vTy s $ CopyCF v
      RefTy _ _ -> pure $ Core vTy s $ CopyCF v
      _ -> throwError $ CannotCopyNonRef vTy s
  RefTm v -> do
    ty <- createVarRef v s
    pure $ Core ty s $ RefCF v
  Let sv t1 t2 -> letClause sv.span sv t1 t2 synth
  Case t1 branches -> caseClause s t1 branches Synth
  -- ltOfFVar is the name of the variable used for the lifetime of the variable f, which is
  -- a reference to this function itself.
  -- FixTm _ _ s -> throwError $ CannotSynthFixTm s
  FunTm fixVar polyB argB body -> synthFunTm s fixVar polyB argB body
  AppTy t1 tyArgs -> synthAppTy t1 tyArgs s
  AppTm t1 t2 -> do
    -- Roughly we synthesize t1 and use that to check t2.
    t1Core@Core{ty=t1Ty} <- synth t1
    case t1Ty.tyf of
      -- We allow consumption of both single and multi-use functions.
      FunTy _ aTy lts bTy -> do
        checkBorrowList lts s
        t2Core <- check aTy t2
        useRef aTy
        decrementLts lts
        incRef bTy
        pure $ Core bTy s $ extendAppTm t1Core t2Core
      RefTy lt (Ty _ (FunTy Many aTy lts bTy)) -> do
        checkBorrowList lts s
        t2Core <- check aTy t2
        useRef aTy
        useRef t1Ty
        incRef bTy
        pure $ Core bTy s $ extendAppTm t1Core t2Core
      _ -> throwError $ TyIsNotFun t1Ty $ getSpan t1
  LiteralTm lit ->
    let ty = case lit of
          IntLit _ -> Ty s $ TyCon (Var "I64")
          StringLit _ -> Ty s $ TyCon (Var "String")
    in pure $ Core ty s $ LiteralCF lit

check :: Ty -> Tm -> Tc Core
check ty tm@Tm{span=s, tmf} = verifyCtxSubset s $ case tmf of
  Let sv t1 t2 -> letClause sv.span sv t1 t2 $ check ty
  Case t1 branches -> caseClause s t1 branches $ Check ty
  LetStruct con vars t1 t2 -> letStructClause s con vars t1 t2 $ check ty
  Drop sv t -> do
    dropVar sv.var sv.span
    tCore <- check ty t
    cf $ DropCF sv tCore
  FunTm mbFix polyB argB body -> checkFunTm s mbFix polyB argB body ty
  _ -> do
    tmCore@Core{ty=ty'} <- synth tm
    if ty == ty'
      then pure tmCore
      else throwError $ ExpectedButInferred ty ty' $ getSpan tm
  where
    cf = pure . Core ty (getSpan tm)

-- TODO: write a helper function that will run the entire type check monad for this
-- and give me a context with the data types and new functions.
-- data CoreContext = CoreContext [DataType] [(Var, Core)]
-- generateCore :: [Decl] -> CoreContext

-- | Type checks all declarations in the file and generates the Core IR
-- for all of the functions.
typeCheckFile :: [Decl] -> Tc [(Var, Core)]
typeCheckFile = fmap catMaybes . mapM go where
  go decl = case decl of
    FunDecl name ty body s -> do
      ctx <- get
      ty' <- indexTyVars ty
      sanityCheckType ty'
      body' <- indexTyVarsInTm body
      D.traceM $ "body: " <> show body'
      core <- check ty' body'
      put ctx
      addModuleFun s (Var name) ty'
      pure $ Just (Var name, core)
    StructDecl name tyParams args s -> do
      indexedArgs <- indexArgs tyParams args
      addDataType (Var name) $ StructType name tyParams indexedArgs s
      pure Nothing
    EnumDecl tyName tyParams enumCons s -> do
      enumCons' <- forM enumCons \(EnumCon x y) -> (x,) <$> indexArgs tyParams y
      let caseM = M.fromList enumCons'
      addDataType (Var tyName) $ EnumType tyName tyParams caseM s
      pure Nothing
    where
      indexArgs :: [TypeParam] -> [Ty] -> Tc [Ty]
      indexArgs tyParams tys = traverse f tys where
        f = rawIndexTyVars (length tyParams - 1) $ M.fromList $ zip ((.name) <$> reverse tyParams) [0..]
