{-# LANGUAGE OverloadedStrings, OverloadedRecordDot, BlockArguments #-}
module Rll.TypeCheck where

import Rll.Ast
import Rll.TypeError
import Rll.Context
import Rll.Tc

import Control.Monad (unless, when, forM_, void, forM)
import Data.Text (Text, pack, unpack)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Data.Set as TS
import Control.Monad.State (MonadState(..), StateT, modify', runStateT, gets)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Data.Maybe (fromMaybe, mapMaybe)
import Control.Arrow (first, second)
import Data.Function (on)
import Data.Functor (($>))
import qualified Data.List as L
import qualified Debug.Trace as T
import Data.List (find, foldl')
import Safe (atMay)
import Data.Foldable (foldlM)

-- | Use this to construct the type of a reference type.
createVarRef :: Var -> Span -> Tc Ty
createVarRef v s = do
  t <- lookupVar v s
  case t of
    RefTy _ _ _ -> throwError $ CannotRefOfRef t s
    _ -> pure ()
  alterBorrowCount v (+1)
  -- NOTE I'm pretty sure using this span makes sense, but check.
  pure $ RefTy (LtOf v s) t s

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

-- | This is used to "use" a term var. If it cannot find a term
-- var in termVars to consume, it looks in moduleTerms.
useVar :: Var -> Span -> Tc Ty
useVar v s = do
  ctx <- get
  case M.lookup v ctx.termVars of
    Just (borrowCount, ty) -> do
      when (borrowCount < 0) $ throwError $ CompilerLogicError "subzero borrow count" (Just s)
      unless (borrowCount == 0) $ do
        borrowers <- variablesBorrowing v
        throwError $ CannotUseBorrowedVar v borrowers s
      deleteVar v s
      pure ty
    Nothing -> case M.lookup v ctx.moduleTerms of
      Just ty -> pure ty
      Nothing -> expectedTermVar v s

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

data TcMethod a where
  Check :: TcMethod ()
  Synth :: TcMethod Ty

class Eq a => TcMethodResult a where
  getTcMethod :: TcMethod a

instance TcMethodResult Ty where
  getTcMethod = Synth

instance TcMethodResult () where
  getTcMethod = Check

-- | Join type checking actions on multiple branches of a case statement.
--
-- We parameterize over TcMethodResult for switching between synthesis and checking.
--
-- The span is the span of the overall case statement. Each branch has a span for the
-- body of that branch.
joinBranches :: forall a. TcMethodResult a => Span -> [(Span, Tc a)] -> Tc a
joinBranches s [] = throwError $ NoCaseBranches s
joinBranches s [(_,b)] = b
joinBranches s ((s1,b):bs) = do
  ctx <- get
  ty1 <- b
  ctx1 <- get
  let f (s,b) = do
        put ctx
        bTy <- b
        ctx' <- get
        pure $ ((s,bTy),s,ctx')
  (sTys,spans,ctxs) <- unzip3 <$> traverse f bs
  unless (all (localEq ctx1) ctxs) $
    let ctxs' = diffCtxTerms $ ctx1:ctxs
        sCtxs = zip (s1:spans) ctxs'
    in throwError $ CannotJoinCtxs sCtxs s
  case getTcMethod @a of
    Check -> pure ()
    Synth -> do
      unless (all ((ty1==) . snd) sTys) $ throwError $ CannotJoinTypes ((s1,ty1):sTys) s
      pure ty1

toRef :: Span -> Ty -> Ty -> Ty
toRef s lt ty@(RefTy _ _ _) = ty
toRef s lt ty = RefTy lt ty s

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
    RefTy lt _ _ -> throwError $ ExpectedKind LtKind TyKind $ getSpan lt
    _ -> error "toRef should ensure type is always a RefTy"

-- | Substitute for the type parameter variables inside the fields of a
-- data type.
applyTypeParams :: [Ty] -> [TypeParam] -> [Ty] -> [Ty]
applyTypeParams args params members = go (length args - 1) args params members where
  go i [] [] members = members
  go i (a:as) (p:ps) members = go (i-1) as ps $
    rawTypeSub i a <$> members
  go i _ _ _ = error "Should be caught by kind check"

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
    getArgs t@(TyCon name s) = pure (name, t, [])
    getArgs (TyApp ty1 ty2 _) = do
      (name, t, args) <- getArgs ty1
      pure $ (name, t, ty2:args)
    getArgs t = mkErr t

caseClause :: forall a. TcMethodResult a => Span -> Tm -> [CaseBranch] -> (Tm -> Tc a) -> Tc a
caseClause caseSpan t1 branches method = do
  t1Ty <- synth t1
  case t1Ty of
    RefTy lt enumTy _ -> do
      useRef t1Ty
      (tyName,conMap) <- ensureEnum enumTy
      let f sv ty = addPartialBorrowVar sv.var sv.span lt ty
      joinBranches caseSpan $ buildHandler f tyName conMap <$> branches
    _ -> do
      (tyName,conMap) <- ensureEnum t1Ty
      let f sv ty = addVar sv.var sv.span ty
      joinBranches caseSpan $ buildHandler f tyName conMap <$> branches
  where
    -- | Just here to extract the span and package it nicely alongside the handleBranch result.
    buildHandler :: (SVar -> Ty -> Tc ()) -> Var -> M.HashMap Text [Ty] -> CaseBranch -> (Span, Tc a)
    buildHandler addMember tyName conMap cb@(CaseBranch _ _ body) =
      (getSpan body, handleBranch addMember tyName conMap cb)
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
        StructType _ _ _ _ -> throwError $ TypeIsNotEnum enumTy (getSpan t1)
        EnumType tyParams conMap _ -> do
          pure $ (tyName, M.map (applyTypeParams args tyParams) conMap)
    handleBranch :: (SVar -> Ty -> Tc ()) -> Var -> M.HashMap Text [Ty] -> CaseBranch -> Tc a
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
    EnumType _ _ _ -> throwError $ TypeIsNotStruct conTy termSpan
    StructType structCon' tyParams memberTys _ -> do
      pure $ (structCon', name, applyTypeParams args tyParams memberTys)

letStructClause :: forall a. Span -> SVar -> [SVar] -> Tm -> Tm -> (Tm -> Tc a) -> Tc a
letStructClause letSpan structCon memberVars t1 body method = do
  t1Ty <- synth t1
  case t1Ty of
    RefTy lt structTy _ -> do
      useRef t1Ty
      let f svar ty = T.trace (show svar.var <> ": " <> show ty) $ addPartialBorrowVar svar.var svar.span lt ty
      handle f structTy
    _ -> do
      let f svar ty = addVar svar.var svar.span ty
      handle f t1Ty
  where
    handle :: (SVar -> Ty -> Tc ()) -> Ty -> Tc a
    handle addMember t1Ty = do
      (structCon', tyName, memberTys) <- getStructMembers t1Ty $ getSpan t1
      unless (structCon.var.name == structCon') $ throwError $
        WrongConstructor structCon.var structCon' tyName structCon.span
      unless (length memberTys == length memberVars) $
        throwError $ BadLetStructVars memberVars memberTys
      let members = zip memberVars memberTys
      forM_ members $ uncurry addMember
      method body

letClause :: Span -> Var -> Tm -> Tm -> (Tm -> Tc a) -> Tc a
letClause s x t1 t2 f = do
  xTy <- synth t1
  addVar x s xTy
  f t2

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
  let lts = flip LtJoin s $ ltSetToTypes $ ltsForClosure startCtx endCtx body
      mult = findMult startCtx endCtx
  checkStableBorrowCounts s startCtx endCtx
  incrementLts lts
  pure $ (lts, mult, out)

synthFun :: Span -> SVar -> Ty -> Tm -> Tc Ty
synthFun s v vTy body = do
  (lts, mult, bodyTy) <- mkClosureSynth s body do
    addVar v.var v.span vTy
    synth body
  pure $ FunTy mult vTy lts bodyTy s

synthPoly :: Span -> TyVarBinding -> Kind -> Tm -> Tc Ty
synthPoly s b kind body = do
  (lts, mult, bodyTy) <- mkClosureSynth s body $
    withKind kind $ synth body
  pure $ Univ mult lts b kind bodyTy s

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
mkClosureCheck :: Span -> Tm -> Mult -> Ty -> Tc () -> Tc ()
mkClosureCheck s body mult lts m = do
  startCtx <- get
  m
  endCtx <- get

  -- Check specified lifetimes
  verifyBorrows s startCtx endCtx lts body

  -- Check multiplicity if Many is specified
  verifyMult s mult startCtx endCtx

  checkStableBorrowCounts s startCtx endCtx

checkFun :: Span -> SVar -> Tm -> Mult -> Ty -> Ty -> Ty -> Tc ()
checkFun s v body mult aTy lts bTy = mkClosureCheck s body mult lts do
  addVar v.var v.span aTy
  check bTy body

checkPoly :: Span -> TyVarBinding -> Kind -> Tm -> Mult -> Ty -> Ty -> Tc ()
checkPoly s b kind body mult lts bodyTy = mkClosureCheck s body mult lts do
  withKind kind $ check bodyTy body

checkFixTm :: Span -> Mult -> SVar -> Tm -> Ty -> Tc ()
checkFixTm s mult funVar body bodyTy = do
  when (mult == Single) $ throwError $ CannotFixSingle s $ getSpan bodyTy
  withKind LtKind do
    -- fLt is essentially static. Even if the reference escapes, the lts
    -- stuff will keep it from being used wrong.
    let fLt = LtJoin [] funVar.span
        refTy = RefTy fLt bodyTy funVar.span
    addVar funVar.var funVar.span refTy
    check bodyTy body
    dropVar funVar.var funVar.span

synth :: Tm -> Tc Ty
synth tm = verifyCtxSubset (getSpan tm) $ case tm of
  Drop sv t s -> do
    dropVar sv.var sv.span
    synth t
  LetStruct con vars t1 t2 s -> letStructClause s con vars t1 t2 synth
  TmCon v s -> lookupDataCon v s
  Anno t ty _ -> do
    sanityCheckType ty
    check ty t
    pure ty
  TmVar v s -> useVar v s
  Copy v s -> do
    vTy <- lookupVar v s
    case vTy of
      RefTy (LtOf v' _ ) _ _ -> do
        alterBorrowCount v' (+1)
        pure vTy
      RefTy _ _ _ -> pure vTy
      _ -> throwError $ CannotCopyNonRef vTy s
  RefTm v s -> createVarRef v s
  Let sv t1 t2 s -> letClause sv.span sv.var t1 t2 synth
  Case t1 branches s -> caseClause s t1 branches synth
  FunTm v (Just vTy) body s -> synthFun s v vTy body
  FunTm _ Nothing _ s -> throwError $ SynthRequiresAnno s
  Poly (Just (v,kind)) body s -> synthPoly s v kind body
  Poly Nothing _ s -> throwError $ SynthRequiresAnno s
  AppTy t1 tyArg s -> do
    t1Ty <- synth t1
    case t1Ty of
      Univ _ lts v k body _ -> do
        k' <- kindOf tyArg
        unless (k == k') $ throwError $ ExpectedKind k k' $ getSpan tyArg
        decrementLts lts
        incRef body
        pure $ typeSub tyArg body
      RefTy l (Univ Many lts v k body _) _ -> do
        useRef t1Ty
        incRef body
        pure $ typeSub tyArg body
      _ -> throwError $ TyIsNotUniv t1Ty s
  AppTm t1 t2 s -> do
    -- Roughly we synthesize t1 and use that to check t2.
    t1Ty <- synth t1
    case t1Ty of
      -- We allow consumption of both single and multi-use functions.
      FunTy _ aTy lts bTy _ -> do
        checkBorrowList lts s
        check aTy t2
        useRef aTy
        decrementLts lts
        incRef bTy
        pure bTy
      RefTy lt (FunTy Many aTy lts bTy _) _ -> do
        checkBorrowList lts s
        check aTy t2
        useRef aTy
        useRef t1Ty
        incRef bTy
        pure bTy
      _ -> throwError $ TyIsNotFun t1Ty $ getSpan t1
  -- ltOfFVar is the name of the variable used for the lifetime of the variable f, which is
  -- a reference to this function itself.
  FixTm _ _ s -> throwError $ CannotSynthFixTm s

check :: Ty -> Tm -> Tc ()
check ty tm = verifyCtxSubset (getSpan tm) $ case tm of
  Let sv t1 t2 s -> letClause sv.span sv.var t1 t2 $ check ty
  Case t1 branches s -> caseClause s t1 branches $ check ty
  LetStruct con vars t1 t2 s -> letStructClause s con vars t1 t2 $ check ty
  Drop sv t s -> do
    dropVar sv.var sv.span
    check ty t
  FunTm v mbVTy body s ->
    case ty of
      FunTy m aTy lts bTy _ -> do
        checkBorrowList lts s
        case mbVTy of
          Just vTy -> unless (vTy == aTy) $ throwError $ ExpectedType aTy vTy
          Nothing -> pure ()
        checkFun s v body m aTy lts bTy
      _ -> throwError $ ExpectedFunType ty s
  Poly mbBind body s1 ->
    case ty of
      Univ m lts b2 k2 bodyTy s2 -> do
        checkBorrowList lts s1
        forM_ mbBind \(b1,k1) -> do
          -- NOTE I don't know if this should check text name.
          unless (b1.name == b2.name) $ throwError $ TypeVarBindingMismatch b1 s1 b2 s2
          unless (k1 == k2) $ throwError $ TypeKindBindingMismatch k1 s1 k2 s2
        checkPoly s1 b2 k2 body m lts bodyTy
      _ -> throwError $ ExpectedUnivType ty s1
  FixTm funVar body s1 ->
    case ty of
      FunTy m xTy lts bodyTy s2 -> do
        checkBorrowList lts s1
        checkFixTm s1 m funVar body ty
      Univ m lts bind kind bodyTy s2 -> do
        checkBorrowList lts s1
        checkFixTm s1 m funVar body ty
      _ -> throwError $ ExpectedFixableType ty s1
  _ -> do
    ty' <- synth tm
    if ty == ty'
      then pure ()
      else throwError $ ExpectedButInferred ty ty' $ getSpan tm

processDecl :: Decl -> Tc ()
processDecl decl = case decl of
  FunDecl name ty body s -> do
    ctx <- get
    ty' <- indexTyVars ty
    sanityCheckType ty'
    body' <- indexTyVarsInTm body
    check ty' body'
    put ctx
    addModuleFun s (Var name) ty'
  StructDecl name tyParams args s -> do
    indexedArgs <- indexArgs tyParams args
    addDataType (Var name) $ StructType name tyParams indexedArgs s
  EnumDecl tyName tyParams enumCons s -> do
    enumCons' <- forM enumCons \(EnumCon x y) -> (x,) <$> indexArgs tyParams y
    let caseM = M.fromList enumCons'
    addDataType (Var tyName) $ EnumType tyParams caseM s
  where
    indexArgs :: [TypeParam] -> [Ty] -> Tc [Ty]
    indexArgs tyParams tys = traverse f tys where
      f = rawIndexTyVars (length tyParams - 1) $ M.fromList $ zip ((.name) <$> reverse tyParams) [0..]
