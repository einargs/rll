{-# LANGUAGE OverloadedStrings, OverloadedRecordDot #-}
module Rll.TypeCheck where

import Rll.Ast

import Control.Monad (unless, when, forM_)
import Data.Text (Text, pack)
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import Control.Monad.State (MonadState(..), StateT, modify', runStateT)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Data.Maybe (fromMaybe)
import Control.Arrow (first, second)
import Data.Function (on)
import Data.Functor (($>))
import qualified Data.List as L
import qualified Debug.Trace as T

-- TODO: rename to termVars and typeVars
-- | Only typeCtx is actual de-brujin indices that get shifted. As such, varNames
-- only applies to termCtx for now.
data Ctx = Ctx { termCtx :: M.IntMap (Int, Ty), typeCtx :: M.IntMap Kind, varNames :: M.IntMap Text }
  deriving (Show)

instance Eq Ctx where
  (Ctx tm ty vn) == (Ctx tm' ty' vn') = tm == tm' && ty == ty'

onTermCtx :: (M.IntMap (Int, Ty) -> M.IntMap (Int, Ty)) -> Ctx -> Ctx
onTermCtx f (Ctx vm tm vn) = Ctx (f vm) tm vn

-- Shadowing references doesn't matter; we can drop an external one, or return a value
-- that borrows a variable.
-- TODO: I think I need to compare the borrow counts and make sure a2 has lower or equal borrow counts.
-- Is the first ctx a subset of the second ctx.
subsetOf :: Ctx -> Ctx -> Bool
subsetOf (Ctx a1 b1 _) (Ctx a2 b2 _) = M.isSubmapOfBy f a1 a2 && b1 == b2 -- M.isSubmapOf (M.map snd a1) (M.map snd a2) && b1 == b2
  where
    f :: (Int, Ty) -> (Int, Ty) -> Bool
    f (i1, t1) (i2, t2) = t1 == t2

data TyErr = TyErr Text deriving (Eq, Show)

newtype Tc a = MkTc { unTc :: StateT Ctx (Except TyErr) a }
  deriving (Functor, Applicative, Monad, MonadError TyErr, MonadState Ctx)

traceCtx :: String -> Tc ()
traceCtx name = do
  Ctx tm _ _ <- get
  T.traceM $ name <> ": " <> show tm

emptyCtx :: Ctx
emptyCtx = Ctx M.empty M.empty M.empty

runTc :: Ctx -> Tc a -> Either TyErr a
runTc ctx = fmap fst . runExcept . flip runStateT ctx . unTc

tyErr :: Text -> Tc a
tyErr = throwError . TyErr

varErr :: Var -> Text -> Tc a
varErr (Var n i) txt = tyErr $ "Var " <> n <> "@" <> pack (show i) <> ": " <> txt

lookupEntry :: Var -> Tc (Int, Ty)
lookupEntry v@(Var _ i) = do
  (Ctx m _ _) <- get
  case M.lookup i m of
    Nothing -> do
      varErr v "does not exist."
    Just e -> pure e

lookupVar :: Var -> Tc Ty
lookupVar v = snd <$> lookupEntry v

alterBorrowCount :: Var -> (Int -> Int) -> Tc ()
alterBorrowCount v@(Var _ i) f = modify' $ onTermCtx $ M.adjust (first f) i

-- | Use this to construct the type of a reference type.
borrowVar :: Var -> Tc Ty
borrowVar v = do
  t <- lookupVar v
  alterBorrowCount v (+1)
  pure $ RefTy (LtOf v) t

addVar :: Var -> Ty -> Tc ()
addVar v@(Var name i) ty = do
  (Ctx m tm vn) <- get
  case M.lookup i m of
    Just _ -> varErr v "already exists"
    Nothing -> put $ Ctx (M.insert i (0, ty) m) tm (M.insert i name vn)

lifetimeVars :: Ty -> Tc [Var]
lifetimeVars (LtOf v) = pure [v]
lifetimeVars (LtJoin ls) = concat <$> traverse lifetimeVars ls
lifetimeVars _ = tyErr "Not a lifetime."

decrementLts :: Ty -> Tc ()
decrementLts lty = lifetimeVars lty >>= mapM_ (flip alterBorrowCount (subtract 1))

dropVar :: Var -> Tc ()
dropVar v@(Var _ i) = do
  (borrowCount, ty) <- lookupEntry v
  unless (borrowCount == 0) $ varErr v "is still borrowed."
  case ty of
    RefTy l _ -> decrementLts l
    Univ Many l _ _ _ -> decrementLts l
    FunTy Many _ l _ -> decrementLts l
    _ -> varErr v "cannot be dropped."
  modify' $ onTermCtx $ M.delete i

useVar :: Var -> Tc Ty
useVar v@(Var _ i) = do
  (borrowCount, ty) <- lookupEntry v
  unless (borrowCount == 0) $ do
    (Ctx tm _ _) <- get
    varErr v "is still borrowed."
  modify' $ onTermCtx $ M.delete i
  pure ty

-- | Utility function for decrementing the lifetime of references when
-- using stuff.
--
-- This is about when a reference, a kind of value is used; useVar is about when
-- a variable is consumed.
useRef :: Ty -> Tc ()
useRef ty = do
  case ty of
    RefTy l _ -> decrementLts l
    _ -> pure ()

-- | Utility function to drop kinds from the type context automatically.
withKind :: Var -> Kind -> Tc a -> Tc a
withKind v@(Var _ i) k m = do
  ctx <- get
  case M.lookup i ctx.typeCtx of
    Just _ -> error "Overlapping de-brujin indicies compiler logic error"
    Nothing -> pure ()
  put $ ctx {typeCtx=M.insert i k ctx.typeCtx }
  val <- m
  modify' $ \c -> c{typeCtx=M.delete i c.typeCtx }
  pure val

verifyCtxSubset :: Tc a -> Tc a
verifyCtxSubset m = do
  ctx1 <- get
  v <- m
  ctx2 <- get
  unless (ctx2 `subsetOf` ctx1) $ tyErr $ "Output ctx should be a subset of input context. Input: " <> pack (show ctx1) <> " Output: " <> pack (show ctx2)
  pure v

joinSides :: Eq a => Tc a -> Tc a -> Tc a
joinSides s1 s2 = do
  ctx <- get
  ty1 <- s1
  ctx1 <- get
  put ctx
  ty2 <- s2
  ctx2 <- get
  unless (ctx1 == ctx2) $ tyErr "Sides don't match"
  unless (ty1 == ty2) $ tyErr "Types don't match"
  pure ty1

withVar :: Var -> Ty -> Tc a -> Tc a
withVar v ty m = addVar v ty >> m

toRef :: Ty -> Ty -> Ty
toRef lt ty@(RefTy _ _) = ty
toRef lt ty = RefTy lt ty

-- TODO rewrite a bunch of this using recursion schemes.
typeSub :: Ty -> Ty -> Ty
typeSub = sub 0
  where
    sub xi arg target = case target of
      UnitTy -> UnitTy
      SumTy a b -> SumTy (f a) (f b)
      ProdTy a b -> ProdTy (f a) (f b)
      LtOf v -> LtOf v
      TyVar v@(Var _ vi) -> if vi == xi then arg else TyVar v
      FunTy m a b c -> FunTy m (f a) (f b) (f c)
      LtJoin ts -> LtJoin $ f <$> ts
      RefTy a b -> RefTy (f a) (f b)
      Univ m lts v k body -> Univ m (f lts) v k $ sub (xi+1) (shift 1 0 arg) body
      where f = sub xi arg
    shift :: Int -> Int -> Ty -> Ty
    shift i c ty = case ty of
      UnitTy -> UnitTy
      SumTy a b -> SumTy (f a) (f b)
      ProdTy a b -> ProdTy (f a) (f b)
      LtOf v -> LtOf v
      TyVar (Var t n) -> TyVar $ Var t $ if n < c then n else n+i
      FunTy m a b c -> FunTy m (f a) (f b) (f c)
      LtJoin ts -> LtJoin $ f <$> ts
      RefTy a b -> RefTy (f a) (f b)
      Univ m lts v k body -> Univ m (f lts) v k $ shift i (c+1) body
      where f = shift i c

addPartialBorrowVar :: Var -> Ty -> Ty -> Tc ()
addPartialBorrowVar v lt bTy = do
  let ty = toRef lt bTy
  addVar v ty
  case ty of
    RefTy (LtOf v') _ -> alterBorrowCount v' (+1)
    _ -> error "No other possiblity should be valid"

caseClause :: Eq a => Mult -> Tm -> Var -> Tm -> Var -> Tm -> (Tm -> Tc a) -> Tc a
caseClause Single t1 x t2 y t3 f = do
  t1Ty <- synth t1
  case t1Ty of
    SumTy xTy yTy -> joinSides (addVar x xTy >> f t2) (addVar y yTy >> f t3)
    _ -> tyErr "Owning case used on non-sum type"
caseClause Many t1 x t2 y t3 f = do
  t1Ty <- synth t1
  useRef t1Ty
  case t1Ty of
    RefTy lt (SumTy xBTy yBTy) ->
      joinSides (addPartialBorrowVar x lt xBTy >> f t2)
        (addPartialBorrowVar y lt yBTy >> f t3)
    _ -> tyErr $ "Reference case used on type other than a reference to a sum type " <> pack (show t1) <> " " <> pack (show t1Ty)

letProdClause :: Mult -> Var -> Var -> Tm -> Tm -> (Tm -> Tc a) -> Tc a
letProdClause Single x y t1 t2 f = do
  t1Ty <- synth t1
  case t1Ty of
    ProdTy xTy yTy -> do
      addVar x xTy
      addVar y yTy
      f t2
    _ -> tyErr "Tried to deconstruct type other than a prod type"
letProdClause Many x y t1 t2 f = do
  t1Ty <- synth t1
  useRef t1Ty
  case t1Ty of
    RefTy lt (ProdTy xTy yTy) -> do
      addPartialBorrowVar x lt xTy
      addPartialBorrowVar y lt yTy
      f t2
    _ -> tyErr "Tried to deconstruct type other than a reference to a prod type"

letClause :: Var -> Tm -> Tm -> (Tm -> Tc a) -> Tc a
letClause x t1 t2 f = do
  xTy <- synth t1
  addVar x xTy
  f t2

varsBorrowedIn :: Ctx -> Tm -> [Var]
varsBorrowedIn ctx tm = L.nub $ f tm [] where
  f tm l = case tm of
    Unit -> l
    InL t -> f t l
    InR t -> f t l
    Case _ t1 _ t2 _ t3 -> f t3 $ f t2 $ f t1 l
    ProdTm t1 t2 -> f t2 $ f t1 l
    LetProd _ _ _ t1 t2 -> f t2 $ f t1 l
    LetUnit t1 t2 -> f t2 $ f t1 l
    Let _ t1 t2 -> f t2 $ f t1 l
    FunTm _ _ t1 -> f t1 l
    Poly _ _ t1 -> f t1 l
    TmVar _ -> l
    Copy _ -> l
    RefTm v@(Var _ i) -> if M.member i ctx.termCtx then v:l else l
    AppTy t1 _ -> f t1 l
    Drop _ t1 -> f t1 l
    AppTm t1 t2 -> f t2 $ f t1 l
    Fold _ t1 -> f t1 l
    Unfold t1 -> f t1 l
    UnfoldRef t1 -> f t1 l
    RecFun _ _ _ _ t1 -> f t1 l
    Anno t1 _ -> f t1 l

consumedVars :: Ctx -> Ctx -> [Var]
consumedVars c1 c2 = if M.isSubmapOfBy (const $ const True) m c1.varNames
  then fmap (uncurry $ flip Var) $ M.assocs $ M.difference c1.varNames m
  else error "Variable names map did not contain name for consumed variable"
  where m = M.difference c1.termCtx c2.termCtx

findMult :: Ctx -> Ctx -> Mult
findMult c1 c2 = if [] /= M.keys m then Single else Many where
  m = M.difference c1.termCtx c2.termCtx

verifyMult :: Mult -> Ctx -> Ctx -> Tc ()
verifyMult Many c1 c2 | consumed /= [] = tyErr msg
  where
    consumed = consumedVars c1 c2
    msg = "Consumed external variables in multi-use function: " <> pack (show consumed)
verifyMult _ _ _ = pure ()

-- | Checks to make sure borrows and drops are balanced in a function definition.
--
-- Any borrowing of a variable in startCtx needs to have same borrow count at the end.
checkStableBorrowCounts :: Ctx -> Ctx -> Tc ()
checkStableBorrowCounts startCtx endCtx = unless (stableBorrowCounts startCtx endCtx) err
  where
  err = tyErr "Too many drops or borrows of external variable in function body."
  stableBorrowCounts :: Ctx -> Ctx -> Bool
  stableBorrowCounts c1 c2 = [] == M.keys m where
    m = M.mergeWithKey f (const M.empty) (const M.empty) c1.termCtx c2.termCtx
    f _ (i1, _) (i2, _) | i1 /= i2 = Just ()
                        | otherwise = Nothing

synthFun :: Var -> Ty -> Tm -> Tc Ty
synthFun v vTy body = do
  startCtx <- get
  addVar v vTy
  bodyTy <- synth body
  endCtx <- get
  let vars = varsBorrowedIn startCtx body
      lts = LtJoin $ LtOf <$> vars
      mult = findMult startCtx endCtx
  checkStableBorrowCounts startCtx endCtx
  forM_ vars $ flip alterBorrowCount (+1)
  pure $ FunTy mult vTy lts bodyTy

synthPoly :: Var -> Kind -> Tm -> Tc Ty
synthPoly v kind body = do
  startCtx <- get
  bodyTy <- withKind v kind $ synth body
  endCtx <- get
  let vars = varsBorrowedIn startCtx body
      lts = LtJoin $ LtOf <$> vars
      mult = findMult startCtx endCtx
  checkStableBorrowCounts startCtx endCtx
  forM_ vars $ flip alterBorrowCount (+1)
  pure $ Univ mult lts v kind bodyTy

verifyBorrows :: Ctx -> Ty -> Tm -> Tc ()
verifyBorrows ctx lts body = do
  ltsSet <- toSet <$> lifetimeVars lts
  -- TODO: upgrade to list variables.
  unless (ltsSet == varSet) $ tyErr "Specified borrowed variables did not match actually borrowed variables."
  forM_ vars $ flip alterBorrowCount (+1)
  where
    toSet = S.fromList . fmap (.index)
    vars = varsBorrowedIn ctx body
    varSet = toSet vars

mkClosureCheck :: Tm -> Mult -> Ty -> Tc () -> Tc ()
mkClosureCheck body mult lts m = do
  startCtx <- get
  m
  endCtx <- get

  -- Check specified lifetimes
  verifyBorrows startCtx lts body

  -- Check multiplicity if Many is specified
  verifyMult mult startCtx endCtx

  checkStableBorrowCounts startCtx endCtx

checkFun :: Var -> Tm -> Mult -> Ty -> Ty -> Ty -> Tc ()
checkFun v body mult aTy lts bTy = mkClosureCheck body mult lts do
  addVar v aTy
  check bTy body

checkPoly :: Var -> Kind -> Tm -> Mult -> Ty -> Ty -> Tc ()
checkPoly v kind body mult lts bodyTy = mkClosureCheck body mult lts do
  withKind v kind $ check bodyTy body

synth :: Tm -> Tc Ty
synth tm = verifyCtxSubset $ case tm of
  Unit -> pure UnitTy
  InL _ -> tyErr "Cannot synthesize the type of a sum fragment"
  InR _ -> tyErr "Cannot synthesize the type of a sum fragment"
  Drop v t -> do
    dropVar v
    synth t
  LetUnit t1 t2 -> do
    check UnitTy t1
    synth t2
  ProdTm x y -> do
    xTy <- synth x
    yTy <- synth y
    pure $ ProdTy xTy yTy
  Anno t ty -> check ty t >> pure ty
  TmVar v -> useVar v
  Copy v -> do
    vTy <- lookupVar v
    case vTy of
      RefTy (LtOf v') _ -> borrowVar v'
      RefTy _ _ -> pure vTy
      _ -> varErr v "is not a reference."
  RefTm v -> borrowVar v
  Let x t1 t2 -> letClause x t1 t2 synth
  Case m t1 x t2 y t3 -> caseClause m t1 x t2 y t3 synth
  LetProd m x y t1 t2 -> letProdClause m x y t1 t2 synth
  -- To synthesize this will need a way to examine the body and find all referenced lifetimes.
  -- Maybe it's better to instead use check and restrict what can be seen? I can add a thing that
  -- let's me track if a lifetime was referenced to the monad?
  -- TODO: allow check to force a many function to be single use.
  FunTm v (Just vTy) body -> synthFun v vTy body
  FunTm _ Nothing _ -> tyErr "Cannot synthesize type of a function without an argument annotation."
  Poly v kind body -> synthPoly v kind body
  AppTy t1 tyArg -> do
    t1Ty <- synth t1
    case t1Ty of
      Univ _ lts v k body -> do
        decrementLts lts
        pure $ typeSub tyArg body
      RefTy l (Univ Many lts v k body) -> do
        useRef t1Ty
        pure $ typeSub tyArg body
      _ -> tyErr "Must be a universal polymorphism to have a type applied."
  AppTm t1 t2 -> do
    -- Roughly we synthesize t1 and use that to check t2.
    t1Ty <- synth t1
    case t1Ty of
      FunTy Single aTy lts bTy -> do
        check aTy t2
        decrementLts lts
        pure bTy
      -- TODO: original plan called for only being able to call multi-use functions
      -- through references, but is that really a useful distinction?
      FunTy Many aTy lts bTy -> do
        check aTy t2
        decrementLts lts
        pure bTy
      RefTy lt (FunTy Many aTy lts bTy) -> do
        check aTy t2
        useRef t1Ty
        pure bTy
      _ -> tyErr "Must be a function to apply to an argument."
  -- ltOfFVar is the name of the variable used for the lifetime of the variable f, which is
  -- a reference to this function itself.
  RecFun x ltOfFVar f (Just xTy) body -> undefined
  RecFun _ _ _ Nothing _ -> tyErr "Cannot synthesize type of a function without an argument annotation."
  Fold ty t1 -> undefined
  Unfold t1 -> undefined
  UnfoldRef t1 -> undefined

check :: Ty -> Tm -> Tc ()
check ty tm = verifyCtxSubset $ case (tm, ty) of
  (LetUnit x y, _) -> do
    check UnitTy x
    check ty y
  (InL x, SumTy xTy _) -> check xTy x
  (InR y, SumTy _ yTy) -> check yTy y
  (ProdTm x y, ProdTy xTy yTy) -> do
    check xTy x
    check yTy y
  (Let x t1 t2, _) -> letClause x t1 t2 $ check ty
  (Case m t1 x t2 y t3, _) -> caseClause m t1 x t2 y t3 $ check ty
  (LetProd m x y t1 t2, _) -> letProdClause m x y t1 t2 $ check ty
  (FunTm v mbVTy body, FunTy m aTy lts bTy) -> do
    case mbVTy of
      Just vTy -> unless (vTy == aTy) $ tyErr "local argument type annotation does not match checked type."
      Nothing -> pure ()
    checkFun v body m aTy lts bTy
  (Poly v1 k1 body, Univ m lts v2 k2 bodyTy) -> do
    -- TODO I don't know if this should check text name.
    unless (v1 == v2) $ tyErr "Mismatch in type variable"
    unless (k1 == k2) $ tyErr "Kind mismatch"
    checkPoly v1 k1 body m lts bodyTy
  _ -> do
    ty' <- synth tm
    if ty == ty'
      then pure ()
      else tyErr "no check rules matched, synthesize attempt produced different type"
