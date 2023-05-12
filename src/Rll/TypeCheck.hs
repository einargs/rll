{-# LANGUAGE OverloadedStrings, OverloadedRecordDot #-}
module Rll.TypeCheck where

import Rll.Ast

import Control.Monad (unless, when, forM_)
import Data.Text (Text, pack)
import qualified Data.IntMap.Strict as M
import Control.Monad.State (MonadState(..), StateT, modify', runStateT)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Data.Maybe (fromMaybe)
import Control.Arrow (first, second)
import Data.Function (on)
import Data.Functor (($>))
import qualified Data.List as L
import qualified Debug.Trace as T


data Ctx = Ctx { termCtx :: M.IntMap (Int, Ty), tyCtx :: M.IntMap Kind }
  deriving (Eq, Show)

onTermCtx :: (M.IntMap (Int, Ty) -> M.IntMap (Int, Ty)) -> Ctx -> Ctx
onTermCtx f (Ctx vm tm) = Ctx (f vm) tm

-- Shadowing references doesn't matter; we can drop an external one, or return a value
-- that borrows a variable.
-- TODO: I think I need to compare the borrow counts and make sure a2 has lower or equal borrow counts.
-- Is the first ctx a subset of the second ctx.
subsetOf :: Ctx -> Ctx -> Bool
subsetOf (Ctx a1 b1) (Ctx a2 b2) = M.isSubmapOfBy f a1 a2 && b1 == b2 -- M.isSubmapOf (M.map snd a1) (M.map snd a2) && b1 == b2
  where
    f :: (Int, Ty) -> (Int, Ty) -> Bool
    f (i1, t1) (i2, t2) = t1 == t2

data TyErr = TyErr Text deriving (Eq, Show)

newtype Tc a = MkTc { unTc :: StateT Ctx (Except TyErr) a }
  deriving (Functor, Applicative, Monad, MonadError TyErr, MonadState Ctx)

traceCtx :: String -> Tc ()
traceCtx name = do
  Ctx tm _ <- get
  T.traceM $ name <> ": " <> show tm

emptyCtx :: Ctx
emptyCtx = Ctx M.empty M.empty

runTc :: Ctx -> Tc a -> Either TyErr a
runTc ctx = fmap fst . runExcept . flip runStateT ctx . unTc

tyErr :: Text -> Tc a
tyErr = throwError . TyErr

varErr :: Var -> Text -> Tc a
varErr (Var n i) txt = tyErr $ "Var " <> n <> "@" <> pack (show i) <> ": " <> txt

lookupEntry :: Var -> Tc (Int, Ty)
lookupEntry v@(Var _ i) = do
  (Ctx m _) <- get
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
addVar v@(Var _ i) ty = do
  (Ctx m tm) <- get
  case M.lookup i m of
    Just _ -> varErr v "already exists"
    Nothing -> put $ Ctx (M.insert i (0, ty) m) tm

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
    (Ctx tm _) <- get
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
    Poly _ _ _ t1 -> f t1 l
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

synthFun :: Var -> Ty -> Tm -> Tc Ty
synthFun v vTy body = do
  startCtx <- get
  addVar v vTy
  bodyTy <- synth body
  endCtx <- get
  let vars = varsBorrowedIn startCtx body
      lts = LtJoin $ LtOf <$> vars
      mult = findMultiplicity startCtx endCtx
      stable = stableBorrowCounts startCtx endCtx
  unless stable $ tyErr "Too many drops or borrows of external variable in function body."
  forM_ vars $ flip alterBorrowCount (+1)
  pure $ FunTy mult vTy lts bodyTy
  where
    -- TODO: I do need a check to make sure no borrow counts decrease below initial value.
    -- TODO: this doesn't work. Detecting changes afterwards means I could go in,
    -- borrow a variable, and then drop it, and keep the same borrow count.
    findMultiplicity :: Ctx -> Ctx -> Mult
    findMultiplicity c1 c2 = if [] /= M.keys m then Single else Many where
      m = M.difference c1.termCtx c2.termCtx
    -- Any borrowing of a variable in startCtx needs to have same borrow count at the end.
    stableBorrowCounts :: Ctx -> Ctx -> Bool
    stableBorrowCounts c1 c2 = [] == M.keys m where
      m = M.mergeWithKey f (const M.empty) (const M.empty) c1.termCtx c2.termCtx
      f _ (i1, _) (i2, _) | i1 /= i2 = Just ()
                          | otherwise = Nothing

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
  Poly m v kind body -> undefined
  AppTy t1 ty -> undefined
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
      _ -> do
        T.traceM $ show t1Ty
        tyErr "Must be a function to apply to an argument."
  -- ltOfFVar is the name of the variable used for the lifetime of the variable f, which is
  -- a reference to this function itself.
  RecFun x ltOfFVar f (Just xTy) body -> undefined
  RecFun _ _ _ Nothing _ -> tyErr "Cannot synthesize type of a function without an argument annotation."
  Fold ty t1 -> undefined
  Unfold t1 -> undefined
  UnfoldRef t1 -> undefined

-- TODO: to finish this I'd need a bidirectional type system.
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
  _ -> do
    ty' <- synth tm
    if ty == ty'
      then pure ()
      else tyErr "no check rules matched, synthesize attempt produced different type"
