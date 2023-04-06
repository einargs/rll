module Rll.TypeCheck where

import Rll.Ast

import Control.Monad (unless, when)
import Data.Text (Text)
import qualified Data.IntMap.Strict as M
import Control.Monad.State (MonadState(..), StateT)
import Control.Monad.Except (MonadError(..), Except)
import Data.Maybe (fromMaybe)

data Ctx = Ctx { termCtx :: M.IntMap (Int, Ty), tyCtx :: M.IntMap Kind }
  deriving Eq

-- Does the number of shadowing references affect whether a subset is okay?
subsetOf :: Ctx -> Ctx -> Bool
subsetOf (MkCtx m1) (MkCtx m2) = M.isSubmapOf m1 m2

data TyErr = TyErr Text

newtype Tc a = MkTc { unTc :: StateT Ctx (Except TyErr) a }
  deriving (Functor, Applicative, Monad, MonadError TyErr, MonadState Ctx)

tyErr :: Text -> Tc a
tyErr = throwError . TyErr

lookupTyVar :: Var -> Tc Kind
lookupTyVar (Var txt i) = fromMaybe
  (tyErr $ "Cannot find type variable " <> txt)
  $ get >>= M.lookup i . tyCtx

-- | Get a list of variables this type shadows.
tyShadows :: Ty -> [Var]
tyShadows UnitTy = []
tyShadows (SumTy x y) = tyShadows x <> tyShadows y
tyShadows (ProdTy x y) = tyShadows x <> tyShadows y
tyShadows Static = []
tyShadows (TyVar x) = lookupTyVar >>= \case
  Ty -> []
  Lifetime -> [x]
tyShadows (LtOf x) = [x]
tyShadows (FunTy m x y z) = undefined
tyShadows (LtJoin xs) = xs >>= tyShadows
tyShadows (RefTy x y) = undefined
tyShadows (Univ m xTy v k yTy) = undefined
tyShadows (RecTy v xTy) = undefined

joinSides :: Tc Ty -> Tc Ty -> Tc Ty
joinSides s1 s2 = do
  ctx <- get
  ty1 <- s1
  ctx1 <- get
  set ctx
  ty2 <- s2
  ctx2 <- get
  -- TODO compare them

lookupVar :: Var -> Tc Ty
lookupVar (Var _ i) = M.lookup i m

addVar :: Var -> Ty -> Tc Ctx
addVar (Var _ i) ty = modify $ MkCtx . M.insert i ty . unCtx

dropVar :: Var -> Ctx -> Ctx
dropVar (Var _ i) (MkCtx m) = MkCtx $ M.delete i m

withVar :: Var -> Ty -> Ctx -> (Ctx -> a) -> a
withVar v ty ctx f = f $ addVar v ty ctx

synth :: Tm -> Ctx -> Tc (Ctx, Ty)
synth tm ctx = do
  ctx' <- case tm of
    Unit -> pure (ctx, UnitTy)
    Case Single t1 x t2 y t3 -> do
      (ctx', t1Ty) <- synth t1 ctx
      case t1Ty of
        SumTy xTy yTy -> do
          (ctx1, lTy) <- withVar x xTy ctx' $ synth t2
          (ctx2, rTy) <- withVar y yTy ctx' $ synth t3
          when (ctx1 /= ctx2) $ tyErr "branches of case statement produced different contexts"
          when (lTy /= rTy) $ tyErr "branches of statement synthesized different types"
          pure (ctx1, lTy)
        _ -> tyErr "Owning case used on non-sum type"
    Case Many t1 x t2 y t3 -> do
      (ctx', t1Ty) <- synth t1 ctx
      case t1Ty of
        RefTy lt (SumTy xBTy yBTy) -> do
          (ctx1, lTy) <- withVar x (RefTy lt xBTy) ctx' $ synth t2
          (ctx2, rTy) <- withVar y (RefTy lt yBTy) ctx' $ synth t2
          when (ctx1 /= ctx2) $ tyErr "branches of case statement produced different contexts"
          when (lTy /= rTy) $ tyErr "branches of statement synthesized different types"
          pure (ctx1, lTy)
        _ -> tyErr "Reference case used on type other than a reference to a sum type"
    ProdTm x y -> do
      (ctx', xTy) <- synth x ctx
      (ctxOut, yTy) <- synth y ctx'
      pure (ctxOut, ProdTy xTy yTy)
  unless (ctx' `subsetOf` ctx) $ tyErr "Output ctx should be a subset of input context."
  pure ctx'

-- TODO: to finish this I'd need a bidirectional type system.
check :: Tm -> Ty -> Ctx -> Tc Ctx
check tm ty ctx = do
  ctx' <- case (tm, ty) of
    (LetUnit x y, _) -> check x UnitTy ctx >>= check y ty
    (InL x, SumTy xTy _) -> check x xTy ctx
    (InR x, SumTy _ xTy) -> check x xTy ctx
    (Case Single t1 x t2 y t3, _) -> do
      (ctx', t1Ty) <- synth t1 ctx
      case t1Ty of
        SumTy xTy yTy -> do
          ctx1 <- withVar x xTy ctx' $ check t2 ty
          ctx2 <- withVar y yTy ctx' $ check t3 ty
          when (ctx1 /= ctx2) $ tyErr "branches of case statement produced different contexts"
          pure ctx1
        _ -> tyErr "Owning case used on non-sum type"
    (Case Many t1 x t2 y t3, _) -> do
      (ctx', t1Ty) <- synth t1 ctx
      case t1Ty of
        RefTy lt (SumTy xBTy yBTy) -> do
          ctx1 <- withVar x (RefTy lt xBTy) ctx' $ check t2 ty
          ctx2 <- withVar y (RefTy lt yBTy) ctx' $ check t2 ty
          when (ctx1 /= ctx2) $ tyErr "branches of case statement produced different contexts"
          pure ctx1
        _ -> tyErr "Reference case used on type other than a reference to a sum type"
    (ProdTm x y, ProdTy xTy yTy) -> check x xTy ctx >>= check y yTy
    _ -> do
      (ctx', ty') <- synth tm ctx
      if ty == ty'
        then pure ctx'
        else tyErr "no check rules matched, synthesize attempt produced different type"
  unless (ctx' `subsetOf` ctx) $ tyErr "Output ctx should be a subset of input context."
  pure ctx'
