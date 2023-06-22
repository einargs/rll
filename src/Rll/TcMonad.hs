-- | The basic `Tc` monad and some simple helper
-- functions for looking up entries in the context.
--
-- Also re-exports relevant utility functions.
module Rll.TcMonad
  ( Tc(..), runTc, evalTc
  , lookupEntry, lookupKind, lookupDataCon
  , lookupDataType, lookupVar
  , expectedTermVar
  , MonadError(..)
  , MonadState(..), modify', gets
  ) where

import Rll.Context
import Rll.TypeError
import Rll.Ast

import qualified Data.HashMap.Strict as M
import Control.Monad.State (MonadState(..), StateT, runStateT, modify', gets)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Safe (atMay)

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
    Just (_,Just removedSpan) -> RemovedTermVar v s removedSpan
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
