module Rll.LtSet
  ( LtSet
  , ltSetToSVars, ltSetToVars, ltSetToTypes
  , ltsInTy, ltsForClosure, isTyBorrowing
  , lifetimeSet, lifetimeSVars, lifetimeVars
  ) where

import Rll.Ast
import Rll.Context
import Rll.TcMonad
import Rll.TypeError

import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.Maybe (mapMaybe)
import Safe (atMay)

-- | A lifetime type reduced down to its essence.
newtype LtSet = LtSet {rawSet :: S.HashSet (Span, Either TyVar Var)}
  deriving (Eq)

instance Show LtSet where
  showsPrec i (LtSet s) = showsPrec i $ S.toList s

-- | Convenience function for getting a list of variables and their locations
-- in the type from a lifetime set.
ltSetToSVars :: LtSet -> [(Var, Span)]
ltSetToSVars = mapMaybe f . S.toList . (.rawSet) where
  f (s, Right v) = Just (v, s)
  f _ = Nothing

-- | Convenience function for getting a list of variables from a lifetime set
ltSetToVars :: LtSet -> [Var]
ltSetToVars = fmap fst . ltSetToSVars

-- | Convert a lifetime set to a list of the lifetimes.
ltSetToTypes :: LtSet -> [Ty]
ltSetToTypes (LtSet ltSet) = fmap f $ S.toList ltSet where
  f (s, Left x) = Ty s $ TyVar x
  f (s, Right v) = Ty s $ LtOf v

-- | Get a set of all lifetimes referenced in a type relative to the context.
--
-- Specifically, this means that we do not add lifetimes in the input or output
-- of functions or in the body of a reference type.
--
-- It's important that the context type variable indices line up with those
-- in the type.
ltsInTy :: Ctx -> Ty -> LtSet
ltsInTy ctx typ = LtSet $ S.fromList $ f typ [] where
  f Ty{span=s, tyf} l = case tyf of
    LtOf v -> (s, Right v):l
    TyVar tv -> case getKind tv of
      LtKind -> (s, Left tv):l
      TyKind -> l
      TyOpKind _ _ -> l
    FunTy _ _ lts _ -> f lts l
    Univ _ lts _ _ _ -> f lts l
    RefTy lt _ -> f lt l
    _ -> foldr f l tyf
  getKind tv@(MkTyVar n i) = case atMay ctx.localTypeVars i of
    Just k -> k
    Nothing -> error $ "type variable " <> show tv
      <> " has no kind in context " <> show ctx.localTypeVars
      <> "\nFound in type " <> show typ <> " span " <> show typ.span

-- | Get all lifetimes implied by borrows and copies inside a closure.
--
-- Context is the closure entrance context. Used to make sure
-- we only return lifetimes external to the closure.
ltsBorrowedIn :: Ctx -> Tm -> LtSet
ltsBorrowedIn ctx tm = LtSet $ S.fromList $ g 0 tm [] where
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
ltsInConsumed c1 c2 = LtSet $ S.unions ltSets where
  diff = M.difference c1.termVars c2.termVars
  ltSets = (.rawSet) . ltsInTy c1 . snd <$> M.elems diff

-- | Infer the lifetimes for a closure type.
ltsForClosure :: Ctx -> Ctx -> Tm -> LtSet
ltsForClosure c1 c2 tm = LtSet $ S.union (ltsInConsumed c1 c2).rawSet (ltsBorrowedIn c1 tm).rawSet

-- | Does the type use the lifetime of this variable?
isTyBorrowing :: Var -> Ty -> Bool
isTyBorrowing v1 Ty{tyf} = case tyf of
  LtOf v -> v == v1
  _ -> or $ isTyBorrowing v1 <$> tyf

-- | Get a set of all unique variables and lifetime variables mentioned in
-- the lifetime. This is the most granular set of lifetimes.
lifetimeSet :: Ty -> Tc LtSet
lifetimeSet ty = LtSet <$> go ty where
  go Ty{span, tyf} = case tyf of
    LtOf v -> pure $ S.singleton $ (span, Right v)
    LtJoin ls -> S.unions <$> traverse go ls
    TyVar x -> do
      k <- lookupKind x span
      case k of
        LtKind -> pure $ S.singleton $ (span, Left x)
        _ -> throwError $ ExpectedKind LtKind k span
    _ -> throwError $ ExpectedKind LtKind TyKind span

-- | Get a list of explicitly mentioned variables in the lifetime.
-- Ignores lifetime variables.
lifetimeVars :: Ty -> Tc [Var]
lifetimeVars = fmap ltSetToVars . lifetimeSet

-- | Get a list of explicitly mentioned variables and their spans
-- in the lifetime.
--
-- Ignores lifetime variables.
lifetimeSVars :: Ty -> Tc [(Var, Span)]
lifetimeSVars = fmap ltSetToSVars . lifetimeSet
