{-# LANGUAGE DeriveTraversable #-}
module Rll.Core
  ( CoreF(..), Core(..)
  , extendPoly, extendLam, extendAppTy, extendFix
  , extendAppTm
  ) where

import Rll.Ast

import Data.Text (Text)

-- | This IR is produced during type checking and annotates every
-- term with its type.
data CoreF a
  = CaseCF a [(SVar, [SVar], a)]
  | LetStructCF SVar [SVar] a a
  | LetCF SVar a a
  | LamCF (Maybe SVar) [(TyVarBinding, Kind)] [(SVar, Ty)] a
  | ModuleVarCF Var
  | LocalVarCF Var
  | ConCF Var
  | CopyCF Var
  | RefCF Var
  | DropCF SVar a
  | AppTmCF a [a]
  | AppTyCF a [Ty]
  | LiteralCF Literal
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | This annotates everything in `CoreF` with its type and span.
data Core = Core {ty::Ty, span::Span, core::(CoreF Core)}
  deriving (Eq)

-- | Either extends an existing `PolyCF` or introduces a new one.
extendPoly :: TyVarBinding -> Kind -> Core -> CoreF Core
extendPoly b k fullCore@Core{core} = case core of
  LamCF Nothing polyB argB body -> LamCF Nothing ((b,k):polyB) argB body
  _ -> LamCF Nothing [(b,k)] [] fullCore

-- | Either extends an existing `LamCF` or introduces a new one.
extendLam :: SVar -> Ty -> Core -> CoreF Core
extendLam v vTy fullCore@Core{core} = case core of
  LamCF Nothing polyB argB body -> LamCF Nothing polyB ((v,vTy):argB) body
  _ -> LamCF Nothing [] [(v,vTy)] fullCore

extendAppTy :: Core -> Ty -> CoreF Core
extendAppTy fullCore@Core{core} ty = case core of
  AppTyCF body tys -> AppTyCF body (tys <> [ty])
  _ -> AppTyCF fullCore [ty]

extendFix :: SVar -> Core -> CoreF Core
extendFix funVar fullCore@Core{core} = case core of
  LamCF (Just _) _ _ _ -> error "Type checking should catch this"
  LamCF Nothing polyB argB body -> LamCF (Just funVar) polyB argB body
  _ -> error "Type checking should prevent this"

extendAppTm :: Core -> Core -> CoreF Core
extendAppTm t1@Core{core} t2 = case core of
  AppTmCF f args -> AppTmCF f $ args <> [t2]
  _ -> AppTmCF t1 [t2]

instance Show Core where
  show (Core _ _ cf) = show cf

instance Spans Core where
  getSpan = (.span)
