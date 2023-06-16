module Rll.AstUtil
  ( es
  , tyCon, ltOf, refTy, refVar, tyVar, staticLt
  , ltJoin, funTy, tyVar0, univ
  , tmVar, tmCon, letStruct, appTm, appTy, tmLet
  , fixFunTm, funTm, ref, tmCase, br, copy
  , argI, argT, argK, intL, strL, dropv, anno
  ) where

import Rll.Ast

import Data.Text (Text)

es :: Span
es = Span "test.rll" 1 1 1 1

sv :: Text -> SVar
sv t = (SVar (Var t) es)

et :: TyF Ty -> Ty
et = Ty es

em :: TmF Tm -> Tm
em = Tm es

tyCon v = et $ TyCon (Var v)
ltOf v = et $ LtOf $ Var v
refTy a b = et $ RefTy a b
refVar v ty = refTy (ltOf v) ty
tyVar0 v = et $ TyVar (MkTyVar v 0)
tyVar v i = et $ TyVar (MkTyVar v i)
staticLt = et $ LtJoin []
ltJoin tys = et $ LtJoin tys
funTy s a lts b = et $ FunTy s a lts b
univ s lts t k body = et $ Univ s lts (TyVarBinding t) k body

tmVar v = em $ TmVar (Var v)
tmCon v = em $ TmCon (Var v)
letStruct vars t1 t2 = em $ LetStruct con mem t1 t2
  where (con:mem) = sv <$> vars
appTm t1 t2 = em $ AppTm t1 t2
tmLet v t1 t2 = em $ Let (sv v) t1 t2
appTy t1 ty = em $ AppTy t1 ty
copy v = em $ Copy (Var v)
ref v = em $ RefTm (Var v)
dropv v t1 = em $ Drop (sv v) t1
anno t1 ty = em $ Anno t1 ty
intL i = em $ LiteralTm $ IntLit i
strL s = em $ LiteralTm $ StringLit s
tmCase t1 branches = em $ Case t1 branches

-- | Build a case branch.
br :: [Text] -> Tm -> CaseBranch Tm
br vars t1 = CaseBranch con mem t1
  where (con:mem) = sv <$> vars

-- | For building inferred arguments for a function term.
argI :: Text -> (SVar, Maybe Ty)
argI t = (sv t, Nothing)

argT :: Text -> Ty -> (SVar, Maybe Ty)
argT t ty = (sv t, Just ty)

argK :: Text -> Kind -> (TyVarBinding, Kind)
argK t k = (TyVarBinding t, k)

fixFunTm v polyB argB body = em $ FunTm (Just $ sv v) polyB argB body
funTm polyB argB body = em $ FunTm Nothing polyB argB body
