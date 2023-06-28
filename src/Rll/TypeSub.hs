-- | Tools for substituting types.
module Rll.TypeSub
  ( rawTypeSub, typeSub, typeAppSub
  , typeShift
  , applyTypeParams
  ) where

import Rll.Ast

rawTypeShift :: Int -> Int -> Ty -> Ty
rawTypeShift i c ty@Ty{span=s, tyf} = Ty s $ case tyf of
  TyVar (MkTyVar t n) -> TyVar (MkTyVar t $ if n < c then n else n+i)
  Univ m lts v k body -> Univ m (f lts) v k (rawTypeShift i (c+1) body)
  _ -> f <$> tyf
  where f = rawTypeShift i c

typeShift :: Int -> Ty -> Ty
typeShift i = rawTypeShift i 0

rawTypeSub :: Int -> Ty -> Ty -> Ty
rawTypeSub xi arg target@Ty{span=s, tyf} = case tyf of
  TyVar v@(MkTyVar _ vi) -> if vi == xi then arg else Ty s $ TyVar v
  Univ m lts v k body -> Ty s $ Univ m (f lts) v k $
    rawTypeSub (xi+1) (typeShift 1 arg) body
  _ -> Ty s $ f <$> tyf
  where f = rawTypeSub xi arg

-- | Do type substitution on a type.
--
-- Argument, body
typeSub :: Ty -> Ty -> Ty
typeSub = rawTypeSub 0

-- | Do type application on the body of a `Univ` type, which
-- requires that we then upshift to account for the lost variable.
--
-- Argument, body
typeAppSub :: Ty -> Ty -> Ty
typeAppSub arg body = typeShift (-1) $
  typeSub (typeShift 1 arg) body

-- | Substitute for the type parameter variables inside the fields of a
-- data type.
--
-- Type arguments, data type fields.
applyTypeParams :: [Ty] -> [Ty] -> [Ty]
applyTypeParams args members = go (length args - 1) args members where
  go i [] members = members
  go i (a:as) members = go (i-1) as $
    rawTypeSub i a <$> members
