-- | Tools for substituting types.
module Rll.TypeSub
  ( rawTypeSub, typeAppSub
  , typeShift
  , applyTypeParams
  , tyIsConcrete
  , typeAppSubs
  ) where

import Rll.Ast
import Data.List (foldl')

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
  TyVar v@(MkTyVar _ vi) -> if vi == xi then arg else target
  Univ m lts v k body -> Ty s $ Univ m (f lts) v k $
    rawTypeSub (xi+1) (typeShift 1 arg) body
  _ -> Ty s $ f <$> tyf
  where f = rawTypeSub xi arg

-- | If the type has any type variables in it returns false.
tyIsConcrete :: Ty -> Bool
tyIsConcrete Ty{tyf} = case tyf of
  TyVar _ -> False
  _ -> all tyIsConcrete tyf

-- | Do type application on the body of a `Univ` type, which
-- requires that we then upshift to account for the lost variable.
--
-- Argument, body
typeAppSub :: Ty -> Ty -> Ty
typeAppSub arg body = typeShift (-1) $
  rawTypeSub 0 (typeShift 1 arg) body

-- | Apply multiple substitutions at once. Requires that there be `n`
-- free variables in the type where `n` is the number of arguments.
--
-- Essentially this assumes that we have descended beneath/discarded
-- binders on the body but have not correspondingly shifted the arguments.
typeAppSubs :: [Ty] -> Ty -> Ty
typeAppSubs args body = typeShift (-n) body' where
  n = length args
  -- We shift the arguments up by `n` so that there can be no conflicts
  -- with variables in the body.
  shiftedArgs = typeShift n <$> args
  -- NOTE: any bound type variables in body should be skipped over when
  -- unshifting, so the unshift only affects the arguments.
  g ty (i, arg) = rawTypeSub i arg ty
  -- We reverse because the zeroth argument is the furthest right for functions (and datatypes):
  -- forall c:Type. forall d:Type. c@1 -M[]> d@0
  body' = foldl' g body $ zip [0..] $ reverse shiftedArgs

-- |
subsAllIn :: [Ty] -> [a] -> (a -> Ty) -> (a -> Ty -> a) -> [a]
subsAllIn = undefined -- TODO: this just takes a lens
-- needs to substitute for all type variables in the body.

-- | Substitute for the type parameter variables inside the fields of a
-- data type.
--
-- Type arguments, data type fields.
applyTypeParams :: [Ty] -> [Ty] -> [Ty]
applyTypeParams args members = typeAppSubs args <$> members
{-
applyTypeParams args members = typeShift (-argLen) <$> go (argLen - 1) shiftedArgs members where
  argLen = length args
  -- We shift the arguments up by the number of type variables that can be present inside
  -- the members so that there are no conflicts.
  shiftedArgs = typeShift argLen <$> args
  go i [] members = members
  go i (a:as) members = go (i-1) as $
    rawTypeSub i a <$> members
-}
