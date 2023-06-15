module Rll.Context
  ( Ctx(..), DataType(..), localEq, onTermVars, subsetOf, diffCtxTerms, emptyCtx
  , BuiltInType(..), getDataTypeName
  ) where

import Data.HashMap.Strict qualified as M
import Data.Text (Text)
import Data.List (foldl')

import Rll.Ast

-- | Only localTypeVars is actual de-brujin indices that get shifted.
data Ctx = Ctx
  -- | For term vars, when processing a function definition, we just start
  -- by transforming the moduleTerms map into an initial value.
  { termVars :: M.HashMap Var (Int, Ty)
  -- | Keeps track of where variables were defined. When they're dropped, we
  -- record that too. Used for better error messages.
  , varLocs :: M.HashMap Var (Span, (Maybe Span))
  -- | De-brujin indices keep track of the type variables for easy type
  -- equality.
  , localTypeVars :: [Kind]
  -- | Map of module level functions.
  , moduleFuns :: M.HashMap Var Ty
  -- | List of module level data constructors.
  , moduleDataCons :: M.HashMap Var (DataType, Ty)
  -- | Mapping variables to declared data types.
  , dataTypes :: M.HashMap Var DataType
  } deriving (Eq, Show)

emptyCtx :: Ctx
emptyCtx = Ctx M.empty M.empty [] M.empty M.empty dataTypes where
  dataTypes = M.fromList $ f <$> [minBound..maxBound]
  f ty = (Var $ getBuiltInName ty, BuiltInType ty)

-- | Check for equality only on the local term variables and types.
localEq :: Ctx -> Ctx -> Bool
localEq c1 c2 = c1.termVars == c2.termVars && c1.localTypeVars == c2.localTypeVars

onTermVars :: (M.HashMap Var (Int, Ty) -> M.HashMap Var (Int, Ty)) -> Ctx -> Ctx
onTermVars f c = c{termVars=f c.termVars}

-- Shadowing references doesn't matter; we can drop an external one, or return a value
-- that borrows a variable.
-- | This is only a local operation.
subsetOf :: Ctx -> Ctx -> Bool
subsetOf c1 c2 = M.isSubmapOfBy f c1.termVars c2.termVars
  && c1.localTypeVars == c2.localTypeVars
  where
    f :: (Int, Ty) -> (Int, Ty) -> Bool
    f (i1, t1) (i2, t2) = t1 == t2

-- | Finds the common intersection of all contexts' term
-- variables and returns the diff for each with regard to it.
--
-- Only performs a diff on the term variables.
diffCtxTerms :: [Ctx] -> [[(Var,Int,Ty)]]
diffCtxTerms [] = []
diffCtxTerms [c] = [f c.termVars] where
  f = fmap (\(a,(b,c)) -> (a,b,c)) . M.toList
diffCtxTerms full = f <$> diffs where
  c:cs = (.termVars) <$> full
  common = foldl' M.intersection c cs
  diffs = flip M.difference common <$> (c:cs)
  f :: M.HashMap Var (Int, Ty) -> [(Var,Int,Ty)]
  f = fmap (\(a,(b,c)) -> (a,b,c)) . M.toList

-- | Enum for our builtin types. Eventually we'll probably have some
-- tool that hooks into C or something.
--
-- This is entirely a tag based enum. Any type arguments are provided
-- via `TyApp`.
data BuiltInType
  = BuiltInI64
  | BuiltInString
  deriving (Eq, Show, Enum, Bounded)

getBuiltInName :: BuiltInType -> Text
getBuiltInName enum = case enum of
  BuiltInI64 -> "I64"
  BuiltInString -> "String"

data DataType
  = EnumType Text [TypeParam] (M.HashMap Text [Ty]) Span
  | StructType Text [TypeParam] [Ty] Span
  | BuiltInType BuiltInType
  deriving (Eq, Show)

getDataTypeName :: DataType -> Text
getDataTypeName dt = case dt of
  EnumType n _ _ _ -> n
  StructType n _ _ _ -> n
  BuiltInType enum -> getBuiltInName enum
