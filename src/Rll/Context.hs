module Rll.Context
  ( Ctx(..), DataType(..), localEq, onTermVars, subsetOf, diffCtxTerms, emptyCtx
  , BuiltInType(..), getDataTypeName, getDataConArgNum
  , BuiltInFun(..), getBuiltInFunName, getBuiltInFunTy, builtInFunNameMap
  ) where

import Rll.Ast

import Data.HashMap.Strict qualified as M
import GHC.Generics (Generic)
import Data.Text (Text, unpack)
import Data.List (foldl')
import Data.Hashable (Hashable(..))

import Data.Aeson (FromJSON, ToJSON)

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
emptyCtx = Ctx M.empty M.empty [] builtInFuns' M.empty dataTypes where
  dataTypes = M.fromList $ f <$> [minBound..maxBound]
  f ty = (Var $ getBuiltInName ty, BuiltInType ty)
  -- We start our map of module level functions with the list of built-in functions.
  builtInFuns' = getBuiltInFunTy <$> builtInFunNameMap

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
  BuiltInI64 -> i64TyName.name
  BuiltInString -> stringTyName.name

data DataType
  = EnumType Text [TypeParam] (M.HashMap Text [Ty]) Span
  | StructType Text [TypeParam] [Ty] Span
  | BuiltInType BuiltInType
  deriving (Eq)

instance Show DataType where
  show = unpack . getDataTypeName

-- | Get the name of a data type.
getDataTypeName :: DataType -> Text
getDataTypeName dt = case dt of
  EnumType n _ _ _ -> n
  StructType n _ _ _ -> n
  BuiltInType enum -> getBuiltInName enum

-- | Get the number of arguments a data constructor accepts.
getDataConArgNum :: DataType -> Var -> Int
getDataConArgNum dt con = case dt of
  EnumType name tyParams m _ -> case M.lookup con.name m of
    Just args -> length args
    Nothing -> error "Constructor mismatch; should be caught by type checking"
  StructType name tyParams members _ -> length members
  BuiltInType b -> case b of
    BuiltInI64 -> error "has no constructor"
    BuiltInString -> error "has no constructor"

-- | Enum listing all of our built-in functions.
data BuiltInFun
  = AddI64
  deriving (Eq, Show, Enum, Bounded, Generic, Hashable, FromJSON, ToJSON)

getBuiltInFunName :: BuiltInFun -> Text
getBuiltInFunName fun = case fun of
  AddI64 -> "addI64"

builtInFunNameMap :: M.HashMap Var BuiltInFun
builtInFunNameMap = M.fromList $ g <$> [minBound..maxBound]
  where
  g fun = (Var $ getBuiltInFunName fun, fun)

getBuiltInFunTy :: BuiltInFun -> Ty
getBuiltInFunTy fun = case fun of
  AddI64 -> mkBuiltinFun [i64, i64] i64
  where
  i64 = TyCon i64TyName
  lift = Ty $ Span "builtin" 0 0 0 0
  -- This assumes that the function is always re-usable
  mkBuiltinFun :: [TyF Ty] -> TyF Ty -> Ty
  mkBuiltinFun args retTy = foldr f (lift retTy) args where
    f arg ret = lift $ FunTy Many (lift arg) (lift $ LtJoin []) ret
