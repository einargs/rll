module Rll.Context
  ( Ctx(..), DataType(..), localEq, onTermVars, subsetOf, diffCtxTerms, emptyCtx
  ) where

import Data.HashMap.Strict qualified as M
import Data.Text (Text)
import Data.List (foldl')
import Data.Function (on)

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
  -- | List of module level terms.
  --
  -- We add functions and data type constructors to this.
  , moduleTerms :: M.HashMap Var Ty
  -- | Mapping variables to declared data types.
  , dataTypes :: M.HashMap Var DataType
  } deriving (Eq, Show)

emptyCtx :: Ctx
emptyCtx = Ctx M.empty M.empty [] M.empty M.empty

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


data DataType
  = EnumType [TypeParam] (M.HashMap Text [Ty]) Span
  | StructType Text [TypeParam] [Ty] Span
  deriving (Eq, Show)

instance Spans DataType where
  getSpan (EnumType _ _ s) = s
  getSpan (StructType _ _ _ s) = s
