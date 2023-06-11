{-# LANGUAGE BlockArguments, OverloadedStrings, QuasiQuotes #-}
module Rll.TcSpecUtil
  ( txt, stdFile, synthTo, checkTo, rawTest, baseTest
  , baseFailTest, baseCtx
  -- Utility constructors
  , es, tyCon, refTy, tyVar, staticLt
  ) where

import Test.Hspec
import qualified Data.Text as T
import qualified Text.Megaparsec as M
import Control.Monad (void)

import QuoteTxt
import qualified Rll.Parser as RP
import Rll.TypeCheck
import Rll.Ast
import Rll.TypeError (prettyPrintError, TyErr(..))
import Rll.Context
import Rll.Tc

es :: Span
es = Span "test.rll" 1 1 1 1

tyCon v = TyCon (Var v) es
refTy v ty = RefTy (LtOf (Var v) es) ty es
tyVar v i = TyVar (MkTyVar v i) es
staticLt = LtJoin [] es

processFile :: String -> T.Text -> Either (M.ParseErrorBundle T.Text RP.RllParseError) (Tc ())
processFile filename text = (void . typeCheckFile) <$> M.parse RP.fileDecls filename text

stdFile :: T.Text
stdFile = [txt|
struct Unit {}
struct Int {}
struct Str {}
struct Pair { Int Str }
enum Sum = Left Int | Right Str;
enum Bool = True | False;

struct Tuple (a:Type) (b:Type) { a b }

enum Either (a:Type) (b:Type) = InL a | InR b;

consInt : Int -M[]> Unit
= \x -> let Int = x in Unit;

consStr : Str -M[]> Unit
= \x -> let Str = x in Unit;

consPair : Pair -M[]> Unit
= \p -> let Pair i s = p in
let Int = i in let Str = s in Unit;

consSum : Sum -M[]> Unit
= \s -> case s of
| Left i -> let Int = i in Unit
| Right s -> let Str = s in Unit;
|]

baseCtx :: Ctx
baseCtx = case runTc emptyCtx fileTc of
  Left err -> error $ T.unpack $ prettyPrintError stdFile err
  Right (_,ctx) -> ctx
  where fileTc = case processFile "ctx.rll" stdFile of
          Left err -> error $ M.errorBundlePretty err
          Right v -> v

buildChecker :: HasCallStack => (Tm -> Ty -> Expectation) -> T.Text -> T.Text -> Expectation
buildChecker cmp tmTxt tyTxt = do
  termMay <- runP "term.rll" RP.tm tmTxt
  typMay <- runP "type.rll" RP.ty tyTxt
  case (termMay, typMay) of
    (Just tm, Just ty) -> cmp tm ty
    _ -> pure ()
  where
    runP :: String -> RP.Parser a -> T.Text -> IO (Maybe a)
    runP filename p txt = case M.parse (p <* M.eof) filename txt of
      Right v -> pure $ Just v
      Left err -> do
        expectationFailure $ M.errorBundlePretty err
        pure Nothing

synthTo :: HasCallStack => T.Text -> T.Text -> Expectation
synthTo tmTxt tyTxt = buildChecker f tmTxt tyTxt where
  f tm ty = case evalTc baseCtx (synth tm) of
    Left err -> expectationFailure $ T.unpack $ prettyPrintError tmTxt err
    Right ty' -> ty `shouldBe` ty

checkTo :: HasCallStack => T.Text -> T.Text -> Expectation
checkTo tmTxt tyTxt = buildChecker f tmTxt tyTxt where
  f tm ty = case evalTc baseCtx (check ty tm) of
    Left err -> expectationFailure $ T.unpack $ prettyPrintError tmTxt err
    Right _ -> pure ()

mkTest :: HasCallStack => Ctx -> T.Text -> Expectation
mkTest ctx txt = case processFile "test.rll" txt of
  Left err -> expectationFailure $ M.errorBundlePretty err
  Right tc -> case runTc ctx tc of
    Left err -> expectationFailure $ T.unpack $ prettyPrintError txt err
    Right _ -> pure ()

rawTest :: HasCallStack => T.Text -> Expectation
rawTest = mkTest emptyCtx

baseTest :: HasCallStack => T.Text -> Expectation
baseTest = mkTest baseCtx

mkFailTest :: HasCallStack => Ctx -> TyErr -> T.Text -> Expectation
mkFailTest ctx err txt = case processFile "test.rll" txt of
  Left err -> expectationFailure $ M.errorBundlePretty err
  Right tc -> case evalTc ctx tc of
    Left err' -> err' `shouldBe` err
    Right _ -> expectationFailure "Expected to fail."

baseFailTest :: HasCallStack => TyErr -> T.Text -> Expectation
baseFailTest = mkFailTest baseCtx
