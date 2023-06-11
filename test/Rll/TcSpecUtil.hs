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
import Data.Maybe (mapMaybe)
import Data.Foldable (asum)
import Control.Applicative ((<|>))

import QuoteTxt
import qualified Rll.Parser as RP
import Rll.TypeCheck
import Rll.Ast
import Rll.TypeError (prettyPrintError, TyErr(..))
import Rll.Context
import Rll.Tc
import Rll.Core

es :: Span
es = Span "test.rll" 1 1 1 1

tyCon v = TyCon (Var v) es
refTy v ty = RefTy (LtOf (Var v) es) ty es
tyVar v i = TyVar (MkTyVar v i) es
staticLt = LtJoin [] es

processFile :: String -> T.Text
  -> Either (M.ParseErrorBundle T.Text RP.RllParseError) (Tc ())
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

-- |
--
-- We don't check that the types are equal because we haven't corrected
-- the type variable indices in `Tm`.
compareCoreToTm :: Core -> Tm -> Maybe (Core, Tm)
compareCoreToTm fullCore@(Core cTy _ core) tm = case (core, tm) of
  -- Core has no anno so we skip it
  (_, Anno t1 ty _) -> compareCoreToTm fullCore t1
  (CaseCF c1 cb, Case t1 tb _) -> compareCoreToTm c1 t1 <|>
    allBranches cb tb
  (LetStructCF cCon cVars c1 c2, LetStruct tCon tVars t1 t2 _) ->
    cCon #= tCon <|> cVars #= tVars <|> compareCoreToTm c1 t1
    <|> compareCoreToTm c2 t2
  (LetCF cv c1 c2, Let tv t1 t2 _) -> cv #= tv
    <|> compareCoreToTm c1 t1 <|> compareCoreToTm c2 t2
  (LamCF sv _ c1, FunTm tv _ t1 _) -> sv #= tv <|> compareCoreToTm c1 t1
  (PolyCF _ _ c1, Poly _ t1 _) -> compareCoreToTm c1 t1
  (VarCF cv, TmVar tv _) -> cv #= tv
  (ConCF cv, TmCon tv _) -> cv #= tv
  (CopyCF cv, Copy tv _) -> cv #= tv
  (RefCF cv, RefTm tv _) -> cv #= tv
  (AppTyCF c1 _, AppTy t1 _ _) -> compareCoreToTm c1 t1
  (DropCF cv c1, Drop tv t1 _) -> cv #= tv <|> compareCoreToTm c1 t1
  (AppTmCF c1 c2, AppTm t1 t2 _) -> compareCoreToTm c1 t1 <|> compareCoreToTm c2 t2
  (FixCF cv c1, FixTm tv t1 _) -> cv #= tv <|> compareCoreToTm c1 t1
  (IntLitCF ci, IntLit ti _) -> ci #= ti
  (StringLitCF cs, StringLit ts _) -> cs #= ts
  _ -> err
  where
  err = Just (fullCore, tm)
  (#=) :: Eq a => a -> a -> Maybe (Core, Tm)
  a #= b | a == b = Nothing
         | otherwise = err
  allBranches cb tb | length cb /= length tb = error $ "wrong length"
                    | otherwise = asum $ zipWith compareBranches cb tb
  compareBranches :: (SVar, [SVar], Core) -> CaseBranch -> Maybe (Core, Tm)
  compareBranches (cCon,cVars,c1) (CaseBranch tCon tVars t1) =
    cCon #= tCon <|> cVars #= tVars <|> compareCoreToTm c1 t1

mkTest :: HasCallStack => Ctx -> T.Text -> Expectation
mkTest ctx txt = case M.parse RP.fileDecls "test.rll" txt of
  Left err -> expectationFailure $ M.errorBundlePretty err
  Right decls ->
    let tmFns = flip mapMaybe decls \case
          (FunDecl _ _ tm _) -> Just tm
          _ -> Nothing
    in case evalTc ctx $ typeCheckFile decls of
      Left err -> expectationFailure $ T.unpack $ prettyPrintError txt err
      Right coreFns ->
        case asum $ zipWith compareCoreToTm (snd <$> coreFns) tmFns of
          Nothing -> pure ()
          Just (core, tm) -> expectationFailure $
            "Core didn't match term.\nCore(" <> show core.span
            <> "): " <> show core <> "\nTm: " <> show tm

rawTest :: HasCallStack => T.Text -> Expectation
rawTest = mkTest emptyCtx

baseTest :: HasCallStack => T.Text -> Expectation
baseTest = mkTest baseCtx

mkFailTest :: HasCallStack => Ctx -> TyErr -> T.Text -> Expectation
mkFailTest ctx err txt = case processFile "test.rll" txt of
  Left perr -> expectationFailure $ M.errorBundlePretty perr
  Right tc -> case evalTc ctx tc of
    Left err' -> err' `shouldBe` err
    Right _ -> expectationFailure $ "Expected type error: " <> show err

baseFailTest :: HasCallStack => TyErr -> T.Text -> Expectation
baseFailTest = mkFailTest baseCtx
