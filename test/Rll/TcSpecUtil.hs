{-# LANGUAGE BlockArguments, OverloadedStrings, QuasiQuotes #-}
module Rll.TcSpecUtil
  ( txt, stdFile, synthTo, checkTo, rawTest, baseTest
  , baseFailTest, baseCtx
  ) where

import Test.Hspec
import qualified Data.Text as T
import qualified Text.Megaparsec as M
import Control.Monad (void)
import Data.Maybe (mapMaybe)
import Data.Foldable (asum)
import Control.Applicative ((<|>))

import QuoteTxt
import Rll.AstUtil

import qualified Rll.Parser as RP
import Rll.TypeCheck
import Rll.Ast
import Rll.TypeError (prettyPrintError, TyErr(..))
import Rll.Context
import Rll.TcTools
import Rll.TcMonad
import Rll.Core

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

copyInt : forall M [] l : Lifetime. &l Int -M[]> Int
= \[l : Lifetime] r -> drop r in Int;

copyStr :
  forall M [] l : Lifetime.
  &l Str -M[]> Str
= \r -> drop r in Str;
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
compareCoreToTm fullCore@(Core cTy _ core) tm@Tm{tmf}
  | isLt cTy = err
  | otherwise = case (core, tmf) of
    -- Core has no anno so we skip it
    (_, Anno t1 ty) -> compareCoreToTm fullCore t1
    (CaseCF c1 cb, Case t1 tb) -> compareCoreToTm c1 t1 <|>
      allBranches cb tb
    (LetStructCF cCon cVars c1 c2, LetStruct tCon tVars t1 t2) ->
      cCon #= tCon <|> cVars #= tVars <|> compareCoreToTm c1 t1
      <|> compareCoreToTm c2 t2
    (LetCF cv c1 c2, Let tv t1 t2) -> cv #= tv
      <|> compareCoreToTm c1 t1 <|> compareCoreToTm c2 t2
    (LamCF cFix cPolys cArgs _ c1,
     FunTm tFix tPolys tArgs t1) -> tFix #= cFix <|> compareCoreToTm c1 t1
    (ModuleVarCF cv, TmVar tv) -> cv #= tv
    (LocalVarCF cv, TmVar tv) -> cv #= tv
    (ConCF _ cv, TmCon tv) -> cv #= tv
    (CopyCF cv, Copy tv) -> cv #= tv
    (RefCF cv, RefTm tv) -> cv #= tv
    (AppTyCF c1 _, AppTy t1 _) -> compareCoreToTm c1 t1
    (DropCF cv _ c1, Drop tv t1) -> cv #= tv <|> compareCoreToTm c1 t1
    (AppTmCF c1 cs, _) ->
      let (ts, t1) = collectApps tm
      in compareCoreToTm c1 t1
        <|> asum (zipWith compareCoreToTm cs $ reverse ts)
    (LiteralCF cl, LiteralTm tl) -> cl #= tl
    _ -> err
  where
  isLt Ty{tyf=LtOf _} = True
  isLt Ty{tyf=LtJoin _} = True
  isLt _ = False
  err = Just (fullCore, tm)
  collectApps t = case t.tmf of
    AppTm t1 t2 -> let (ls, tf) = collectApps t1 in (t2:ls, tf)
    _ -> ([], t)
  (#=) :: Eq a => a -> a -> Maybe (Core, Tm)
  a #= b | a == b = Nothing
         | otherwise = err
  allBranches cb tb | length cb /= length tb = error $ "wrong length"
                    | otherwise = asum $ zipWith compareBranches cb tb
  compareBranches :: CaseBranch Core -> CaseBranch Tm -> Maybe (Core, Tm)
  compareBranches (CaseBranch cCon cVars c1) (CaseBranch tCon tVars t1) =
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
        case asum $ zipWith compare (snd <$> coreFns) tmFns of
          Nothing -> pure ()
          Just (fullCore, fullTm, core, tm) -> expectationFailure $
            "Core didn't match term.\nCore(" <> show core.span
            <> "): " <> show core
            <> "\nTm(" <> show tm.span <> "): " <> show tm
            <> "\nFull Tm: " <> show fullTm
            <> "\nFull Core: " <> show fullCore
  where
    compare core tm = (\(a,b) -> (core, tm, a, b)) <$> compareCoreToTm core tm

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
