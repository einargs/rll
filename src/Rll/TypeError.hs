module Rll.TypeError
  ( TyErr(..), prettyPrintError
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as LT
import Errata qualified as E
import Errata.Styles qualified as S
import Data.Vector qualified as V
import Prettyprinter qualified as P
import Prettyprinter ((<+>))
import Prettyprinter.Render.Text qualified as PRT
import Debug.Trace qualified as D
import Data.Maybe (mapMaybe)

import Rll.Ast

data TyErr
  -- | This is an error we didn't think was possible.
  = CompilerLogicError Text (Maybe Span)
  -- | The type variable was not bound.
  | UnknownTypeVar TyVar Span
  -- | The term variable has either been dropped or never introduced.
  | UnknownTermVar Var Span
  -- | We know the term var was used/dropped.
  --
  -- Variable, current usage span, where it was used/dropped
  | RemovedTermVar Var Span Span
  -- | Referenced an undefined datatype.
  | UnknownDataType Var Span
  -- | The introduction of a new variable would shadow an existing one.
  --
  -- The new variable, it's span, and the span of the existing one
  | VarAlreadyInScope Var Span Span
  -- | We expected the type to have a different kind.
  -- Expected kind, type's kind, type loc
  -- TODO may eventually need a span for specific site indication?
  | ExpectedKind Kind Kind Span
  -- | Cannot drop a variable that is still borrowed.
  | CannotDropBorrowedVar Var [Var] Span
  -- | This type cannot be dropped.
  | CannotDropTy Ty Span
  -- | We cannot consume or move this var while it is borrowed.
  --
  -- borrowed variable, variables borrowing it, span of where trying to use it
  | CannotUseBorrowedVar Var [Var] Span
  -- | Variables introduced inside a scope were not properly used
  -- or dropped and are escaping the scope.
  --
  -- Escaping variables, span of scope
  | VarsEscapingScope [Var] Span
  -- | Case statement has no branches.
  | NoCaseBranches Span
  -- | The end contexts of different branches of a case statement can't join.
  --
  -- Uses the output of `diffCtxTerms` minus the borrow count.
  | CannotJoinCtxs [(Span, [(Var,Int,Ty)])] Span
  -- | The result types of different branches of a case statement aren't equal.
  | CannotJoinTypes [(Span, Ty)] Span
  -- | A reference to a single variable cannot have a composite lifetime (`LtJoin`).
  --
  -- The type and a span indicating the reference.
  | RefLtIsComposite Ty Span
  -- | Cannot case split on the type.
  --
  -- Type of expression, expression span
  | TypeIsNotEnum Ty Span
  -- | Used an unknown constructor in a case of expression.
  --
  -- Name of the enum, unknown case, span
  --
  -- TODO the last span should be the span for the enum branch,
  -- but the parser doesn't do that right now, so instead it's
  -- for the entire case statement.
  | UnknownEnumCase Var SVar
  -- | Unknown data constructor. May merge with some of the enum errors.
  | UnknownDataCon Var Span
  -- | The case of branch used the wrong number of variables for a constructor.
  | BadEnumCaseVars [SVar] [Ty] Span
  -- | Missing a branch for this enum case in this case of expression.
  | NoBranchForCase Text Span
  -- | Multiple branches for the same enum case in this case of expression.
  | MultBranchesForCase Text Span
  -- | Cannot destructure the type.
  --
  -- Type of the expression, span of the expression
  | TypeIsNotStruct Ty Span
  -- | The constructor used in let struct did not match the struct type.
  --
  -- The incorrect constructor, the correct constructor, the struct type,
  -- the span of the incorrect constructor in the let struct
  | WrongConstructor Var Text Var Span
  -- | The number of variables in let struct did not match the struct definition.
  | BadLetStructVars [SVar] [Ty]
  -- | A multi-use closure consumed external variables.
  --
  -- List of consumed variables, span of closure.
  -- TODO: list of variable locations
  | MultiFnCannotConsume [Var] Span
  -- | Too many borrows or drops of an external variable.
  | UnstableBorrowCounts [Var] Span
  -- | Inferred borrowed variables does not match specified borrowed variables.
  --
  -- Type specifying borrowed variables, list of variables, closure span
  | IncorrectBorrowedVars Ty [Ty] Span
  -- | Attempted to copy a variable that is not a reference.
  --
  -- Type of variable, span of copy.
  | CannotCopyNonRef Ty Span
  -- | Cannot synthesize a function type or univ type without an argument annotation.
  | SynthRequiresAnno Span
  -- | Cannot apply a type argument to this type.
  --
  -- type, span of AppTy
  | TyIsNotUniv Ty Span
  -- | Must be a function to accept an argument.
  --
  -- Type, span of AppTm
  | TyIsNotFun Ty Span
  -- | Cannot synthesize the type of a recursive function. Please use an annotation.
  | CannotSynthFixTm Span
  -- | We expected a specific type and got a different one.
  | ExpectedType Ty Ty
  -- | Type binding mismatch.
  --
  -- May eventually remove this as an error, but want to check how that would work first.
  | TypeVarBindingMismatch TyVarBinding Span TyVarBinding Span
  -- | Mismatch of the kinds when checking a type variable.
  | TypeKindBindingMismatch Kind Span Kind Span
  -- | Cannot create a recursive function from a single use function.
  --
  -- Span for recursive function, span for incorrect type
  | CannotFixSingle Span Span
  -- | Error for when the data type already exists.
  --
  -- Name of data type, span for second definition
  | DataTypeAlreadyExists Var Span
  -- | A top level term already exists with that name.
  --
  -- Name of term, span for second definition
  | DefAlreadyExists Var Span
  -- | We expected type 1 but inferred type 2.
  --
  -- Expected type, inferred type, span of terms.
  | ExpectedButInferred Ty Ty Span
  -- | We expected a function type. Thrown when checking a FunTm with
  -- a non-function type.
  --
  -- Type got, span of term.
  -- TODO: combine with TyIsNotFun
  | ExpectedFunType Ty Span
  -- | We expected a function or universal quantification type as
  -- the argument to a FixTm.
  --
  -- Type, span of fix term
  | ExpectedFixableType Ty Span
  -- | We expected a forall type. Thrown when checking a Poly with
  -- a non-univ type.
  --
  -- Type got, span of term.
  | ExpectedUnivType Ty Span
  -- | Cannot take a reference of a reference.
  --
  -- Type of thing being ref'd, span of term being ref'd
  | CannotRefOfRef Ty Span
  -- | Cannot apply a type to a non-type operator.
  --
  -- actual kind, location of type with that kind
  | IsNotTyOp Kind Span
  -- | This Univ type creates a rank 2 type.
  | NoRank2 Ty
  -- | No polymorphic functions in a data type field.
  | NoPolyInField Ty
  -- | Cannot return a polymorphic function.
  | NoPolyInRet Ty
  -- | Polymorphic type arguments were only partially listed in function
  -- definition. They must all be present or all be omitted.
  | PartialTyArgsInLam Ty Span
  -- | You defined too many arguments for this lambda compared to the
  -- type it is being checked against.
  | TooManyArgsInLam Ty Span
  -- | When specializing a polymorphic function you must fully apply
  -- the type arguments.
  --
  -- Type left over, span of type app.
  | NotFullyApplied Ty Span
  deriving (Eq, Show)

tpretty :: P.Pretty a => a -> Text
tpretty = ptext . P.pretty

ptext :: P.Doc ann -> Text
ptext = PRT.renderStrict . P.layoutSmart P.defaultLayoutOptions

varList :: [Var] -> Text
varList = T.intercalate ", " . fmap (.name)

-- | Pretty print the error message.
--
-- The source text, the error message.
prettyPrintError :: Text -> TyErr -> Text
prettyPrintError source err = LT.toStrict $ E.prettyErrors source [errMsg] where
  lineLengths = V.fromList $ f <$> T.lines source where
    f line = case T.findIndex (/=' ') line of
      Just start -> Just (start + 1, (T.length line) + 1)
      Nothing -> Nothing
  getColAt i = lineLengths V.! (i-1)

  spanToPtrs connect lbl ptrStyle s = mapMaybe f [s.startLine..s.endLine] where
    f :: Int -> Maybe E.Pointer
    f line = g line <$> getColAt line
    g :: Int -> (Int, Int) -> E.Pointer
    g line (start, end) = E.Pointer line startCol endCol connect lbl ptrStyle where
      startCol = if s.startLine == line then s.startColumn else start
      endCol = if s.endLine == line then s.endColumn else end

  defaultSpanToPtrs = spanToPtrs True Nothing S.fancyRedPointer

  defaultStyle = S.fancyYellowStyle
  highlightStyle = defaultStyle{E.styleEnableDecorations =False}
  spanToBlockLoc s = (s.file, s.startLine, s.startColumn)
  highlightBlock s = E.Block highlightStyle (spanToBlockLoc s)
  defBlock s = E.Block defaultStyle (spanToBlockLoc s)
  simpleBlock s msg = defBlock s (Just msg) (defaultSpanToPtrs s) Nothing
  block s hdr ptrs bdy = E.Errata Nothing
    [defBlock s hdr ptrs bdy] Nothing

  spanMsg s msg = block s (Just msg) (defaultSpanToPtrs s) Nothing

  errMsg = case err of
    -- TODO: equip with spans for each context so I can nicely point at each context.
    CannotJoinCtxs sCtxs s ->
      let f (v,bc,ty) = P.pretty v <+> P.parens (P.pretty bc) <> ": " <> P.pretty ty
          toBlock (s, ctx) = simpleBlock s (ptext $ P.list $ f <$> ctx)
          blocks = toBlock <$> sCtxs
      in E.Errata (Just "Cannot join contexts:") blocks Nothing

    -- TODO: maybe have a block showing where the expected type came from?
    ExpectedButInferred exp inf s ->
      spanMsg s $ ptext $ P.vsep $ P.group <$>
      ["Expected:" <> P.line <> P.pretty exp
      , "But got:" <> P.line <> P.pretty inf
      ]

    SynthRequiresAnno s -> block s
      (Just "Type synthesis requires an argument annotation.")
      (spanToPtrs True Nothing S.fancyRedPointer s)
      Nothing

    UnknownTermVar v s -> block s
      (Just $ "Unknown variable " <> v.name)
      (spanToPtrs True Nothing S.fancyRedPointer s)
      Nothing

    RemovedTermVar v use dropped ->
      E.Errata (Just $ ptext $ "Term variable" <+> P.pretty v <+> "was used after being used/dropped")
      [ simpleBlock use "Used here"
      , simpleBlock dropped "Removed here"
      ] Nothing

    CannotUseBorrowedVar v borrowers s -> block s
      (Just $ "Cannot use variable " <> v.name <> " while it is borrowed")
      (defaultSpanToPtrs s)
      (Just $ "Borrowed by: " <> varList borrowers)

    IncorrectBorrowedVars borrowedTy inferredLts s ->
      let tySpan = getSpan borrowedTy
          inferListTxt = ptext $ "inferred borrow list:" <+> P.pretty inferredLts
          headerMsg = ptext $ P.fillSep
            ["inferred borrow list"
            , P.pretty inferredLts
            , "did not match specified borrow list."]
          specMsg = "borrow list specified here:"
          funcBody = "in function body"
          f :: Ty -> E.Block
          f ty = defBlock s (Just msg) (defaultSpanToPtrs s) Nothing
            where s = getSpan ty
                  msg = ptext $ "inferrred" <+> P.pretty ty <+> "from:"
          inferredLocs = f <$> inferredLts
      in E.Errata
        (Just headerMsg)
        ([ highlightBlock s (Just funcBody) (defaultSpanToPtrs s) Nothing
        ] <> inferredLocs <> [
          defBlock tySpan (Just specMsg) (defaultSpanToPtrs tySpan) Nothing
        ])
        Nothing

    WrongConstructor incorrectCon correctCon tyName expSpan ->
      let msg = T.concat
            [ incorrectCon.name, " is not a constructor for struct "
            , tyName.name, "; try ", correctCon, "."]
      in block expSpan
        (Just msg)
        (defaultSpanToPtrs expSpan)
        Nothing

    VarsEscapingScope vars s -> spanMsg s $
      "Variables escaping scope: " <> varList vars

    MultiFnCannotConsume vars s -> spanMsg s $
      "Multi-use function cannot consume variables: " <> varList vars

    ExpectedFunType ty s ->
      let tySpan = getSpan ty
          funMsg = "Function term"
          tyMsg = "Type should be a function type"
      in E.Errata
        (Just "Type does not match function term")
        [ highlightBlock s (Just funMsg) (defaultSpanToPtrs s) Nothing
        , defBlock tySpan (Just tyMsg) (defaultSpanToPtrs tySpan) Nothing
        ]
        Nothing

    ExpectedFixableType ty s ->
      let tySpan = getSpan ty
          funMsg = "fix site"
          tyMsg = "Type should be a function or polymorphic type."
      in E.Errata
        (Just "Type must be polymorphic or a function to make recursive")
        [ highlightBlock s (Just funMsg) (defaultSpanToPtrs s) Nothing
        , defBlock tySpan (Just tyMsg) (defaultSpanToPtrs tySpan) Nothing
        ]
        Nothing

    ExpectedUnivType ty s ->
      let tySpan = getSpan ty
          polyMsg = "Polymorphic term"
          tyMsg = "Type should be a polymorphic type"
      in E.Errata
        (Just "Type does not match polymorphic term")
        [ highlightBlock s (Just polyMsg) (defaultSpanToPtrs s) Nothing
        , defBlock tySpan (Just tyMsg) (defaultSpanToPtrs tySpan) Nothing
        ]
        Nothing

    CannotFixSingle tmSpan tySpan ->
      let polyMsg = "Polymorphic term"
          tyMsg = "Type should be a polymorphic type"
      in E.Errata
        (Just "Recursive functions cannot be single use.")
        [ highlightBlock tmSpan (Just "Function definition") (defaultSpanToPtrs tmSpan) Nothing
        , defBlock tySpan (Just "Single-use type") (defaultSpanToPtrs tySpan) Nothing
        ]
        Nothing

    CannotSynthFixTm s -> spanMsg s
      "Cannot synthesize the type of a recursive function."

    CannotRefOfRef ty s -> spanMsg s
      "Cannot create a reference to a reference:"

    CannotCopyNonRef ty s -> spanMsg s
      "Can only copy a reference."

    TypeIsNotEnum ty s -> spanMsg s $ ptext $
      "expected an enum here, instead got type:" <> P.softline <> P.pretty ty

    TypeIsNotStruct ty s -> spanMsg s $ ptext $
      "expected a struct here, instead got type:" <> P.softline <> P.pretty ty

    TyIsNotFun ty s -> spanMsg s $ ptext $
      "Term is not a function. Type:" <> P.softline <> P.pretty ty

    IsNotTyOp kind s -> spanMsg s $ ptext $
      "Kind" <+> P.pretty kind <+> "is not a type operator and cannot take an argument."

    CompilerLogicError msg mbSpan ->
      let blocks = case mbSpan of
            Just s -> [defBlock s Nothing (defaultSpanToPtrs s) Nothing]
            Nothing -> []
      in E.Errata (Just msg) blocks Nothing

    -- TODO: fix up this message
    BadLetStructVars vars tys -> spanMsg (getSpan $ head vars) $ ptext $
      P.vsep $ [ "There was a problem with the variables in this let struct."
               , "Vars:" <+> P.pretty vars
               , "Expected Types:" <+> P.pretty tys
               ]

    UnknownDataType name s -> spanMsg s $ ptext $ "Unknown data type" <+> P.pretty name

    UnknownTypeVar name s -> spanMsg s $ ptext $ "Unknown type variable" <+> P.pretty name

    ExpectedKind ek ie s -> spanMsg s $ ptext $ P.fillSep
      ["Expected kind", P.pretty ek, "but got", P.pretty ie]

    NoRank2 ty -> spanMsg (getSpan ty)
      "This polymorphic type creates a rank 2 type that can't be specialized."

    UnstableBorrowCounts vars s -> spanMsg s $ ptext $
      "Too many borrows or drops of variables external to the closure:"
      <> P.softline <> P.pretty vars

    _ -> E.Errata (Just $ T.pack $ show err) [] Nothing
      -- [E.Block defaultStyle ("unimplemented", 1, 1) Nothing [] (Just $ T.pack $ show err)]
