{-# OPTIONS_GHC -Wno-partial-fields #-}

module TypeChecker.TypeError (TypeError (..), typeError, UnificationError (..), typeErrorWithLoc) where

import Common
import Data.Row (ExtRow (..), OpenName, prettyRow)
import Diagnostic
import Error.Diagnose (Marker (..), Note (Note), Report (..))
import Eval ()
import LangPrelude
import Prettyprinter (sep, vsep)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax
import Syntax.Term (withVis)

type CType = Located CoreType

data TypeError
    = CannotUnify {loc :: Loc, lhs :: Doc AnsiStyle, rhs :: Doc AnsiStyle, context :: UnificationError}
    | MissingField (Either CType (Term 'Fixity)) OpenName
    | MissingVariant CType OpenName
    | EmptyMatch Loc
    | ArgCountMismatch Loc -- "different amount of arguments in a match expression"
    | NotEnoughArgumentsInTypeOfMatch {loc :: Loc, expectedArgCount :: Int, actualArgCount :: Int, ty :: CoreType}
    | ArgCountMismatchPattern (Pattern 'Fixity) Int Int
    | NotAFunction Loc CType
    | NotASigma Loc CType
    | NoVisibleTypeArgument Loc (Type 'Fixity) CoreType
    | SigmaVisibilityMismatch {loc :: Loc, expectedVis :: Visibility, actualVis :: Visibility}
    | ConstructorVisibilityMismatch {loc :: Loc}
    | ConstructorReturnType {con :: Name, expected :: Name_, returned :: CoreTerm}
    | TooManyArgumentsInPattern {loc :: Loc}
    | NotEnoughArgumentsInPattern {loc :: Loc}

type Spine = [(Visibility, Value)]

data UnificationError
    = NotEq CoreTerm CoreTerm
    | PruneNonRenaming Spine
    | PruneNonPattern Spine
    | NonVarInSpine CoreTerm
    | OccursCheck UniVar
    | EscapingVariable (Maybe UniVar) Level
    | MissingFields {row :: Row CoreType, missing :: Row CoreType}

typeErrorWithLoc :: Diagnose :> es => (Loc -> TypeError) -> Eff es a
typeErrorWithLoc mkTypeError =
    currentLoc >>= \case
        Nothing -> internalError' "typeErrorWithLoc: no location available"
        Just loc -> typeError $ mkTypeError loc

typeError :: Diagnose :> es => TypeError -> Eff es a
typeError =
    fatal . one . \case
        CannotUnify{loc, lhs, rhs, context} ->
            Err
                Nothing
                "Type error"
                (mkNotes [(loc, This "when typechecking this")])
                [ Note $ vsep ["when trying to unify", lhs, rhs]
                , noteFromUnificationError context
                ]
        MissingField row field ->
            Err
                Nothing
                (either prettyDef prettyDef row <+> "does not contain field" <+> prettyDef field)
                (mkNotes [(either getLoc getLoc row, This "row arising from"), (getLoc field, This "field arising from")])
                []
        MissingVariant ty variant ->
            Err
                Nothing
                (prettyDef ty <+> "does not contain variant" <+> prettyDef variant)
                (mkNotes [(getLoc ty, This "type arising from"), (getLoc variant, This "variant arising from")])
                []
        EmptyMatch loc ->
            Err
                Nothing
                "empty match expression"
                (mkNotes [(loc, Blank)])
                []
        ArgCountMismatch loc ->
            Err
                Nothing
                "different amount of arguments in a match expression"
                (mkNotes [(loc, Blank)])
                []
        ArgCountMismatchPattern pat expected got ->
            Err
                Nothing
                ("incorrect arg count (" <> pretty got <> ") in pattern" <+> prettyDef pat <> ". Expected" <+> pretty expected)
                (mkNotes [(getLoc pat, Blank)])
                []
        NotEnoughArgumentsInTypeOfMatch{loc, expectedArgCount, actualArgCount, ty} ->
            Err
                Nothing
                ("this match expression has" <+> pretty expectedArgCount <+> "arguments, but its type has only" <+> pretty actualArgCount)
                (mkNotes [(loc, This "match expression")])
                [Note $ "type of the expression:" <+> prettyDef ty]
        NotAFunction loc ty ->
            Err
                Nothing
                (prettyDef ty <+> "is not a function type")
                (mkNotes [(loc, This "arising from function application")])
                []
        NotASigma loc ty ->
            Err
                Nothing
                (prettyDef ty <+> "is not a dependent pair type")
                (mkNotes [(loc, This "arising from this dependent pair")])
                []
        NoVisibleTypeArgument loc tyArg ty ->
            Err
                Nothing
                "no visible type argument"
                ( mkNotes
                    [ (loc, This "when applying this expression")
                    , (getLoc tyArg, This "to this type")
                    ]
                )
                [Note $ "the expression has type" <+> prettyDef ty]
        -- perhaps the two visibility mismatch errors should be unified
        SigmaVisibilityMismatch{loc, expectedVis, actualVis} ->
            Err
                Nothing
                "visibility mismatch in dependent pair argument"
                (mkNotes [(loc, This "in this pattern")])
                [ Note $ "the pattern is expected to be" <+> pretty (show @Text expectedVis)
                , Note $ "but it is" <+> pretty (show @Text actualVis)
                ]
        ConstructorVisibilityMismatch{loc} ->
            Err
                Nothing
                "unexpected implicit argument in pattern"
                (mkNotes [(loc, This "explicit argument expected here")])
                []
        ConstructorReturnType{con, expected, returned} ->
            Err
                Nothing
                (prettyDef con <+> "doesn't return the right type") -- todo: proper wording
                (mkNotes [(getLoc con, Where "in the definition of this constructor")])
                [ Note $ "expected:" <+> prettyDef expected
                , Note $ "got:" <+> prettyDef returned
                ]
        -- these two error messages are pretty crappy. They need, at list, expected and actual argument counts
        TooManyArgumentsInPattern{loc} ->
            Err Nothing "too many arguments in a constructor" (mkNotes [(loc, This "this constructor pattern has too many arguments")]) []
        NotEnoughArgumentsInPattern{loc} ->
            Err
                Nothing
                "not enough arguments in a constructor"
                (mkNotes [(loc, This "this constructor pattern doesn't have enough arguments")])
                []

-- todo: proper error messages
noteFromUnificationError :: UnificationError -> Note (Doc AnsiStyle)
noteFromUnificationError = \case
    NotEq lhs rhs -> Note $ vsep ["specifically, these types are incompatible", prettyDef lhs, prettyDef rhs]
    PruneNonRenaming spine -> Note $ "can't prune a spine that's not a renaming:" <+> prettySpine spine
    PruneNonPattern spine -> Note $ "can't prune a non-pattern spine:" <+> prettySpine spine
    NonVarInSpine term -> Note $ "non-var in spine:" <+> prettyDef term
    OccursCheck uni -> Note $ "solving the unification variable" <+> prettyDef uni <+> "resulted in a type that refers to itself"
    EscapingVariable (Just uni) lvl -> Note $ "variable" <+> "#" <> pretty lvl.getLevel <+> "is not in scope of" <+> prettyDef uni
    EscapingVariable Nothing lvl -> Note $ "variable" <+> "#" <> pretty lvl.getLevel <+> "is not in scope of a renaming"
    MissingFields{row, missing} -> Note $ "row" <+> prettyNoExtRow row <+> "is missing these fields:" <+> prettyNoExtRow missing
  where
    prettyNoExtRow = prettyRow prettyDef prettyDef . NoExtRow
    prettySpine = sep . map (\(vis, val) -> withVis vis (prettyDef val))
