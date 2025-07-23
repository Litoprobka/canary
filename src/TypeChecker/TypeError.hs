{-# OPTIONS_GHC -Wno-partial-fields #-}

module TypeChecker.TypeError (TypeError (..), typeError, UnificationError (..)) where

import Common
import Data.Row (OpenName)
import Diagnostic
import Error.Diagnose (Marker (..), Note (Note), Report (..))
import LangPrelude
import Prettyprinter (vsep)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Syntax

type CType = Located CoreType

data TypeError
    = CannotUnify {loc :: Loc, lhs :: CoreType, rhs :: CoreType, context :: UnificationError}
    | NotASubtype CType CType (Maybe OpenName)
    | MissingField (Either CType (Term 'Fixity)) OpenName
    | MissingVariant CType OpenName
    | EmptyMatch Loc -- empty match expression
    | ArgCountMismatch Loc -- "different amount of arguments in a match expression"
    | ArgCountMismatchPattern (Pattern 'Fixity) Int Int
    | NotAFunction Loc CType -- pretty fTy <+> "is not a function type"
    | NotASigma Loc CType
    | SelfReferential Loc UniVar CType
    | NoVisibleTypeArgument Loc (Type 'Fixity) CType
    | ConstructorReturnType {con :: Name, expected :: Name, returned :: Name}

data UnificationError
    = NotEq CoreTerm CoreTerm
    | PruneNonRenaming
    | PruneNonPattern
    | NonVarInSpine CoreTerm
    | OccursCheck UniVar
    | EscapingVariable Level

typeError :: Diagnose :> es => TypeError -> Eff es a
typeError =
    fatal . one . \case
        CannotUnify{loc, lhs, rhs, context} ->
            Err
                Nothing
                "Type error"
                (mkNotes [(loc, This "when typechecking this")])
                [ Note $ vsep ["when trying to unify", prettyDef lhs, prettyDef rhs]
                , noteFromUnificationError context
                ]
        NotASubtype lhs rhs mbField ->
            Err
                Nothing
                (prettyDef lhs <+> "is not a subtype of" <+> prettyDef rhs <> fieldMsg)
                (mkNotes [(getLoc lhs, This "lhs"), (getLoc rhs, This "rhs")])
                []
          where
            fieldMsg = case mbField of
                Nothing -> ""
                Just field -> ": right hand side does not contain" <+> prettyDef field
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
        SelfReferential loc var ty ->
            Err
                Nothing
                ("self-referential type" <+> prettyDef var <+> "~" <+> prettyDef ty)
                (mkNotes [(loc, This "arising from"), (getLoc ty, Where "and from")])
                []
        NoVisibleTypeArgument loc tyArg ty ->
            Err
                Nothing
                "no visible type argument"
                ( mkNotes
                    [ (loc, This "when applying this expression")
                    , (getLoc tyArg, This "to this type")
                    , (getLoc ty, Where $ "where the expression has type" <+> prettyDef ty)
                    ]
                )
                []
        ConstructorReturnType{con, expected, returned} ->
            Err
                Nothing
                (prettyDef con <+> "doesn't return the right type") -- todo: proper wording
                ( mkNotes
                    [ (getLoc expected, This "expected return type")
                    , (getLoc returned, Where "this type is returned instead")
                    , (getLoc con, Where "in the definition of this constructor")
                    ]
                )
                []

-- todo: proper error messages
noteFromUnificationError :: UnificationError -> Note (Doc AnsiStyle)
noteFromUnificationError = \case
    NotEq lhs rhs -> Note $ vsep ["specifically, these types are incompatible", prettyDef lhs, prettyDef rhs]
    PruneNonRenaming -> Note "can't prune a spine that's not a renaming"
    PruneNonPattern -> Note "can't prune a non-pattern spine"
    NonVarInSpine term -> Note $ "non-var in spine:" <+> prettyDef term
    OccursCheck uni -> Note $ "solving the unification variable" <+> pretty uni <+> "resulted in a type that refers to itself"
    EscapingVariable lvl -> Note $ "variable" <+> "#" <> pretty lvl.getLevel <+> "is not in scope of a unification variable"
