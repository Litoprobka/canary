{-# OPTIONS_GHC -Wno-partial-fields #-}

module TypeChecker.TypeError (TypeError (..), typeError) where

import Common
import Diagnostic
import Error.Diagnose (Marker (..), Report (..))
import Eval (Value)
import LangPrelude
import Syntax
import Syntax.Row (OpenName)

type TypeDT = Located Value

data TypeError
    = CannotUnify TypeDT TypeDT
    | NotASubtype TypeDT TypeDT (Maybe OpenName)
    | MissingField (Either TypeDT (Term 'Fixity)) OpenName
    | MissingVariant TypeDT OpenName
    | EmptyMatch Loc -- empty match expression
    | ArgCountMismatch Loc -- "different amount of arguments in a match expression"
    | ArgCountMismatchPattern (Pattern 'Fixity) Int Int
    | NotAFunction Loc TypeDT -- pretty fTy <+> "is not a function type"
    | SelfReferential Loc UniVar TypeDT
    | NoVisibleTypeArgument Loc (Type 'Fixity) TypeDT
    | ConstructorReturnType {con :: Name, expected :: Name, returned :: Name}

typeError :: Diagnose :> es => TypeError -> Eff es a
typeError =
    fatal . one . \case
        CannotUnify lhs rhs ->
            Err
                Nothing
                ("cannot unify" <+> prettyDef lhs <+> "with" <+> prettyDef rhs)
                (mkNotes [(getLoc lhs, This $ prettyDef lhs <+> "originates from"), (getLoc rhs, This $ prettyDef rhs <+> "originates from")])
                []
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
