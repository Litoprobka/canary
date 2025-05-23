{-# OPTIONS_GHC -Wno-partial-fields #-}

module TypeChecker.TypeError (TypeError (..), typeError) where

import Common hiding (Blank)
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
    | ArgCountMismatch Loc -- "different amount of arguments in a match statement"
    | ArgCountMismatchPattern (Pattern 'Fixity) Int Int
    | NotAFunction Loc TypeDT -- pretty fTy <+> "is not a function type"
    | SelfReferential Loc UniVar TypeDT
    | NoVisibleTypeArgument (Expr 'Fixity) (Type 'Fixity) TypeDT
    | ConstructorReturnType {con :: Name, expected :: Name, returned :: Name}

typeError :: Diagnose :> es => TypeError -> Eff es a
typeError =
    fatal . one . \case
        CannotUnify lhs rhs ->
            Err
                Nothing
                ("cannot unify" <+> pretty lhs <+> "with" <+> pretty rhs)
                (mkNotes [(getLoc lhs, This $ pretty lhs <+> "originates from"), (getLoc rhs, This $ pretty rhs <+> "originates from")])
                []
        NotASubtype lhs rhs mbField ->
            Err
                Nothing
                (pretty lhs <+> "is not a subtype of" <+> pretty rhs <> fieldMsg)
                (mkNotes [(getLoc lhs, This "lhs"), (getLoc rhs, This "rhs")])
                []
          where
            fieldMsg = case mbField of
                Nothing -> ""
                Just field -> ": right hand side does not contain" <+> pretty field
        MissingField row field ->
            Err
                Nothing
                (either pretty pretty row <+> "does not contain field" <+> pretty field)
                (mkNotes [(either getLoc getLoc row, This "row arising from"), (getLoc field, This "field arising from")])
                []
        MissingVariant ty variant ->
            Err
                Nothing
                (pretty ty <+> "does not contain variant" <+> pretty variant)
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
                "different amount of arguments in a match statement"
                (mkNotes [(loc, Blank)])
                []
        ArgCountMismatchPattern pat expected got ->
            Err
                Nothing
                ("incorrect arg count (" <> pretty got <> ") in pattern" <+> pretty pat <> ". Expected" <+> pretty expected)
                (mkNotes [(getLoc pat, Blank)])
                []
        NotAFunction loc ty ->
            Err
                Nothing
                (pretty ty <+> "is not a function type")
                (mkNotes [(loc, This "arising from function application")])
                []
        SelfReferential loc var ty ->
            Err
                Nothing
                ("self-referential type" <+> pretty var <+> "~" <+> pretty ty)
                (mkNotes [(loc, This "arising from"), (getLoc ty, Where "and from")])
                []
        NoVisibleTypeArgument expr tyArg ty ->
            Err
                Nothing
                "no visible type argument"
                ( mkNotes
                    [ (getLoc expr, This "when applying this expression")
                    , (getLoc tyArg, This "to this type")
                    , (getLoc ty, Where $ "where the expression has type" <+> pretty ty)
                    ]
                )
                []
        ConstructorReturnType{con, expected, returned} ->
            Err
                Nothing
                (pretty con <+> "doesn't return the right type") -- todo: proper wording
                ( mkNotes
                    [ (getLoc expected, This "expected return type")
                    , (getLoc returned, Where "this type is returned instead")
                    , (getLoc con, Where "in the definition of this constructor")
                    ]
                )
                []
