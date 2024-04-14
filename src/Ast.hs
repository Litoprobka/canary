module Ast (Name, Term(..), Pattern(..), Declaration(..), Type'(..)) where

import Relude

type Name = Text --
type TypeVariable = Text

data Term
    = Lambda [Name] Term
    | Application Term [Term]
    | Let [(Pattern, Term)] Term
    | Case Term [(Pattern, Term)]
    | Match [([Pattern], Term)] -- | Haskell's \case
    | If Term Term Term
    | -- | value : Type
      Annotation Term Type'
    | Name Name
    | -- | .field.otherField.thirdField
      RecordLens [Name]
    | Constructor Name
    | -- | 'Constructor
      Variant Name
    | Record (HashMap Name Term)
    | List [Term]

data Pattern
    = VarP Name
    | ConP Name [Pattern]
    | VariantP Name [Pattern]
    | RecordP (HashMap Name Pattern)

data Type'
    = TypeName Name
    | TypeApplication Type' [Type']
    | Forall [TypeVariable] Type' 
    | Exists [TypeVariable] Type'
    -- | Row (HashMap Name Type')
    | VariantType (HashMap Name [Type'])
    | RecordType (HashMap Name Type')

-- should constructors or variants be a separate case?

data Declaration
    = ValueD Name [Pattern] Term [Declaration] -- todo: forbid local type declarations?
    | TypeD Name [TypeVariable] [(Name, [Type'])]
    | AliasD Name Type'
    | SigD Name Type'