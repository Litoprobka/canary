# A very WIP programming language

Canary (name subject to change), an ML family dependently-typed programming languge

There's no concrete plan for the language. For the most part, I'm just figuring out how compilers work.

The language recently underwent a type checker rewrite, and some features, such as polymorphic records and variants, are not supported by the new type checker yet.

## What is implemented

- a parser
- name resolution
- elaboration with dependent types, NbE and pattern unification, exhaustiveness check (currently unused)
  - dependent pattern matching
- custom operators
- a REPL that piggybacks off the existing NbE interpreter used in elaboration

## What is lacking

- actual compilation (duh)
- define-before-use and mutually recursive definitions are not supported by the type checker yet
- erasure is not implemented yet, which also means polymorphic functions aren't guaranteed to be parametric
- totality checking
- postponing is not implemented yet, so the type checker infers less than it could
- desugaring for nested patterns and multi-arg match
- support for modules, namespacing, imports, etc.
- pretty much everything else

## Overview

Syntax-wise, the language is very close to Haskell and Idris.

```haskell
type List a = Cons a (List a) | Nil

map : forall a b. (a -> b) -> List a -> b
map f = match
    (Cons x xs) -> Cons (f x) (map f xs)
    Nil -> Nil
```

Unlike Haskell, type signatures use a single colon. Multiple function bodies are not allowed, but we have the `match` expression (equivalent to `\cases` in Haskell) to help with that.

The compiler infers forall clauses for names prefixed by a quote, so these two bindings are equivalent:

```haskell
id1 : 'a -> 'a
id1 x = x

id2 : forall a. a -> a
id2 x = x
```

### Dependent pattern matching

Just like in most dependently-typed languages, matching on a value refines its type in the local context

```haskell
type Peano = S Peano | Z

type Vec : Peano -> Type -> Type where
    VNil : forall a. Vec Z a
    VCons : forall a n. a -> Vec n a -> Vec (S n) a

-- foreach is our syntax for dependent functions, which is probably going to be replaced by Idris-like `(x : a) -> b x`
replicate : forall a. foreach (n : Peano) -> a -> Vec n a
replicate x = match
    Z -> VNil                      -- in this branch, the output type is Vec Z a, so VNil is well-typed
    S m -> VCons x (replicate m x) -- in this branch, the output type is Vec (S m) a
```

We can also define our own equality type

```haskell
type (===) : forall a. a -> a -> Type where
    Refl : forall a (x : a). a === a

cast : ('a === 'b) -> 'a -> 'b
cast equality x = case equality of
    Refl -> x
```

### Row polymorphism

The language has polymorphic records and variants, based on *Extensible records with scoped labels*. No dependently-typed records (yet?).

As of the type checker rewrite, records and variants are not implemented yet.

```haskell
getX : { x : 'a | 'r } -> 'a
getX record = record.x

These : Type -> Type -> Type Type
These a b = [| 'This a, 'That b, 'These (Pair a b) |]

getA : These a -> Maybe a
getA = match
    'This x -> Just x
    'These (MkPair x _) -> Just x
    _ -> Nothing

-- open variants
getThis : [| 'This 'a | r] -> Maybe 'a
getThis = match
    'This x -> Just x
    _ -> Nothing
```

### Wildcard lambdas

Canary doesn't have operator sections (`(+3) :: Int -> Int`). Instead, there's a more general feature called wildcard lambdas (or something else if I come up with a better name).

```haskell
plus3 = (_ + 3)
```

In expression context, wildcards are desugared to a lambda. The scope is determined by parentheses / brackets / braces. Multiple wildcards are desugared to multiple lambda parameters.

```haskell
expr x = (_ + 8 * _ |> (f _ x))
```
This funky example desugars to:

```haskell
expr x = \$1 $2 -> $1 + 8 * $2 |> (\$1 -> f $1 x)
```

List and record expressions also act as scope delimiters

```haskell
someList = [_, 1, 2, _, _, 3]

someRecord = {x = 0, y = _}
```

### User-defined operators

Just like Haskell, Canary features user-defined operators

```haskell
infix %
(%) : Int -> Int -> Int
(%) = mod
```

Instead of a numeric precedence, you may specify a relation between two operators

```haskell
infix == equals !=
infix !=
infix left && below ==
infix left || below ==
infix left + above ==
infix left - equals +
infix left * above +
```

Relations are transitive, so the declarations above have the same meaning as

```haskell
infix ==, != above &&, || below +, -, *
infix left && below ==, !=, +, -, *
infix left || below ==, !=, +, -, *
infix left +, - above ==, !=, &&, || below *
infix left * above +, -, ==, !=, &&, ||
```

Note how there is no relation between `&&` and `||` specified - that means, whenever these two operators are used together, we must disambiguate the usage with parentheses

```haskell
someCondition n = (n > 5 && n < 10) || n == 42
```

If we introduce a cyclic relation - say, we add `infix & above + below ==` to the above - the cyclic part of the dependency graph becomes ambiguous and requires parentheses

```haskell
infix ==, != above &&, || below *
infix left && below ==, !=, +, -, *
infix left || below ==, !=, +, - *
infix left +, - above &&, || below *
infix left * above +, -, ==, !=, &&, ||
infix &
```

#### Chainfix

Another feature compared to Haskell is the `chain` fixity. Multiple chain operator applications in a row desugar to a single application to a list

```haskell
infix chain ==

(==) : Eq a => a -> NonEmpty a -> Bool

test = 1 == 1 == 1 == 2
-- desugars to
test2 = (==) 1 [1, 1, 2]
```
