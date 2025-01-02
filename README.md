# A very WIP programming language

An unnamed (as of yet) Haskell-like programming languge

There's no concrete plan for the language. For the most part, I'm just figuring out how compilers work.

## What is implemented

- a parser that supports 90% of the syntax
- name resolution
- type checking

## What is lacking

- actual compilation (duh). The compile targets I've considered so far are [HVM-lang](https://github.com/HigherOrderCO/hvm-lang/), LLVM, Cranelift and GRIN (WASM support is planned as well, but not as the main target).
- support for modules, namespacing, imports, etc.
- pretty much everything else

## Overview

The syntax is heavily inspired by the ML-family, notably Haskell.
Whether the language is going to be strict or lazy is to be decided

```haskell
type List 'a = Cons 'a (List 'a) | Nil

map : ('a -> 'b) -> List 'a -> 'b
map f = match
    (L.st.Cons x xs) -> List.Cons (f x) (map f xs)
    List.Nil -> List.Nil
```

Right away, you may notice some differences. Compared to Haskell,
- type signatures use `:` instead of `::`.
- type variables are denoted with a quotation mark. This way, type names don't have to be uppercase, and value-level identifiers may be used at the type level with no ambiguity (the plan is to have dependent type-esque facilities at compile time, if not outright dependent types).
- functions may not have multiple bodies. Instead, there's a `match` expression that behaves the same as `\cases` in Haskell.
- types have their own namespaces, and constructors have to be qualified by default

### Type system

The type system is based on *Complete And Easy Bidirectional Typechecking for Higher-Rank Polymorphism* with some elements of Hindley-Milner.

It can infer anything that HM can, but for higher-rank types, explicit annotations are required.

#### First-class existentials

The language supports existential quantification as well as universal quantification. Type variables are treated as universally quantified by default, so existentials require an explicit `exists` clause.

```haskell
listOfSomething : exists 'a. List 'a
listOfSomething = ["'a", "is", "Text,", "actually"]
```
In simple cases like this, existentials don't make much sense - we could have just annotated `listOfSomething` with `List Text` instead!

One interesting use case is a more lightweight alternative for rank 2 types. For example, `runST` is typed like this in Haskell:

```haskell
runST :: (forall s. ST s a) -> a
```
Instead, we could write
```haskell
runST : exists s. ST s a -> a
```
This way, there are no impredicative instantiations going on when we write
```haskell
computation = runST <| do
    ...
```
and there's no need to special case `<|` [like GHC used to have](https://gitlab.haskell.org/ghc/ghc/blob/795986aaf33e2ffc233836b86a92a77366c91db2/compiler/typecheck/TcExpr.hs#L323-L334) with `$`

In general, wherever Haskell type checking failed with the funky message about a skolem escaping its scope, *language name* infers an existential instead.

Some other use cases:

```haskell
type Relativity = Abs | Rel
type Path ('a : Relativity) = ...

readSymlink : Path 'any -> IO (exists 'rel. Path 'rel)

-- todo: a concatenative DSL example
```

Existentials are good at types-that-cannot-be-named. Here's how the Haskell library justified-containers would look like
```haskell
type JMap 'ph 'k 'v
type Key 'ph 'k

justify : Map 'k 'v -> exists 'ph. JMap 'ph 'k 'v
fromJustified : JMap 'ph 'k 'v -> Map 'k 'v

member : 'k -> JMap 'ph 'k 'v -> Maybe (Key 'ph 'k)
lookup : Key 'ph 'k -> JMap 'ph 'k 'v -> 'v
update : ('v -> 'v) -> Key 'ph 'k -> JMap 'ph 'k 'v -> JMap 'ph 'k 'v

insert : 'k -> 'v -> JMap 'ph 'k 'v -> exists 'ph2. JMap 'ph2 'k 'v
delete : Key 'ph 'k -> JMap 'ph 'k 'v -> exists 'ph2. JMap 'ph2 'k 'v
```

The API is almost exactly the same, except that we don't need an ad-hoc continuation to introduce a scope, we can use the justified map directly

```haskell
example : List ('k, 'v) -> Map 'k 'v -> Map 'k 'v
example kvPairs map' = fromJustified <| foldr (uncurry insert) jmap matchingKeys where
    jmap = justify map
    matchingKeys = keys |> mapMaybe \(k, v) -> map (_, v) (lookup _ jmap)
```

*(currently unimplemented)*
There's a subtle quirk that makes this style possible - whenever a local binding with an outer `exists` quantifier is introduced, the existential is implicitly instantiated to a skolem. That way, multiple uses of that binding share the same type.

#### Row polymorphism

*TODO*. You may read *Extensible records with scoped labels* in the meantime.

### Wildcard lambdas

*name of the language* doesn't have operator sections (`(+3) :: Int -> Int`). Instead, there's a more general feature called wildcard lambdas (or something else if I come up with a better name).

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

Just like Haskell, *language* features user-defined operators

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
