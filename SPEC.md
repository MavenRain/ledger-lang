# ledger-lang specification (draft)

Status: draft for milestone M0. `ledger-lang` is a working name.

## 1. Purpose

ledger-lang is a language for an append-only log of business records. Its
data types are fixed. A program constructs instances of these types. The
compiler checks the program and writes one JSON document: the final state of
all instances that the program constructs.

The compiler host is mechanism-lang. `core/schema.mech` and `core/ops.mech`
are the user's definitions, verbatim. They are the only core data types.

The compiler is one mechanism-lang program on `Text` byte lists: a lexer, a
parser, a checker, an evaluator and a JSON printer. A launcher only moves
bytes between files and that program.

## 2. Programs

A program is a sequence of definitions:

```
def NAME : TYPE := TERM
```

The compiler refuses `mu`, `axiom`, `def rec`, `poly` and `specialize` in a
program. Thus a program cannot add a data type, an unproved fact or general
recursion. Recursion comes only from `fold` and `unfold` (section 4).

## 3. Types

| Type former | Forms |
|---|---|
| Core types | Each family in `core/schema.mech` and `core/ops.mech`, and `Nat` |
| Product | `Prod A B`, `pair`, `first`, `second` |
| Coproduct | `Sum A B`, `inl`, `inr`, `either` |
| Universal quantification | `(x : A) -> B`, `fun (x : A) => t`, application |
| Existential quantification | `Sigma A B`, `pack`, `witness`, `payload` |
| Type equality | `Eq A x y`, `refl`, `transport`, `symm`, `trans`, `cong` |
| Universes | `Type 0`, `Type 1` |

`Type 0` classifies the data types and the function types of data types.
`Type 1` classifies `Type 0`. There is no cumulativity. `Option`, `List`,
`Prod` and `Sum` take data types only. `Query T` takes a data type `T` and
is in `Type 1`, so a definition of a Query type is not an instance.

`Eq A x y` takes a data type `A` and two terms of type `A`. Two sides are
equal when their values have the same JSON encoding. A proof has no runtime
content, so a definition of an `Eq` type is not an instance.

`(x : A) -> B` is the type of a function. A function has no JSON encoding, so
a function type is not a data type. An application `f a` checks `a` against
`A` and evaluates the body of `f` with `x` bound to the value of `a`.

A type definition can name a function type of data types:
`def Rule : Type 0 := (count : Nat) -> Flag`. The name stands for the
function type, also at the end of a longer function type. `WritePath` is
the function type `(log : Log) -> (write : Write) -> Step`.

A function type can start with type parameters: `(A : Type 0) -> (x : A) -> A`.
Each type parameter comes before the value parameters. The types of the
later parameters and the result type can use its name. A function type with
a type parameter is in `Type 1`. An application `f T a` gives one data type
`T` for each type parameter, then the value arguments. The checker replaces
all type parameters with the type arguments in one step. The type of a type
parameter is opaque in the body of the function, so the body is correct for
each type argument. A type that depends on a value parameter is later work.

## 4. Structures

- **Monad** gives `pure`, `map` and `bind`. M0 instances: `Option`, `List`,
  `Sum E`. M1 adds the write monad, a state monad on `Log`.
- **Algebra** gives `fold` and `unfold`. `fold` uses an algebra to consume a
  recursive core type. `unfold` uses a coalgebra and a `Nat` step limit to
  build one, because each program must terminate. Carriers: `Nat`, `Text`,
  `List A`, `Values`, `Attrs` and `Value`.
- **Filterable** gives `filter` with a predicate into `Flag`. Carriers:
  `Option`, `List`, `Text`, `Values`, `Attrs`.

Surface forms in M0. The declared type selects the instance: `pure x`,
`map f t`, `bind f t` and `filter f t` check against `Option B`, `List B` or
`Sum E B`. `filter` has no `Sum E` instance. `f` is the name of a definition
with one parameter. For `map`, `f : A -> B` and `t : F A`. For `bind`,
`f : A -> F B` and `t : F A`. For `filter`, `f : B -> Flag` and `t : F B`.
`either f g s` synthesizes `C` from `f : A -> C`, `g : B -> C` and
`s : Sum A B`. A function body can use `pure`, can apply an earlier
function, and can use `map`, `bind`, `filter` and `either`. The check of
the body at the definition checks the function and the source of a form.
It does not evaluate the form.

`fold f z t` checks against a declared type `C`. `z : C`, and `t`
synthesizes its carrier like the argument of `first`. Over `Nat`,
`f : C -> C`, and `fold` applies `f` to `z` as many times as `t`. Over
`List A`, `Text`, `Values` and `Attrs`, `f : E -> C -> C`, and `fold`
consumes the elements from the right. The elements are the bytes of `Text`
as `Nat`, the `Value` items of `Values`, and the fields of `Attrs` as
`Prod Text Value`. `unfold g n s` checks against a declared carrier. Into
`Nat`, `g : S -> Option S`, and the result is the number of steps. Into a
sequence of `E`, `g : S -> Option (Prod E S)`. `unfold` stops when `g` gives
`none` or after `n` elements. `filter` also checks against `Text`, `Values`
and `Attrs`, with `f : E -> Flag`.

Over `Value`, `fold` takes one function for each constructor after
`valueNull`: `fold fNat fFlag fText fItems fAttrs z t`. `fNat : Nat -> C`,
`fFlag : Flag -> C`, `fText : Text -> C`, `fItems : List C -> C` and
`fAttrs : List (Prod Text C) -> C`. `z` is the result for `valueNull`. `fold`
consumes the children of `valueItems` and `valueAttrs` first, and a field
result is the pair of its key and the folded value. Into `Value`,
`g : S -> Option (Sum Nat (Sum Flag (Sum Text (Sum (List S) (List (Prod Text S))))))`.
`none` gives `valueNull`. The other results give a number, a flag, a text,
the seeds of the items, or the keys and seeds of the fields. `unfold` applies
`g` at most `n` times, in depth-first order. A seed that is left becomes
`valueNull`.

## 5. Instances and the target

An instance is a top-level definition whose type is a data type. Definitions
of functions, of types and of equality proofs are not instances.

The target is one JSON document. Instances are in declaration order:

```json
{ "ledger-lang": 1,
  "instances": [ { "name": "acme", "type": "Party", "value": { } } ] }
```

Encoding rules:

| Type | JSON |
|---|---|
| `Nat` | number |
| `Text` | string (the bytes must be valid UTF-8) |
| `Flag` | `false` or `true` |
| `Option A` | `null` or the value; `{"some": v}` when `A` can encode `null` (an `Option` or `Value`) |
| `List A`, `Values` | array |
| `Attrs` | object, keys in source order; a repeated key is refused |
| `Value` | the JSON value that it represents |
| Family with only constants (for example `Kind`) | the constructor name as a string |
| Family with one constructor (for example `Party`) | object with the field names of the schema |
| Other families (for example `Body`) | object with `"tag"`: constructor name, and the fields |
| `Hash` | the digest string |
| `Ref k` | `{"kind": k, "hash": digest}` |
| `Prod A B` | `{"first": a, "second": b}` |
| `Sum A B` | `{"inl": a}` or `{"inr": b}` |
| `Sigma A B` | `{"witness": a, "payload": b}` |
| `Eq` proof in a field | `null` (proofs have no runtime content) |

## 6. Final state

- M0: the final state of an instance is its value after evaluation.
- M1: the write path. `write : WritePath` appends entries with sha256 entry
  hashes. Each record that an entry creates is an instance. Its final state
  is its projection at the end of the log, with the projected fields filled.
- M2: the read path. `read : ReadPath` answers each `Query` from the log.

## 7. Milestones

| Milestone | Content |
|---|---|
| M0 | Core types, type formers, structures, JSON target, driver, examples, tests |
| M1 | Write path, entry hashes, projection |
| M2 | Read path |
| M3 | Speed and a kernel-checked certificate for the output |
