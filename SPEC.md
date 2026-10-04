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

## 4. Structures

- **Monad** gives `pure`, `map` and `bind`. M0 instances: `Option`, `List`,
  `Sum E`. M1 adds the write monad, a state monad on `Log`.
- **Algebra** gives `fold` and `unfold`. `fold` uses an algebra to consume a
  recursive core type. `unfold` uses a coalgebra and a `Nat` step limit to
  build one, because each program must terminate. Carriers: `Nat`, `Text`,
  `List A`, `Values`, `Attrs` and `Value`.
- **Filterable** gives `filter` with a predicate into `Flag`. Carriers:
  `Option`, `List`, `Text`, `Values`, `Attrs`.

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
| `Option A` | `null` or the value; `{"some": v}` when `A` is an `Option` |
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
