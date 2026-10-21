# ledger-lang specification (draft)

Status: draft for milestone M0. `ledger-lang` is a working name.

## 1. Purpose

ledger-lang is a language for an append-only log of business records. Its
data types are fixed. A program constructs instances of these types. The
compiler checks the program and writes one JSON document: the final state of
all instances that the program constructs.

The compiler is a C program, `build/ledgerc`, built with TinyCC.
`core/schema.def` and `core/ops.def` hold the user's core definitions as
rows: families, constructors, fields and definitions, with types in mech
surface syntax. They are the only core data types.

The compiler works on `Text` byte lists: a lexer, a parser, a checker, an
evaluator and a JSON printer. `bin/ledgerc` only runs `build/ledgerc` on a
file.

`build/ledgerc --certificate` writes the certificate of the document: one
mechanism-lang module. Its last def claims that the render of the
instances is the JSON document and its newline. The mechanism-lang kernel
checks the module in a separate run (`make certificate-check`, README.md).

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
| Core types | Each family in `core/schema.def` and `core/ops.def`, and `Nat` |
| Product | `Prod A B`, `pair`, `first`, `second` |
| Coproduct | `Sum A B`, `inl`, `inr`, `either` |
| Universal quantification | `(x : A) -> B`, `fun (x : A) => t`, application |
| Existential quantification | `Sigma A B`, `pack`, `witness`, `payload` |
| Type equality | `Eq A x y`, `refl`, `transport`, `symm`, `trans`, `cong` |
| Universes | `Type 0`, `Type 1` |

`Type 0` classifies the data types and the function types of data types.
`Type 1` classifies `Type 0`. There is no cumulativity. `Option`, `List`,
`Prod` and `Sum` take data types only. `Query T` takes a data type `T` and
is in `Type 1`, so a definition of a Query type is not an instance. A function
type with a Query parameter or result is also in `Type 1`, including when
the Query type occurs inside the type of a function parameter.

`Eq A x y` takes a data type `A` and two terms of type `A`. Two sides are
equal when their values have the same JSON encoding. A proof has no runtime
content, so a definition of an `Eq` type is not an instance.

`transport (z : A) B e t` takes a proof `e : Eq A x y` and a term `t` of
type `B` with `x` for `z`. Its type is `B` with `y` for `z`, and its value
is the value of `t`. The motive `(z : A) B` has the binder form of
`Sigma (x : A) B`.

`(x : A) -> B` is the type of a function. A function has no JSON encoding, so
a function type is not a data type. An application `f a` checks `a` against
`A` and evaluates the body of `f` with `x` bound to the value of `a`.

A type definition can name a function type of data types:
`def Rule : Type 0 := (count : Nat) -> Flag`. The name stands for the
function type, also at the end of a longer function type. `WritePath` is
the function type `(log : Log) -> (write : Write) -> Step`. `ReadPath` is
the function type
`(answer : Type 0) -> (log : Log) -> (query : Query answer) -> answer`. It
has a type parameter, so it is in `Type 1`. `ReadPath` and `WritePath` are
reserved definition names.

A function type can start with type parameters: `(A : Type 0) -> (x : A) -> A`.
Each type parameter comes before the value parameters. Only a named function
type at the end of a longer function type brings its type parameter after
value parameters, as in `(head : Hash) -> ReadPath`. The types of the
later parameters and the result type can use its name. A function type with
a type parameter is in `Type 1`. Two function types that differ only in the
names of their type parameters are the same type. An application `f T a`
gives one data type `T` for each type parameter, then the value arguments.
In M0 a type argument after a value argument is not read: the checker reads
it as a term. The checker replaces
all type parameters with the type arguments in one step. The type of a type
parameter is opaque in the body of the function, so the body is correct for
each type argument. A data type that depends on a value parameter is later
work. A side of an equality result `Eq A x y` can be the name of a value
parameter of type `A`. The checker compares such a side only with itself
(step D1 of `docs/DEPENDENT-TYPES.md`).

A named function type without type parameters is also a parameter type:
`(f : Rule) -> (count : Nat) -> Prod Nat Nat`. Parentheses can group the
parameter type. An argument for the parameter names an earlier function or
another function parameter of the same type, or is a parenthesized partial
application `(g a1 ... ak)`. The bound arguments supply leading parameters;
the remaining parameters and result must match the expected function type.
Bound values are evaluated in the caller's scope. A bound function argument
is a name, optionally grouped, or another parenthesized partial application.
A partial application of a function with type parameters gives one data type
for each type parameter first, then the bound values. The type arguments
resolve in the scope of the application, so they can name the type
parameters of the caller. The function of `map`, `bind` and `filter` is a
name or a parenthesized partial application that binds all but the last
parameter. The function of `fold` and
`unfold` is a name or a parenthesized partial application whose written
arguments bind the leading parameters; the parameters that are left must fit
the form. Each of the five functions of a fold over `Value` is such a name or
partial application. The function of `map`, `bind` and `filter` can also be
an inline `fun` with one binder of a data type. Its body is checked against
the result type the form expects and keeps the scope of the form. The function
of `fold` and `unfold`, and each of the five functions of a fold over `Value`,
can also be an inline `fun` with one or more binders of data types; the form
gives its result type. A named or partially applied argument keeps the
scope of its function, so its body refers to the definitions before that
function and not to the parameters of the caller. A function argument can
also be an inline `fun` with one or more binders of data types. The binders
must match the parameters of the expected function type, and the body is
checked at the argument against the expected result type with each binder
bound to null. An inline argument keeps the scope of the application, so its
body refers to the definitions and parameters around the application.
A partial application can also bind a parameter of a function type with a
parenthesized inline `fun`. Its body is checked at the partial application
and keeps the scope of the partial application.
The body of the function can apply the parameter, pass it to another function, or give
it to `map`, `bind`, `filter`, `either`, `fold` and `unfold`.
A named function type with a type parameter, such as `ReadPath`, is also a
parameter type. The body applies the parameter with the type arguments
first. A function type with a type parameter that has no name is not a
parameter type.

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

M1 adds the key `records` after `instances`. The key is in the target only
when a `Log` instance, or a `Step` instance that `write` gives, holds a
`creates...` entry. A `Step` from `makeStep` makes no record. The key has one
object for each record, in the order of the first entry of each record:

```json
{ "ledger-lang": 1,
  "instances": [ ],
  "records": [ { "ref": "<64 hex digits>", "type": "Party", "value": { } } ] }
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
  hashes. The hash of an entry is the SHA-256 of its compact JSON. `write
  log x` gives a `Step`: `outcomeAppended`, `outcomeConflict` or
  `outcomeDenied`. Each `creates...` entry of a `Log` instance, or of the
  log of a `Step` instance that `write` gives, makes one record (a `Step`
  from `makeStep` makes no record). The identity of a record is
  the hash of its entry. Its first state is the value in the Body. A later
  `createsEvent` entry sets `lastEvent` on the Party or Commercial record
  whose identity is the hash of its `subject`. The final state of a record
  is its state at the end of the logs. The records are in the key `records`
  of the target (section 5).
- M2: the read path. `read : ReadPath` answers eighteen queries from the
  log: `queryReplay`, `queryTail` and `queryAuditByActor` from the
  entries, `queryCommercial` and `queryProjectionSound` from the records
  of the log, and the seven queries of M3 and the six queries of M4. Each
  other `Query` constructor gives the refusal "the read path does not
  answer this query". The compiler runs the read path.
- M3: the Commitment and the Membership queries of the read path.
  `queryTermsInForce`, `queryTermHistory`, `queryAmountReconciled` and
  `queryDiscountPct` come from the Commitment and Commercial records of
  the log. `queryMembersOf`, `queryEmployer` and `queryJobChanges` come
  from the Membership records of the log (docs/STATUS.md `## M3`).
- M4: the Rollups queries of the read path. `queryPipeline`,
  `queryStageStats` and `queryStaleDeals` come from the Commercial and
  Event records of the log. `queryRenewals` and `queryAccount360` come
  from the Commercial, Commitment, Party, Membership, Assignment, Artifact
  and Event records of the log. `queryReviewQueue` comes from the
  `provenance` field of the records of the log (docs/STATUS.md `## M4`).
- M5: the certificate of the final state. The module of
  `build/ledgerc --certificate` holds the instances, SHA-256 and the entry
  hashes, the write outcomes, the records and the `records` key of the
  target, and the eighteen queries of the read path. A `read` of another
  `Query` constructor keeps the refusal "the read path does not answer
  this query". A form that the certificate does not cover gives the
  refusal "the certificate does not cover SUBJECT yet" (README.md,
  docs/STATUS.md `## M5`).
- M6: the remaining queries of the read path. Part A answers
  `queryEvidence` (the artifact of the entry whose hash is the fact: an
  Event with `artifact = some a` gives `[a]`, an Artifact entry gives its
  own ref, each other case gives `nil`) and `queryArtifactIntact` (`flagYes`
  when the `sha256` of the Artifact record equals the digest, else `flagNo`)
  from the records, in the compiler and in the certificate. Part B answers
  `queryTimeline` (the refs of the Event records of the subject, in log
  order, as of the moment), `queryThread` (the root, then the Event records
  whose `parent` chain reaches the root, in log order) and
  `queryAuditByPolicy` (the Event records whose `policy` is `some policy`,
  in log order) in the same way. Part C answers `queryOwner` (`some` the
  assignee of the last current `roleOwner` Assignment record of the
  account, else `none`), `queryBook` (the distinct subjects of the current
  Assignment records of the assignee, in the order of their first record)
  and the pipeline keys `pipelineByOwner` and `pipelineByTerritory` (the
  owner of a Commercial record is the owner of `accountCommercial c`, else
  of `accountParty p`; no owner or no territory gives the empty key) in the
  same way. Part D1 answers `queryCan` (`verdictAllow` with the first active
  Policy record that applies to the subject and has a rule that allows the
  request, else `verdictDeny` with the first active applying Policy record,
  or with `none`) and `queryRedacted` (the attrs of the subject that an
  active applying Policy record lets the principal read) in the same way.
  Part D2 answers `queryDryRun` (the missing fields, commitment kinds and
  approval roles of each active applying Policy record whose `toStage` is
  the stage) and `querySimulatePolicy` (the Event entries whose verdict
  changes when the given Policy takes the place of the Policy records of
  its name) in the same way. Each `Query` constructor has an answer
  (docs/STATUS.md `## M6`).
- M7: the command bodies and the policy check of the write path. Part A
  checks each write with the policy check of `queryCan` over the records
  of the log: the principal is the actor of the Write, and the action and
  the subject come from the Command. An active applying Policy record that
  allows the request gives `outcomeAppended` with `policy = some p`. An
  active applying Policy record with no allowing rule gives `outcomeDenied
  (some p) nil`, and the log does not change. No active applying Policy
  record gives `outcomeAppended` with `policy = none`. `commandTransition c
  s` appends an `eventStageChanged` Event of `c` with the stages `before`
  and `after`, after the guard of `queryDryRun` for `c` and `s`, and the
  projection sets the `stage` of the Commercial record to `after`. Part B1
  gives `commandResolveParty` the Party find: the first Party record that
  is not deleted and has a matching Identifier is the result, and the log
  does not change. Part B1 also gives a Body to `commandAddIdentifier`,
  `commandVerifyIdentifier`, `commandEnrichParty`, `commandDeleteParty`
  and `commandRestoreParty`, and the projection applies their Events to
  the Party record. The certificate covers part A and part B1
  (docs/STATUS.md `## M7`).

## 7. Milestones

| Milestone | Content |
|---|---|
| M0 | Core types, type formers, structures, JSON target, driver, examples, tests |
| M1 | Write path, entry hashes, projection |
| M2 | Read path |
| M3 | Read path: the Commitment and the Membership queries |
| M4 | Read path: the Rollups queries |
| M5 | Speed and a kernel-checked certificate for the output |
| M6 | Read path: the remaining queries and the pipeline keys |
| M7 | Write path: the command bodies and the policy check |
