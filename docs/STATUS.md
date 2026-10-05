# Compiler status

M0 now implements construction, checking, and JSON encoding for every family
in `core/schema.mech` and every `Type 0` family in `core/ops.mech`. It does
not complete the M0 milestone in `SPEC.md`.

## Implemented

- Lexer with byte positions, line comments, decimal literals, and escaped
  UTF-8 strings.
- Type and term parser for definitions, grouped expressions, every schema
  constructor, products, and sums.
- Universes `Type 0` and `Type 1`, type definitions, and the instance
  boundary for types. The output does not contain type definitions. Type
  formers refuse universe arguments.
- `first` and `second`. Their argument synthesizes its type: an earlier
  definition, a projection, or one of these in parentheses.
- Equality types `Eq A x y` with `refl`, `symm`, and `trans`. Sides are atoms
  of a data type A. The compiler compares them by their JSON encoding. An
  equality type is only the type of a definition, and proofs are not
  instances. `symm` and `trans` synthesize their types like `first`.
- First-order functions: function types `(x : A) -> B` over data types,
  `fun` with flat or curried binders, and saturated application. The
  definition checks the body once. Each application evaluates the body again
  with the argument values. A function body cannot apply a function.
  Functions are not instances.
- Reserved names for every SPEC form, also for forms of later slices.
- Type-directed checking with exact types on references to earlier
  definitions. Duplicate and implemented schema names are refused.
- Hash and indexed Ref construction. Ref indices accept Kind constants,
  earlier Kind definitions, and parentheses. The compiler normalizes aliases
  before comparing types, including inside containers and record fields.
- All schema enums, records, and variants, including the eight business
  record families, Account, Subject, Actor, Body, and Entry. Field names and
  order follow the schema. Mixed families use tagged objects even for their
  constructors with no fields.
- Constructor evaluation into the core Value/Values/Attrs families.
  Parsing, checking, and evaluation remain fused for this slice.
- JSON encoding with decimal numbers, escaped strings, Option presence for
  `Option` and `Value` payloads, ordered objects, and duplicate-key rejection.
- Structural recursion or explicit fuel throughout. Serialization charges one
  fuel step per emitted byte and threads the remaining fuel through all
  instances. Name and key comparisons stop at the first different byte.
- Wasm reactor build, byte transport, command-line launcher, values and CRM
  examples, and integration tests against the reactor and CLI.
- Monad `pure`, `map` and `bind` over `Option`, `List` and `Sum E`,
  Filterable `filter` over `Option` and `List`, and `either`. The function
  argument names a definition with one parameter.
- Algebra `fold` and `unfold` over `Nat`, `Text`, `List A`, `Values` and
  `Attrs`, and Filterable `filter` over `Text`, `Values` and `Attrs`. The
  source of `fold` synthesizes its type. `unfold` stops at `none` or at its
  `Nat` limit. An `Attrs` result refuses duplicate keys.
- Algebra `fold` and `unfold` over `Value`. `fold` takes five functions, one
  for each constructor after `valueNull`, then the result for `valueNull`.
  `unfold` takes one function that gives the layer of a seed. It applies
  that function at most `n` times in depth-first order, and a seed that is
  left becomes `valueNull`. A layer of fields refuses duplicate keys.
- Operation families of `core/ops.mech`: `Moment`, `Missing`, `Verdict`,
  `Command`, `Write`, `Outcome`, `Step`, `PipelineKey`, `Bucket`,
  `StageStat`, `Renewal` and `Account360`. Construction, checking and JSON
  encoding follow the schema rules. `Log` is an alias of `List Entry`, so
  the output shows `List (Entry)`. The compiler does not run the write path
  or the read path.
- `Query T` is the indexed `Query` family of `core/ops.mech` as a `Type 1`
  type. The compiler checks each of the 29 constructors against its answer
  type. A Query value is not an instance. A Query type is not an argument of
  a type former, a parameter type or a result type.

## Remaining M0 work

1. Add dependent function types, nested application, and inline or partial
   functions as arguments. These need an internal value domain with neutral
   terms and a threaded work budget. Then add Sigma checking and evaluation,
   `transport`, and `cong`, and allow `Eq` inside Sigma and Pi types.
2. Add `WritePath` and `ReadPath`. They are function types, so they need
   function types in type definitions. Until then the type parser refuses
   these two names with `this type belongs to a later milestone`.
3. Extend diagnostics with declaration context and improve source/output
   budgets as measurements justify changes.

## Known limits of this slice

- `map`, `bind`, `filter`, `fold` and `unfold` use one step of the depth
  fuel for each element. The depth fuel is one step per source byte, at most
  512 steps. Thus a long list made by `bind`, or a `fold` over a large `Nat`,
  can stop with a fuel error. Their function argument is a name, not a `fun`
  term or a partial application.
- Over `Value`, `fold` and `unfold` use one step of the depth fuel for each
  level and for each earlier child of the same list. The limit of `unfold`
  into `Value` counts applications, not elements or levels. A fold over
  `Value` needs all five functions. It cannot leave out a case.
- The source of `fold` must synthesize its type. A literal source such as
  `nil` or a string is refused. Name it in an earlier definition.

- Hash wraps a Text value. The compiler does not compute or validate digest
  strings, resolve references to log entries, or apply record projections.
  Schema comments about business rules, such as a person's Party kind or a
  confidence percentage, do not add constraints beyond the declared types.
- The compiler reserves all schema names and every form name of SPEC.md. It
  also reserves every family, constructor and definition name of
  `core/ops.mech`, including `Query` and its constructors. Field names are
  not reserved.
- Each constructor argument costs one parsing fuel step. The host requires a
  structurally recursive definition to examine its recursive argument at the
  start of its body, so the argument parser cannot skip this step. README.md
  gives the measured limits for the original scalar and container forms.
- A function keeps the tokens of its body, not a syntax tree. Each
  application parses and evaluates the body again. A body cannot apply a
  function, so the work of all applications is at most the number of
  application sites times the body size. The body check at the definition
  binds each parameter to null. Thus a constructor error that depends on a
  parameter is reported at the application.

M1 remains the write path, entry hashes, and record projection. M2 remains
the indexed read path. The core files and full specification retain their
original meaning.

## Internal boundaries

`runtime.mech` holds compiler data types and common operations. `lexer.mech`
turns Text into tokens. `schema.mech` describes schema constructors and fields;
`operations.mech` describes the operation families in the same form;
`types.mech` describes primitive and container forms. `parser.mech`,
`checker.mech`, and `evaluate.mech` check and evaluate terms. `json.mech`
serializes checked runtime values. `program.mech` compiles definitions and
produces the success or error document.

`test/schema.test.mjs` derives conformance cases from the original schema,
independently of compiler metadata. It checks every newly added constructor,
field name, field order, argument type, and arity, plus indexed references.
`test/operations.test.mjs` does the same from `core/ops.mech`.

Internal families such as Fuel, Token, LType, Result, Plan, and Binding cannot
be used as ledger types. The only exported runtime boundary is Text and its
byte accessors. Node contains no language parser, type checker, or evaluator
in the compiler or launcher.
