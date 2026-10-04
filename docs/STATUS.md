# Compiler status

M0 now implements construction, checking, and JSON encoding for every family
in `core/schema.mech`. It does not complete the M0 milestone in `SPEC.md`.

## Implemented

- Lexer with byte positions, line comments, decimal literals, and escaped
  UTF-8 strings.
- Type and term parser for definitions, grouped expressions, every schema
  constructor, products, and sums.
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

## Remaining M0 work

1. Add universe, function, Sigma, and Eq checking and evaluation. Enforce
   the instance boundary for types, functions, and proofs.
2. Add product and sum eliminators, Monad map/bind, Algebra fold/unfold,
   and Filterable filter with bounded evaluation.
3. Add operation-family construction and encoding from `core/ops.mech`.
4. Extend diagnostics with declaration context and improve source/output
   budgets as measurements justify changes.

## Known limits of this slice

- Hash wraps a Text value. The compiler does not compute or validate digest
  strings, resolve references to log entries, or apply record projections.
  Schema comments about business rules, such as a person's Party kind or a
  confidence percentage, do not add constraints beyond the declared types.
- The compiler does not yet reserve names of later SPEC forms (for example
  `Sigma`, `Eq`, `Type`, and `fun`) or operation families from `core/ops.mech`.
  Later M0 work reserves them. All implemented schema names are reserved now.
- Each constructor argument costs one parsing fuel step. The host requires a
  structurally recursive definition to examine its recursive argument at the
  start of its body, so the argument parser cannot skip this step. README.md
  gives the measured limits for the original scalar and container forms.

M1 remains the write path, entry hashes, and record projection. M2 remains
the indexed read path. The core files and full specification retain their
original meaning.

## Internal boundaries

`runtime.mech` holds compiler data types and common operations. `lexer.mech`
turns Text into tokens. `schema.mech` describes schema constructors and fields;
`types.mech` describes primitive and container forms. `parser.mech`,
`checker.mech`, and `evaluate.mech` check and evaluate terms. `json.mech`
serializes checked runtime values. `program.mech` compiles definitions and
produces the success or error document.

`test/schema.test.mjs` derives conformance cases from the original schema,
independently of compiler metadata. It checks every newly added constructor,
field name, field order, argument type, and arity, plus indexed references.

Internal families such as Fuel, Token, LType, Result, Plan, and Binding cannot
be used as ledger types. The only exported runtime boundary is Text and its
byte accessors. Node contains no language parser, type checker, or evaluator
in the compiler or launcher.
