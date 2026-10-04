# Compiler status

The first M0 slice implements a complete path from source bytes to checked,
evaluated JSON. It does not complete the M0 milestone in `SPEC.md`.

## Implemented

- Lexer with byte positions, line comments, decimal literals, and escaped
  UTF-8 strings.
- Type and term parser for definitions, grouped expressions, scalar and
  container constructors, products, sums, and Kind enum constants.
- Type-directed checking with exact types on references to earlier
  definitions. Duplicate and reserved names are refused.
- Constructor evaluation into the core Value/Values/Attrs families.
  Parsing, checking, and evaluation are fused for this slice.
- JSON encoding with decimal numbers, escaped strings, Option presence for
  `Option` and `Value` payloads, ordered objects, and duplicate-key rejection.
- Structural recursion or explicit fuel throughout. Serialization charges one
  fuel step per emitted byte and threads the remaining fuel through all
  instances. Name and key comparisons stop at the first different byte.
- Wasm reactor build, byte transport, command-line launcher, an example,
  and integration tests against the reactor and CLI.

## Remaining M0 work

1. Add Hash, indexed Ref, and all remaining schema records and variants.
   Validate dependent constructor indices before encoding record fields.
2. Add universe, function, Sigma, and Eq checking and evaluation. Enforce
   the instance boundary for types, functions, and proofs.
3. Add product and sum eliminators, Monad map/bind, Algebra fold/unfold,
   and Filterable filter with bounded evaluation.
4. Add operation-family construction and encoding from `core/ops.mech`.
5. Extend diagnostics with declaration context and improve source/output
   budgets as measurements justify changes.

## Known limits of this slice

- The compiler does not yet reserve the names of later SPEC forms (for
  example `Sigma`, `Eq`, `Type`, and `fun`) or of schema families and
  constructors that it does not implement (for example `Party` and
  `hashOf`). A program can use these names for definitions now. Later M0
  work reserves them, and such programs will then be refused.
- Each constructor argument costs one parsing fuel step. The host requires a
  structurally recursive definition to examine its recursive argument at the
  start of its body, so the argument parser cannot skip this step. The
  nesting limits are therefore lower than 512. README.md gives the measured
  limits.

M1 remains the write path, entry hashes, and record projection. M2 remains
the indexed read path. The core files and full specification retain their
original meaning.

## Internal boundaries

`runtime.mech` holds compiler data types and common operations. `lexer.mech`
turns Text into tokens. `types.mech` describes supported type and constructor
forms. `parser.mech`, `checker.mech`, and `evaluate.mech` check and evaluate
terms. `json.mech` serializes checked runtime values. `program.mech` compiles
definitions and produces the success or error document.

Internal families such as Fuel, Token, LType, Result, and Binding cannot be
used as ledger types. The only exported runtime boundary is Text and
its byte accessors. Node contains no language parser, type checker, or
evaluator.
