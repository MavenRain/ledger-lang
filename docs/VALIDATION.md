# Validation

Date: 2026-10-05. Node: v23.10.0. Build host: the installed mechanism-lang
OCaml executable at `_build/default/bin/mech.exe`.

`make check test` passes: the host checks the complete compiler, builds the
Wasm reactor, and runs 312 integration tests with zero failures. The test
runner reported 1.5 seconds. In the isolated checkout the host was selected with
`MECH_BIN=/Users/oobi/Documents/mechanism-lang/_build/default/bin/mech.exe`.

The original 61 tests still cover scalar and container constructors, earlier
definition references, declaration and attribute order, Option presence for
`Option` and `Value` payloads, UTF-8, escaping, control and DEL bytes, Nat
boundaries, comments, parenthesized arguments, malformed and forbidden input,
and duplicate names and keys. They exercise the 65,536-byte source boundary,
parsing depth fuel, the byte output budget, and shared values. The fuel test
reads the measured limits from README.md and checks that each stated count
compiles and that one more form exhausts fuel. Error tests check source byte
positions. CLI tests run both `sh bin/ledgerc` and `node bin/ledgerc.mjs`.

The 95 schema tests add coverage for Hash, all eight Ref indices, and every
constructor of the remaining 28 schema families. Conformance cases read
`core/schema.mech`, independently of compiler metadata, and verify:

- All 87 record, enum, and variant constructors, including fieldless
  constructors in mixed families.
- Exact field names and order, nested values, argument types, and rejection
  of missing and extra arguments.
- Ref kind mismatches in record fields, including Option fields and Refs
  inside the List fields `Artifact.subjects` and `Party.identifiers`. The
  Artifact cases also check the exact error byte for mismatches in both the
  first and later list elements.
- Kind alias normalization, all pairs of different Ref kinds, and Ref types
  nested in Option, List, Prod, and Sum.
- Rejection of non-Kind, unknown, and forward indices; byte diagnostics and
  bounded deeply parenthesized indices.
- Reservation of implemented schema names, nominal record aliases, Hash's
  distinct type, nested Option presence, and invalid UTF-8 inside a record.
- `examples/crm.ledger` through the public CLI, covering all eight business
  record families and a nested Entry. The test compares all 18 instances,
  including field order, with literal expected JSON.

The 13 structure tests in `test/structures.test.mjs` cover `pure`, `map`,
`bind` and `filter` over `Option`, `List` and `Sum E`, `either`, nested
structure forms, the refusals for a type without the structure, a function
argument without exactly one parameter, mismatched function types, a bare
form as an argument, and the forms that apply a function in a function body.
The example `examples/structures.ledger` is compiled and its values compared.

The 23 algebra tests in `test/algebra.test.mjs` cover `fold` over `Nat`,
`List`, `Text`, `Values` and `Attrs`, including the right-to-left order and an
empty source. They cover `unfold` into `Nat`, `List`, `Text`, `Values` and
`Attrs`, the step limit, `none` from the coalgebra, and a non-byte element
into `Text`. `filter` over `Text`, `Values` and `Attrs` keeps or removes all
elements in order. Duplicate keys from `unfold` into `Attrs` are refused, also
when a `fold` consumes the result. Refusals are checked at their source
bytes: a type without the structure, the `Value` source, `fold` and `unfold`
in a function body or bare as an argument, a function argument that does not
name a function, function, initial value, limit and seed type mismatches, a
source that does not synthesize its type, and depth fuel exhaustion. The
example `examples/algebra.ledger` is compiled and its values compared.

The 23 function tests in `test/functions.test.mjs` cover flat and curried
binders, argument type checks, applications as arguments of projections,
constructors and other applications, closed applications as `Eq` sides,
constructor errors in a body reported at the application, and 13 rejected
forms at their source bytes. The example `examples/functions.ledger` is
compared with literal expected values. Regression cases reject empty `fun`
parameter groups and check that earlier signature and lambda parameters
shadow outer type aliases and Kind values in subsequent annotations. Valid
mixed currying and value shadowing remain covered.

Historical measurements for the initial slice included 169 review inputs
through the CLI and a Bend 2 Wasm generation timeout at 600 seconds. Those
external review inputs were not rerun for this slice. The committed source
and resource-boundary regression tests were rerun as part of the full gate.
Neither mechanism-lang compiler checkout was edited.

The operation slice adds `test/operations.test.mjs`. It reads
`core/ops.mech` and `core/schema.mech`, not the compiler metadata. For each
of the 48 constructors of the 12 `Type 0` operation families it checks the
field names, field order, argument types and arity, and it rejects a surplus
argument, a missing argument, a wrong argument type and a wrong `Ref` index.
More cases cover the `Log` alias, the later-milestone refusal of `Query`,
`WritePath` and `ReadPath`, the 93 reserved operation names, and the literal
output of `examples/operations.ledger`.

The full design in `SPEC.md` is not implemented. See [STATUS.md](STATUS.md)
for remaining M0 work and [README.md](../README.md) for supported syntax and
resource limits. Entry hashing and projection remain M1 work.
