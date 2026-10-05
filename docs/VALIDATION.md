# Validation

Date: 2026-10-04. Node: v23.10.0. Build host: the installed mechanism-lang
OCaml executable at `_build/default/bin/mech.exe`.

`make check test` passes: the host checks the complete compiler, builds the
Wasm reactor, and runs 156 integration tests with zero failures. The current
gate took 15.2 seconds; the test runner reported 11.7 seconds. In the
isolated checkout the host was selected with
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

Historical measurements for the initial slice included 169 review inputs
through the CLI and a Bend 2 Wasm generation timeout at 600 seconds. Those
external review inputs were not rerun for this slice. The committed source
and resource-boundary regression tests were rerun as part of the full gate.
Neither mechanism-lang compiler checkout was edited.

The full design in `SPEC.md` is not implemented. See [STATUS.md](STATUS.md)
for remaining M0 work and [README.md](../README.md) for supported syntax and
resource limits. Entry hashing and projection remain M1 work.
