# Validation

Date: 2026-10-04. Node: v23.10.0. Build host: the installed mechanism-lang
OCaml executable at `_build/default/bin/mech.exe`.

`make check test` passes in 8.0 seconds: the host checks the complete
compiler, builds the Wasm reactor, and runs 61 integration tests with zero
failures. Alone, `make check` takes 0.56 seconds and `make build` takes 1.23
seconds.

The tests cover the supported type and constructor forms, earlier definition
references, declaration and attribute order, Option presence for `Option`
and `Value` payloads, UTF-8 validation, string escaping, control and DEL
bytes, Nat boundaries, comment ends, parenthesized arguments, malformed and
forbidden input, and duplicate names and keys. They also exercise the
65,536-byte input boundary, parsing depth fuel, and the output budget per
emitted byte, also for shared values. Error tests check the reported byte
for invalid UTF-8, fuel exhaustion, and errors found during output. The
command-line tests run both `sh bin/ledgerc` and `node bin/ledgerc.mjs`.

In one run, the slowest tests were the command-line test (5.4 seconds),
long names and keys (2.1 seconds), and a 65,536-byte source in the reactor
(1.0 second). Long names and keys that share a long tail compile in linear
time.

The review inputs also ran through `bin/ledgerc`: 169 sources, including
65,536-byte shapes for long names, keys, strings, escapes, comments, and
shared values. Each gave the expected result or diagnostic. The slowest
took 2.5 seconds. Inputs whose output exceeds the budget stop with
`output budget exceeded` in 1.7 seconds or less.

The full design in `SPEC.md` is not implemented by this slice. See
[STATUS.md](STATUS.md) for remaining M0 work and [README.md](../README.md)
for supported syntax and resource limits.

The Bend 2 compiler passed an earlier host check, but its Wasm generation
reached a 600-second timeout. The installed OCaml compiler built a reactor
in 0.85 seconds. Both compiler checkouts were used without source edits.
