# ledger-lang

ledger-lang compiles business data definitions to one JSON document. The
language has a fixed core schema. Its compiler runs in mechanism-lang and
the Node launcher only transfers source and result bytes to a Wasm reactor.

This M0 slice supports construction of the complete core schema. See [SPEC.md](SPEC.md) for the full
design and [docs/STATUS.md](docs/STATUS.md) for the implementation boundary.

## Build and run

Use a mechanism-lang checkout with `_build/default/bin/mech.exe` already built and
a Node runtime supporting Wasm GC. The reactor is tested on Node v23.10.0.
The default host is the OCaml executable in the sibling `../mechanism-lang` checkout. Set
`MECH_BIN` to use another installed host executable.

Use the OCaml host for this slice. Current validation is recorded in
[docs/VALIDATION.md](docs/VALIDATION.md). The Bend 2 Wasm build reached a
ten-minute timeout during the initial probe.

```sh
make check
make test
bin/ledgerc examples/values.ledger > values.json
bin/ledgerc examples/crm.ledger > crm.json
bin/ledgerc examples/formers.ledger > formers.json
bin/ledgerc examples/equality.ledger > equality.json
```

`make test` builds `build/ledgerc.wasm` and runs the integration suite.
Rebuild with `make build` after editing compiler sources. Build artifacts
are ignored by Git. No package installation is needed.

## Supported programs

```text
def company : Text := "Acme"
def count : Nat := 42
def profile : Attrs :=
  attrsField "company" (valueText company)
    (attrsField "count" (valueNat count) attrsEnd)
def contacts : List Text := cons "Mira" (cons "Jo" nil)
def optional : Option (Option Text) := some none
def pairOfValues : Prod Text Nat := pair company count
```

The output contains every definition in declaration order. A definition can
refer to earlier definitions of the same type. Constructor arguments use
the expected type, so `nil` and `none` need no explicit type arguments.
Parentheses group types and terms. An argument that is itself a type former
or a constructor with arguments needs parentheses: write `Option (Option Text)`
and `cons "a" (cons "b" nil)`. `--` starts a comment that ends at a line feed
or a carriage return. A name or keyword cannot start directly after a number.

Implemented types are `Nat`, every family in `core/schema.mech`, `Prod A B`,
and `Sum A B`. This includes all business records, enums, and variants, plus
`Hash`, indexed `Ref k`, `Option A`, and `List A`. Constructors follow the
schema, plus `pair`, `inl`, and `inr` from the specification. `first` and `second`
project a product. Sums support construction only.

```text
def companyKind : Kind := kindParty
def companyRef : Ref companyKind := refTo (hashOf "company-entry")
def company : Party := makeParty partyOrg "Acme" none nil attrsEnd none none
def entry : Entry := makeEntry none (actorSystem "import") (createsParty company)
```

Ref indices accept Kind constants and earlier Kind definitions, including
parenthesized aliases. `Ref companyKind` normalizes to `Ref (kindParty)` in
the output type. References of different kinds cannot be interchanged,
including in record fields and nested containers. Ref JSON is
`{"kind":"kindParty","hash":"company-entry"}`.

Records encode as objects with schema field names in schema order. Enums
encode as constructor names. Other variants encode as objects with `tag`
followed by their fields, including fieldless variants of mixed families
such as `scopeAll` and `systemEmail`. `Hash` encodes as its digest Text;
M0 accepts that text as supplied. Hash computation, reference resolution,
and record projection are later work. See [examples/crm.ledger](examples/crm.ledger)
for a program constructing all eight business record families.

A type definition gives a name to a type. `Type 0` classifies the data types
and `Type 1` classifies `Type 0`. A type definition is not an instance, so
the output does not contain it. Type formers take only data types, thus
`Option (Type 0)` is an error.

```text
def Contact : Type 0 := Prod Text (Option Text)
def mira : Contact := pair "Mira" none
def miraName : Text := first mira
```

The argument of `first` or `second` is an earlier definition, a projection,
or one of these in parentheses. Its type must be a product. A literal or a
constructor has no type of its own, so it is not an argument of a projection.
See [examples/formers.ledger](examples/formers.ledger).

An equality type `Eq A x y` is the type of a definition. `A` is a data type
in atom form, and the sides `x` and `y` are atoms of type `A`. `refl` proves
`Eq A x x`: the compiler evaluates both sides and compares their JSON
encodings. `symm p` and `trans p q` synthesize their types from earlier
proofs, like `first`. Proofs are not instances, so the output omits them:

```
def price : Nat := 1200
def total : Nat := 1200
def same : Eq Nat price total := refl
def back : Eq Nat total price := symm same
```

In this slice, `Eq` cannot occur inside another type former or a type
definition. The checking budget of the definition limits the JSON size of
each side. See [examples/equality.ledger](examples/equality.ledger).

`Option` presence is preserved. `none` is `null`. When the payload type can
encode `null` (an `Option` or a `Value`), `some v` is `{"some":v}`. For other
payload types, `some v` is `v`. Thus `some none` at `Option (Option Text)` and
`some valueNull` at `Option Value` both give `{"some":null}`. Attribute keys
retain source order. Duplicate keys and duplicate definition names are errors.

On an error, `bin/ledgerc` prints `FILE: byte N: message` to stderr, exits
with status 1, and emits no partial JSON on stdout. Errors from the bridge or
the file system have no byte and print as `FILE: message`. An error found
while the output is written reports the first byte of that definition.

## Limits

- Nat literals range from 0 through 1,073,741,823, matching the probed host
  boundary. Leading zeroes are accepted and output uses ordinary decimal.
- Source size is at most 65,536 bytes. The bridge accepts source bytes and
  returns the decoded result string. The mechanism-lang compiler validates
  UTF-8 source and emitted Text. Invalid UTF-8 is reported at the first bad
  byte, or at the lead byte of a truncated sequence.
- Names use ASCII letters or `_`, followed by ASCII letters, digits, or `_`.
- String literals support UTF-8 and `\"`, `\\`, `\/`, `\n`, `\r`, `\t`, `\b`,
  and `\f`. A `\u` escape is currently refused. Raw control bytes 0 through 31
  and 127 (DEL) are refused. Other valid UTF-8 is accepted, including the C1
  controls U+0080 through U+009F.
- Parsing and checking fuel is one step per source byte, at most 512 steps
  on a path. Each definition has its own fuel. The measured limits for one
  definition are 511 nested parentheses, 256 nested `Option` type formers,
  127 nested `textByte` or `cons` terms, and 102 nested `attrsField` terms.
  Each count includes the innermost form. The error reports the token where
  the fuel ran out. Split a longer list or attribute object across
  definitions, for example
  `def rest : List Text := ...` and `def all : List Text := cons "a" rest`.
- Serialization shares a budget of 32 steps per source byte plus 128 steps
  across all instances. Each emitted byte costs one step. Thus the output is
  at most 32 bytes per source byte plus 128 bytes, also for shared values
  with a large expansion. When the budget runs out, the compiler reports
  `output budget exceeded`. The bridge also caps the result at 4 MiB.
- A 65,536-byte source needs more V8 stack than the Node default.
  `bin/ledgerc` runs Node with `--stack-size=7000 --max-old-space-size=1024`,
  and `node bin/ledgerc.mjs` starts Node again with these flags. A program
  that imports `bin/bridge.mjs` must start Node with the same flags.

See `core/ops.mech` for the planned write and read types. The current
reactor loads `core/schema.mech`; operations are preserved for later work.
