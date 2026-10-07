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
bin/ledgerc examples/functions.ledger > functions.json
bin/ledgerc examples/structures.ledger > structures.json
bin/ledgerc examples/algebra.ledger > algebra.json
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

A function definition has a type `(x : A) -> B`. A value parameter has a
data type or a named function type without type parameters. The result has
a data type, and `B` cannot refer to a value parameter. The term is
`fun (x : A) => t`. Write more parameters as `fun (a : A) (b : B) => t` or as
`fun (a : A) => fun (b : B) => t`. Each binder type must be equal to the
declared parameter type. The body can refer to the parameters and to earlier
definitions.

```text
def tag : (label : Text) -> (count : Nat) -> Prod Text Nat :=
  fun (label : Text) (count : Nat) => pair label count
def visits : Prod Text Nat := tag "acme" 3
def count : Nat := second (tag "beta" 7)
```

The compiler checks the body once, at the definition. An application `f a b`
supplies all arguments. Each argument is an atom, and the compiler checks it
against its parameter type. The application then evaluates the body again
with the argument values. An application synthesizes its result type. Thus,
in parentheses, it can be the argument of `first` or `second`, or a side of
`Eq`. Functions are not instances, so the output does not contain them.

In this slice, a function body can apply an earlier function or a function
parameter. A function argument names an earlier function or another
function parameter, with optional grouping parentheses. It can also be a
parenthesized partial application `(g a1 ... ak)`: the supplied arguments
bind the leading parameters, and the remaining parameters and result must
match the expected function type. Bound values are evaluated in the caller's
scope. A bound function argument can be a name, optionally grouped, a
parenthesized inline function, or another partial application, as in
`use (apply (pickK 6))`. Nested partial applications keep the caller's scope.
See [examples/bound-partial.ledger](examples/bound-partial.ledger). A partial
application of a function with type parameters gives the type arguments
first, as in `use (konst Nat 6)`. The type arguments can name the type
parameters of the caller. This applies in each position that takes a
partial application.
See [examples/poly-partial.ledger](examples/poly-partial.ledger).
The function of `map`, `bind` and `filter` can also be a
parenthesized partial application that binds all but the last parameter, as
in `map (pick 1) xs`. See [examples/form-partial.ledger](examples/form-partial.ledger).
The function of `fold` and `unfold` can also be a parenthesized partial
application: the written arguments bind the leading parameters, and the
parameters that are left must fit the form, as in `fold (pick3 9) 0 xs`.
See [examples/fold-partial.ledger](examples/fold-partial.ledger).
The five functions of a fold over `Value` can also be partial applications,
as in `fold (pickK 7) onFlag onText onItems onAttrs 0 v`.
See [examples/value-fold-partial.ledger](examples/value-fold-partial.ledger).
`map`, `bind` and `filter` also take an inline function with one binder,
as in `map (fun (x : Nat) => cons x nil) xs`. The body sees the definitions
and parameters around the form. See [examples/inline-fun.ledger](examples/inline-fun.ledger).
`fold` and `unfold`, and each of the five functions of a fold over `Value`,
take an inline function with one or more binders, as in
`fold (fun (x : Nat) (acc : List Nat) => cons x acc) nil xs`. The binders
give the parameter types and the form gives the result type.
See [examples/inline-step.ledger](examples/inline-step.ledger).
A function argument can also be an inline function, as in
`apply (fun (x : Nat) => x) 5`. The binders must match the parameters of the
expected function type. The body sees the definitions and parameters around
the application. See [examples/inline-argument.ledger](examples/inline-argument.ledger).
A partial application can bind an inline function, as in
`use (apply (fun (x : Nat) => x))` or `map (apply (fun (x : Nat) => 2)) xs`.
The body sees the definitions and parameters around the partial application.
See [examples/inline-bound.ledger](examples/inline-bound.ledger).
For example:

```text
def Rule : Type 0 := (n : Nat) -> Nat
def pick : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => a
def apply : (f : Rule) -> (n : Nat) -> Nat := fun (f : Rule) (n : Nat) => f n
def result : Nat := apply (pick 42) 7
```

Here `result` is `42`. A function body can
use `map`, `bind`, `filter`, `either`, `fold` and `unfold`. A
function that a form applies evaluates in the scope of its definition, so a
parameter of the caller cannot replace a name in that function. The body
check at the definition does not know the argument values, so it checks an
application in the body only by type. Thus a constructor
error in the body, such as `textByte n textEnd` with `n` above 255, is
reported at its byte in the body when an application supplies that value.
Each application parses the body again with the fuel that remains at the
application site. A body evaluates in the scope of its definition. Thus a
name in the body refers to the definition before the function, also when a
caller has a parameter with the same name. Each evaluated body uses one unit
of the work budget. See [examples/functions.ledger](examples/functions.ledger),
[examples/nested.ledger](examples/nested.ledger) and
[examples/bodies.ledger](examples/bodies.ledger).

A function can have type parameters. A type parameter `(A : Type 0)` comes
before each value parameter. The types of the later parameters and the
result type can use its name. An application gives one data type for each
type parameter in the position of an argument, as in `id Nat 4` or
`id (Prod Nat Nat) p`. In the body, the type of a type parameter is opaque:
no constructor makes a term of it. A binder can give a new name to a type
parameter. A type definition of a function type with a type parameter is in
`Type 1`. See [examples/poly.ledger](examples/poly.ledger).

A type definition can name a function type without type parameters in
`Type 0`. The name then stands for the function type: as the type of a
function definition, as the body of another type definition, at the end of
a longer function type, and as a parameter type. Parentheses can group a
parameter type, as in `(f : (Rule))`. A function parameter keeps the scope
of its argument and can be passed to `map`, `bind`, `filter`, `either`,
`fold` and `unfold`. A function type is not a data type, so its name is not
an argument of a type former or a type argument of a polymorphic function.
See [examples/higher.ledger](examples/higher.ledger).

```
def Rule : Type 0 := (count : Nat) -> Prod Nat Nat
def Tagged : Type 0 := (label : Text) -> Rule
def twin : Rule := fun (count : Nat) => pair count count
def keep : Tagged := fun (label : Text) (count : Nat) => pair count 0
def applyRule : (f : Rule) -> (count : Nat) -> Prod Nat Nat :=
  fun (f : Rule) (count : Nat) => f count
def paired : Prod Nat Nat := applyRule twin 3
```

The structure forms `pure x`, `map f t`, `bind f t` and `filter f t` check
against a declared `Option B`, `List B` or `Sum E B`. `filter` has no `Sum E`
form. The argument `f` is the name of a function with one parameter: `map`
needs `A -> B`, `bind` needs `A -> F B`, and `filter` needs `B -> Flag`.
`map` and `bind` apply `f` to the payload of `some` and `inr` and to each list
item. The values `none` and `inl e` stay as they are. `filter` keeps the
payloads for which `f` gives `flagYes`. `either f g s` applies `f` to the
payload of `inl` and `g` to the payload of `inr`, and its type is the result
type of `f` and `g`. A function body can use `pure` and the
other forms. Each list item uses one step of the depth fuel. See
[examples/structures.ledger](examples/structures.ledger).

The algebra forms `fold f z t` and `unfold g n s` check against a declared
type `C`. For `fold`, `z : C`, and the source `t` synthesizes its type like
the argument of `first`: an earlier definition, a projection, or one of these
in parentheses. Thus `fold f z nil` is refused. Over `Nat`, `f : C -> C` is
applied `t` times. Over `List A`, `Text`, `Values` and `Attrs`,
`f : E -> C -> C` consumes the elements from the right. The elements of
`Text` are its bytes as `Nat`, and the fields of `Attrs` are `Prod Text Value`
pairs. For `unfold`, the declared type selects the carrier. Into `Nat`,
`g : S -> Option S` and the result is the number of steps. Into a sequence of
`E`, `g : S -> Option (Prod E S)`. `unfold` stops at `none` or after `n`
elements. An element above 255 into `Text` and a duplicate key into `Attrs`
are errors at `unfold`. `filter f t` also checks against `Text`, `Values` and
`Attrs`, with `f : E -> Flag`, and keeps the order of the elements. A
function body can use `fold` and `unfold`. Each element uses one step of
the depth fuel, so a short program can fold or unfold only a short sequence.

`Value` is a carrier too. A fold over a `Value` takes five functions before
`z`: `fold fNat fFlag fText fItems fAttrs z t`. The source `t` synthesizes
the type `Value`. For the declared type `C`, `fNat : Nat -> C`,
`fFlag : Flag -> C`, `fText : Text -> C`, `fItems : List C -> C` and
`fAttrs : List (Prod Text C) -> C`. `valueNull` gives `z`. A scalar gives its
payload to its function. `valueItems` and `valueAttrs` fold each child first,
from the left, and then give the list of the results to their function. The
result of a field is the pair of its key and the folded value. One function
with a `Value` source, or five functions with another source, stops the
compiler with `the number of functions does not fit the source of this fold`.
Each of the five functions is a name or a parenthesized partial application
whose written arguments bind the leading parameters. A parenthesized second
term is `fFlag` when the parameter it leaves is a `Flag`; otherwise it is `z`.

`unfold g n s` checks against `Value` when `g` gives the layer of a seed of
type `S`:

```text
g : (s : S) -> Option (Sum Nat (Sum Flag (Sum Text (Sum (List S) (List (Prod Text S))))))
```

`none` gives `valueNull`. The other results give a number, a flag, a text,
the seeds of the items, or the keys and seeds of the fields. `unfold` applies
`g` to the seeds in depth-first order, at most `n` times. A seed that is left
after `n` applications becomes `valueNull`. A duplicate key is an error at
`unfold`. Each level and each earlier child of the same list uses one step of
the depth fuel. See [examples/algebra.ledger](examples/algebra.ledger).

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
  These limits use only required parentheses. For example, the innermost
  Option is `Option Nat`; writing `Option (Nat)` costs another fuel step.
  Each count includes the innermost form. The error reports the token where
  the fuel ran out. Split a longer list or attribute object across
  definitions, for example
  `def rest : List Text := ...` and `def all : List Text := cons "a" rest`.
- Function evaluation shares a work budget of 8 bodies per source byte plus
  64 bodies across all definitions. Each application evaluates one body. This
  includes an application in another body, each application that a structure
  form, `fold` or `unfold` makes, and an application in a side of an `Eq`
  type. When the budget runs out, the compiler reports
  `work budget exceeded` at the body that the budget cannot pay for. Thus a
  chain of functions that each apply the previous function twice cannot make
  the compiler do exponential work.
- Serialization shares a budget of 32 steps per source byte plus 128 steps
  across all instances. Each emitted byte costs one step. Thus the output is
  at most 32 bytes per source byte plus 128 bytes, also for shared values
  with a large expansion. When the budget runs out, the compiler reports
  `output budget exceeded`. The bridge also caps the result at 4 MiB.
- A 65,536-byte source needs more V8 stack than the Node default.
  `bin/ledgerc` runs Node with `--stack-size=7000 --max-old-space-size=1024`,
  and `node bin/ledgerc.mjs` starts Node again with these flags. A program
  that imports `bin/bridge.mjs` must start Node with the same flags.

## Operation families

The compiler constructs, checks and encodes the `Type 0` families of
`core/ops.mech`: `Moment`, `Missing`, `Verdict`, `Command`, `Write`,
`Outcome`, `Step`, `PipelineKey`, `Bucket`, `StageStat`, `Renewal` and
`Account360`. The encoding rules are the schema rules. `Log` is an alias of
`List Entry`. See `examples/operations.ledger`.

```
def now : Moment := momentNow
def key : PipelineKey := pipelineByStage
def history : Log := nil
```

`now` encodes as `{"tag":"momentNow"}`, `key` as `"pipelineByStage"`, and
`history` as `[]` with the type `List (Entry)`.

`Query T` is a `Type 1` type that takes one data type `T`, the answer type.
A Query constructor checks only against the Query type of its answer type.
Another answer type stops the compiler with
`this constructor gives a Query of another answer type`. A definition of a
Query type is not an instance. A Query type is not an argument of a type
former, a parameter type or a result type.

```
def isReconciled : Query Flag := queryAmountReconciled deal
```

`WritePath` is the function type `(log : Log) -> (write : Write) -> Step`.
A function definition can have this type, a type definition can name it,
and a longer function type can end with it. See
[examples/paths.ledger](examples/paths.ledger).

```
def refuse : WritePath :=
  fun (log : Log) (write : Write) => makeStep log (outcomeDenied none nil)
```

`ReadPath` is a reserved name. It has a type parameter, so it needs
dependent function types. As a type, it stops the compiler with
`this type belongs to a later milestone`. The compiler does not run the
write path or the read path. The reactor loads `core/schema.mech` only. `compiler/operations.mech` holds the constructor
and field data of `core/ops.mech`.
