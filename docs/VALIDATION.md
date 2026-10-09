# Validation

Date: 2026-10-08. Node: v23.10.0. Build host: TinyCC (`tcc`).
`build/ledgerc` is the only compiler.

`make check` and `make test` pass: `tcc -Wall -Werror` compiles each C
source, `make test` links `build/ledgerc` and runs 516 integration tests
with zero failures, and `make c-test` passes the C module and output tests.
The C compiler gives the same output as the earlier mechanism-lang
compiler, which is kept outside this repository, on 3139 of 3139 programs:
859 and 241 port cases, the 22 examples and 2017 corpus programs. Nineteen of the tests, in
`test/dependent.test.mjs`, check steps D1, D2, D2b, D4a, D4b and D4c of `docs/DEPENDENT-TYPES.md`: an
equality result can name a value parameter on both sides, two different
parameters or a parameter and a constant are not equal, a side names a
parameter of the side type, and step D2 instantiates the
sides at an application: `f 3` proves `Eq Nat 3 3`, a body can apply a proof
function to its own parameters, and a different parameter, a different
constant or a parenthesized argument is refused. Step D2b: a proof
parameter can name earlier parameters, `symm e` and `trans e d` check in a
body, and an application refuses a proof with the wrong sides. Step D4a: a
computed side such as `(some n)` checks with `refl`, `f 3` proves
`Eq (Option Nat) (some 3) (some 3)` and a body can pass its own parameter.
A different value, a different parameter, a literal in a body, a type
parameter and the name of an earlier function are refused. Step D4b: a
proof parameter with a computed side checks `symm e` in a body,
`lift 3 3 refl` proves `Eq (Option Nat) (some 3) (some 3)`, and a wrong
proof, a literal in a body and a bound function parameter are refused. Step
D4c: in a body, `f 3` and `f three` prove `Eq (Option Nat) (some 3) (some 3)`,
`pf m 1` proves `Eq (Prod Nat Nat) (pair m 1) (pair m 1)`, and a wrong
literal, a name in a side that keeps a marker and a parenthesized argument
are refused. The review
regressions cover prefixed named signatures, including proof parameters
through repeated prefixes and type parameters while preserving nested function
scopes. Inline bodies refuse captures of proofs with neutral sides from an
outer parameter scope, while closed proof captures still check and run.
The regressions also cover neutral references from different function scopes, proof composition,
`either`, partial applications, and preservation of whole-function references
and closed equality applications.

The partial application review adds eight cases in `test/partial.test.mjs`.
They check leading data arguments, grouped and computed arguments, lexical
scope under caller shadowing, bound function names, partial application of
function parameters, forwarding, and use through `map`. Refusals cover
missing, extra and mistyped arguments, and incompatible remaining
signatures. The existing
higher-order test keeps all five rejection cases and checks the parentheses
diagnostic for a compatible function with an unbound prefix.

The form partial application review adds five cases in
`test/form-partial.test.mjs`. They check `map`, `bind` and `filter` over a
partial application with literal, computed, caller-scope and function-name
bound arguments, grouped and one-parameter functions, partial application of
a function parameter, and the example file. Refusals cover mistyped,
missing and extra bound arguments, data names and the unchanged bare form.

The fold partial application review adds five cases in
`test/fold-partial.test.mjs`. They check `fold` over a partial application
with literal, computed, list, caller-scope and function-name bound arguments,
grouped and two-parameter functions, partial application of a function
parameter, two bound arguments, a `Nat` source, and the example file.
Refusals cover mistyped, extra and fully bound arguments, data names, a
number in parentheses for `unfold`, the bare form,
and unclosed or empty parentheses.

The Value fold partial application review adds six cases in
`test/value-fold-partial.test.mjs`. They check a fold over `Value` whose
functions are partial applications in each of the five positions and in all
five at once, grouped and two-parameter functions, a computed bound argument,
caller-scope and captured-scope bound arguments, partial application of a
function parameter, parenthesized initial values still selecting the fold
over a sequence, and the example file. A work-budget regression verifies
that a computed argument to the first function is evaluated once and that
multiple computed arguments still share the same budget. Refusals cover a mistyped bound
argument, partial applications that do not fit their position, a data
name, a fully bound function, and an unclosed parenthesis.

The inline function review adds five cases in `test/inline-fun.test.mjs`.
They check `map`, `bind` and `filter` over an inline `fun` with one binder,
over a list and an option, a body that applies an earlier function and a
parameter of the enclosing function, a binder that shadows a definition, a
grouped inline function, a nested inline function, a definition whose body
is only checked, and the example file. Refusals cover a reserved binder
name, a missing `=>`, two binders, a mistyped body, a binder that does not
fit the source, a filter body that is not a `Flag`, a bare `fun` without
parentheses, a universe binder, an arrow binder, an unclosed parenthesis, an
inline function with one binder given to `fold`, and an unknown name in the
body.

The inline fold review adds seven cases in `test/inline-step.test.mjs`.
They check `fold` over a list and over `Nat`, `unfold` into a list and into
`Value`, and each of the five functions of a fold over `Value`, with inline
functions that are grouped, nested, use a parameter of the enclosing
function or shadow a definition, and the example file. Refusals cover
binders that do not fit the source, a mistyped body, a reserved binder name,
a universe binder, a missing `=>`, an `unfold` body that does not give the
seed type, an unclosed parenthesis, and an unknown name in the body.
Regressions reject repeated binder names, including on an empty source,
and outer type aliases or `Kind` indices shadowed by an earlier binder.
A binder can use an outer alias in its own annotation, and its scope does
not leak into later definitions.

The inline argument review adds five cases in
`test/inline-argument.test.mjs`. They check inline functions with one and
two binders as function arguments, grouped and nested inline arguments, a
body that uses a parameter of the enclosing function, an earlier
definition, a function parameter or a structure form, a shadowed
definition, and the example file. Refusals cover a bare `fun` argument,
binders that do not match the expected function type, a `fun` term where a
data type is expected, a partial application bound by a partial application,
a mistyped body, a missing `=>`, a reserved binder name, an unknown name in
the body, an unclosed parenthesis, and a mistyped body in a function that
is not applied.

The inline bound argument review adds five cases in
`test/inline-bound.test.mjs`. They check a partial application that binds an
inline function as a function argument, with a grouped inline function, at a
later parameter, as the function of `map`, and as the function of `fold`.
They check a body that uses a parameter of the enclosing function, a
function parameter, a partial application in a structure form of a function
body, a shadowed definition, and the example file. Refusals cover binders
that do not match the parameter type, a bare `fun`, a mistyped body, an
unknown name in the body, and a partial application bound by a partial
application.

The partial application with type parameters review adds nine cases in
`test/poly-partial.test.mjs`. They check function arguments that give the
type arguments with and without bound values, a closure body that uses the
type arguments, type and bound arguments that name the parameters of the
caller, nested partial applications, `map` and `fold`, `unfold` into a list,
`Text` and `Nat`, `unfold` into `Value`, the five functions of a fold over
`Value` with two type parameters each, a partial application with type
parameters that binds another one, also in a function with type parameters,
and the example file. Refusals cover a wrong or missing type argument, a
mistyped bound value, a bare function with type parameters, and partial
applications that do not fit `map`, `unfold`, a fold over `Value` or a bound
parameter.

The original 61 tests still cover scalar and container constructors, earlier
definition references, declaration and attribute order, Option presence for
`Option` and `Value` payloads, UTF-8, escaping, control and DEL bytes, Nat
boundaries, comments, parenthesized arguments, malformed and forbidden input,
and duplicate names and keys. They exercise the 65,536-byte source boundary,
parsing depth fuel, the byte output budget, and shared values. The fuel test
reads the measured limits from README.md and checks that each stated count
compiles and that one more form exhausts fuel. Error tests check source byte
positions. CLI tests run `sh bin/ledgerc`.

The 95 schema tests add coverage for Hash, all eight Ref indices, and every
constructor of the remaining 28 schema families. Conformance cases read
`core/schema.def`, independently of compiler metadata, and verify:

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

Of the 42 algebra tests in `test/algebra.test.mjs`, 23 cover `fold` over `Nat`,
`List`, `Text`, `Values` and `Attrs`, including the right-to-left order and an
empty source. They cover `unfold` into `Nat`, `List`, `Text`, `Values` and
`Attrs`, the step limit, `none` from the coalgebra, and a non-byte element
into `Text`. `filter` over `Text`, `Values` and `Attrs` keeps or removes all
elements in order. Duplicate keys from `unfold` into `Attrs` are refused, also
when a `fold` consumes the result. Refusals are checked at their source
bytes: a type without the structure, a `Value` source with one function,
`fold` and `unfold` in a function body or bare as an argument, a function
argument that does not name a function, function, initial value, limit and
seed type mismatches, a source that does not synthesize its type, and depth
fuel exhaustion. The example `examples/algebra.ledger` is compiled and its
values compared.

The other 19 algebra tests cover the `Value` carrier. A fold over `Value`
selects the case of each of the six constructors, gives each scalar payload
to its function, and folds the children of items and of fields before their
parent. An unfold into `Value` builds each scalar layer, gives `valueNull`
for `none` and for a seed that is left after the limit, applies the coalgebra
in depth-first order, and keeps the field order. A `fold` consumes a `Value`
that an `unfold` built. Refusals are checked at their source bytes: each of
the five functions and the initial value with a wrong type, five functions
with a source that is not a `Value`, two functions, six functions, a source
that does not synthesize its type, both forms in a function body, a bare
fold as an argument, a coalgebra with a wrong type, limit and seed type
mismatches, and a duplicate key from a layer of fields. Depth fuel
exhaustion gives its message. No mutation run was made for this slice.

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
`core/ops.def` and `core/schema.def`, not the compiler metadata. For each
of the 48 constructors of the 12 `Type 0` operation families it checks the
field names, field order, argument types and arity, and it rejects a surplus
argument, a missing argument, a wrong argument type and a wrong `Ref` index.
More cases cover the `Log` alias, the later-milestone refusal of
`ReadPath`, the 93 reserved operation names, and the literal output of
`examples/operations.ledger`.

The Query slice adds one case for each of the 29 `Query` constructors. Each
case checks the answer type, the argument types and the arity, and it checks
that the value is not an instance. One more case covers the universe of a
Query type and its refusal as an argument of a type former, a parameter type
and a result type.

The function type slice adds `test/paths.test.mjs` with 20 cases. They cover
a type definition of a function type, the name as the type of a function
definition, in another type definition and at the end of a longer function
type, the `Type 0` universe, the refusal as a data type and as a term,
`WritePath` in each of these positions, the refusal of `ReadPath`, and the
literal steps of `examples/paths.ledger`. Additional cases cover grouping
of function type names and complete arrow types, the 511-parenthesis
boundary, parameter shadowing, universe and data type restrictions, and
missing closing parentheses. This slice has no mutation run.

The nested application slice adds `test/nested.test.mjs` with 10 cases. They
cover an application in a function body, a structure form that applies such
a function, the scope of a body, the type check of an application in a body,
a constructor error in a nested body, and `examples/nested.ledger`. The work
budget cases cover the exact boundary (a program that evaluates 8,192 bodies
passes in 1,016 source bytes and is refused in 1,015 bytes), the shared
budget across definitions, a doubling chain of 41 functions, and the sides
of an `Eq` type. The slice removes the old refusal case from
`test/functions.test.mjs`. This slice has no mutation run.

The in-body forms slice adds `test/bodies.test.mjs` with 4 cases. They
cover `map`, `bind`, `either` and `fold` in a function body, a form that
applies a function with a form in its body, the scope of a function that a
form applies, the check of a form at the definition, and the work budget
for forms in function bodies. Six earlier rows in
`test/structures.test.mjs` and `test/algebra.test.mjs` asserted the refusal
of a form in a function body. These rows now assert that the program
compiles. The earlier paragraphs that name this refusal describe the rows
before this slice. The full suite has 394 tests. This slice has no example
file and no mutation run.

The coverage slice for in-body forms adds 6 cases to
`test/bodies.test.mjs` and adds `examples/bodies.ledger`. The cases use
literal values. They cover `bind`, `filter` and `map` over `Option`,
`Sum E` and `Text` in a function body, `fold` over `Nat`, `Text` and
`List A`, `fold` and `unfold` over `Value`, the scope of a function that
`unfold` applies, a source of the wrong type in a body for each form, and
the example. The slice changes no compiler file. The full suite has 400
tests. This slice has no mutation run.

The full design in `SPEC.md` is not implemented. See [STATUS.md](STATUS.md)
for remaining M0 work and [README.md](../README.md) for supported syntax and
resource limits. Entry hashing and projection remain M1 work.

The type parameter slice adds `test/poly.test.mjs` with 20 cases and
`examples/poly.ledger`. The positive cases apply a polymorphic function at
`Nat` and at a product type, apply polymorphic functions in the body of
another polymorphic function, give the type parameters to a second function
in the other order, and give a new name to a type parameter in a binder. The
case with the other order fails for a substitution that replaces one name
after the other. Thirteen cases refuse a program at its byte: a result or an
argument of another type, a missing type argument, a type former without
parentheses, a universe as a type argument, a type parameter after a value
parameter (also through the name of a function type), a reserved name, a
value binder for a type parameter, the declared name after a binder gives a
new name, a constructor at an opaque type, a term of another type parameter,
and a polymorphic function as the argument of `map`. One case in
`test/functions.test.mjs` changes: `Type 0` is now the type of a type
parameter, so the case uses `Type 1`. No mutation run covers this slice.

The function parameter slice adds `test/higher-order.test.mjs` with 13
cases and `examples/higher.ledger`. The positive cases apply a function
parameter, group a parameter type and an argument in parentheses, give a
`WritePath` argument, forward a function parameter to a second function,
bind a function argument through a parameter whose type itself takes a
function, keep the scope of an argument when the caller has parameters with
the same names, give a function parameter to `map` and to `fold`, use a
function parameter next to a renamed type parameter, and run the example.
Three cases refuse a program at its byte: an argument with another
parameter type, result type or arity, a parameter of a polymorphic function
type (also in grouping parentheses), and a grouped parameter type without
its closing parenthesis. Two cases in `test/paths.test.mjs` change: `Rule`
and `WritePath` are now parameter types, so the cases use `List Rule` and
`List WritePath`. No mutation run covers this slice.
