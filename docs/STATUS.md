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
- Dependent equality results, step D1 of `docs/DEPENDENT-TYPES.md`. A
  function type can end in `Eq A x y`, and a side can be the name of a value
  parameter of type A. Such a side is neutral. The definition checks the
  body with the neutral sides, so `refl` needs the same parameter or the
  same closed value on both sides. Step D2: an application replaces
  each neutral side with the side of its argument. In a definition body, an
  argument that names a parameter of the body gives the neutral side of
  that parameter. Step D2b: the type of a proof parameter `(e : Eq A x y)`
  can name earlier value parameters, and an application checks a proof
  argument with the sides of the earlier arguments.
- Functions: function types `(x : A) -> B` over data types,
  `fun` with flat or curried binders, and saturated application. The
  definition checks the body once. Each application evaluates the body again
  with the argument values. A function body can apply an earlier function.
  A function body can use `map`, `bind`, `filter`, `either`, `fold` and
  `unfold`. A function that a form applies evaluates in the scope of its
  definition.
  The body evaluates in the scope of its definition. All evaluated bodies of
  a program share one work budget. Functions are not instances.
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
  argument names a function with one parameter, including a function parameter.
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
- Function types in type definitions. A type definition in `Type 0` names a
  function type without type parameters. The name stands for the function
  type as the type of a function definition, in another type definition,
  and at the end of a longer function type. `WritePath` is the built-in function type
  `(log : Log) -> (write : Write) -> Step`.
- Named function parameters, including grouped aliases and `WritePath`.
  An argument names a function or another function parameter of the same
  type, or partially applies a function by binding its leading parameters.
  `map`, `bind` and `filter` take a name or a partial application that
  binds all but the last parameter. `fold` and `unfold` take a name or a
  partial application whose written arguments bind the leading parameters,
  as do the five functions of a fold over `Value`.
  `map`, `bind` and `filter` also take an inline `fun` with one binder of a
  data type. The body is checked once against the result type of the form,
  with the binder bound to null, and keeps the scope of the form.
  The parameter keeps the argument's definition scope and can be
  applied, forwarded, or used by a structure or algebra form. Function
  types with type parameters cannot be parameter types.

- Type parameters. A function type can start with type parameters
  `(A : Type 0)`. The types of the later parameters and the result type can
  use the name of a type parameter. The definition checks its body one time
  with an opaque type for each type parameter. An application gives one data
  type for each type parameter, and the checker replaces all type parameters
  in one step. A binder can give a new name to a type parameter. A type
  definition of a function type with a type parameter is in `Type 1`.
- Inline functions of `fold` and `unfold`. The function of `fold` or
  `unfold`, and each of the five functions of a fold over `Value`, can be
  `(fun (x : A) .. => body)`. The binders give the parameter types. The form
  gives the result type: the declared type for `fold`, `Option (Prod E S)`
  or `Option S` for `unfold` with the seed type `S` of the first binder,
  and the layer type of `S` for `unfold` into `Value`. The form checks the
  binders against its source or its seed. The body is checked at the form
  with each binder bound to null.
- Inline function arguments. A function argument can be
  `(fun (x : A) .. => body)` with one or more binders of data types. The
  binders must match the parameters of the expected function type. The body
  is checked at the argument against the expected result type, with each
  binder bound to null. The parameter keeps the scope of the application.
  A bare `fun` argument needs parentheses.
- Inline bound arguments. A partial application can bind a parameter of a
  function type with a parenthesized `(fun (x : A) .. => body)`. This applies
  to a partial application that is a function argument, the function of a
  structure form, or the function of `fold`. The body is checked at the
  partial application against the parameter type. The closure keeps the
  scope of the partial application.

- Nested bound partial applications. A bound function argument can itself
  be a partial application, including in structure forms and folds. Each
  nested closure keeps the scope of the outer partial application.
- Partial applications of functions with type parameters. The written
  arguments start with one data type for each type parameter. The closure
  keeps the tokens of the type arguments and parses them again in the scope
  of the application, so they can name the type parameters of the caller.
  This applies to function arguments, nested bound arguments, structure
  forms, `fold`, `unfold` and the five functions of a fold over `Value`. A
  partial application with type parameters can bind another one, also in
  the body of a function with type parameters.

## Remaining M0 work

1. Add dependent function types and support computed function
   expressions.
   These need an internal value domain with neutral terms. Then
   add Sigma checking and evaluation, `transport`, and `cong`, and allow
   `Eq` inside Sigma and Pi types. `docs/DEPENDENT-TYPES.md` gives the plan
   in steps D1 to D7. D1 is done.
2. Add `ReadPath`. It has a type parameter and a `Query` parameter, so it
   needs the dependent function types of item 1. Until then the type parser
   refuses this name with `this type belongs to a later milestone`.
3. Extend diagnostics with declaration context and improve source/output
   budgets as measurements justify changes.

## Known limits of this slice

- `map`, `bind`, `filter`, `fold` and `unfold` use one step of the depth
  fuel for each element. The depth fuel is one step per source byte, at most
  512 steps. Thus a long list made by `bind`, or a `fold` over a large `Nat`,
  can stop with a fuel error. Every form takes a function name or a
  parenthesized partial application, including the five functions of a fold
  over `Value`. `map`, `bind` and `filter` also take an inline `fun` with one
  binder. `fold` and `unfold` also take an inline `fun` with one or more
  binders, and so do the five functions of a fold over `Value`. A function
  argument of a function can also be a `fun` term.
- Over `Value`, `fold` and `unfold` use one step of the depth fuel for each
  level and for each earlier child of the same list. The limit of `unfold`
  into `Value` counts applications, not elements or levels. A fold over
  `Value` needs all five functions. It cannot leave out a case.
- The source of `fold` must synthesize its type. A literal source such as
  `nil` or a string is refused. Name it in an earlier definition. The initial
  value of a `fold` over a sequence can be parenthesized, including a fully
  applied function such as `(pickK 3 4)`.

- A function argument is a name, optionally grouped, or a parenthesized
  partial application binding leading parameters. The remaining signature
  must match the expected type. A bound function argument is a name,
  optionally grouped, a parenthesized inline function, or a nested partial
  application. A partial application of a function with type parameters
  gives all type arguments first.
  A function of type `WritePath`
  is a function of the program. The compiler does not supply the write
  path of M1.
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
  application parses and evaluates the body again. A body can apply an
  earlier function, so the work budget limits the number of evaluated
  bodies to 8 per source byte plus 64. The body check at the definition
  binds each parameter to null. Thus a constructor error that depends on a
  parameter is reported at the application.

M1 remains the write path, entry hashes, and record projection. M2 remains
the indexed read path. The core files and full specification retain their
original meaning.

- Type parameters come before the value parameters. A type argument is in
  the position of an argument, so a type former such as `Prod Nat Nat` needs
  parentheses. The checker does not infer a type argument. The name of a
  function with a type parameter is not a function argument. A partial
  application that gives its type arguments is. A data type cannot depend on a value parameter. Only a side of an
  equality result can name one, as the whole side or inside an atom of
  constructor forms and literals such as `(some n)` (step D4a). An application of a
  function with such a result replaces each neutral side with the side of
  its argument (step D2). In a definition body such an argument is a
  parameter of the body, a literal or a name. The type of a proof parameter
  can name earlier value parameters the same way (step D2b). Partial
  applications of such a function are refused. The name of a
  type parameter is not a reserved name.

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
