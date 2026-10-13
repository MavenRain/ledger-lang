# Dependent types plan

This plan covers items 1 and 2 of "Remaining M0 work" in `STATUS.md`:
dependent function types, Sigma, `transport`, `cong`, `Query` parameters
and `ReadPath`. Each
step is one slice with its own tests. Each step keeps all earlier tests.

## Starting model (before D1)

- A type is an `LType` value. `tyEq A x y` keeps the canonical JSON text of
  the two sides. `refl` compares the two texts.
- A function keeps the tokens of its body. The definition checks the body
  once with null for each parameter. Each application parses and evaluates
  the body again with the argument values.
- Thus a type cannot depend on a value parameter. At the definition check,
  every parameter is null, so `Eq Nat n m` would have two equal sides.

## Neutral values

A neutral value is a value that the checker does not know, because it is a
parameter. The checker can compare a neutral value only with itself.

The plan adds neutral values in two stages:

1. Neutral sides (D1, D2, D3a). A side of `tyEq` is a `Val`: `valClosed`
   with the canonical JSON text of a closed value, or `valVar` with the
   position of the parameter in the function type. A neutral side is equal
   only to itself. D1 and D2 kept a neutral side as text (byte 0, then the
   position). D3a gives the sides their own type.
2. A value domain (D3 and later). A `Term` syntax tree replaces the body
   tokens. A `Val` family holds closed values and neutral terms: a variable
   with its position, or a neutral term applied to values. The checker
   evaluates types into `Val` and compares them by read-back
   (normalization by evaluation). The sides of `tyEq` become `Val` values.
   D4 does this for the sides of `tyEq` with no new `Val` kind: a computed
   side keeps a syntax tree in normal form, and two sides compare by these
   trees. Types still compare by their names.

## Steps

- D1 (done). A function type can end in `Eq A x y`. A side is the name of a
  value parameter of type A, or an atom that names no value parameter and
  applies no function. The definition checks the body against the neutral
  sides. `refl` needs the same parameter or the same closed value on both
  sides. A side such as `(some n)` that contains a parameter was refused
  until D4a.
  Prefixing a named function type shifts its neutral parameter positions.
  D1 refused each application of a function with neutral sides. D2 lifts
  this for saturated applications.
  A reference to the whole function can still be passed as an argument.
- D2 (done). Instantiation at an application. An application replaces each
  neutral side with the side of the argument at that position. Then
  `def p : Eq Nat 3 3 := f 3` checks. In a definition body, an argument at
  such a position is a parameter of the body, which gives the neutral side
  of that parameter, or a literal or a name, which gives its JSON text. So
  `fun (n : Nat) => f n` proves `Eq Nat n n`. A parenthesized argument at
  such a position was refused until D4. An application in an inline function
  or a fold step, through `either`, as a partial application or through a
  bound function parameter is still refused.
- D2b (done). A proof parameter `(e : Eq A x y)` can name earlier value
  parameters of type A as its sides, so `symm e` and `trans e d` work in a
  body. An application checks a proof argument against the parameter type
  with the sides of the earlier arguments. The run binds the proof parameter
  with that type. A function with such a parameter is refused as a partial
  application, through a bound function parameter and as the function of a
  structure form or a fold step. An inline body cannot capture a proof with
  neutral sides from an outer parameter scope; closed proof captures work.
- D3a (done). The sides of `tyEq` are `Val` values, not text. `refl` and
  `trans` compare sides with `sameVal`. A type name prints a neutral side
  as byte 0, then its position, as before. No program changes its result.
- D4a (done). Computed sides in one atom. A side can be an atom that
  applies constructor forms to value parameters and literals, such as
  `(some n)` or `(pair n 1)`. The checker keeps such a side as a `valTerm`:
  its syntax tree, with a marker variable for each parameter. `refl` needs
  structurally equal trees on both sides, so `(some n)` and `(some m)` are
  not equal. An application binds the markers to the argument values and
  evaluates the side to a closed value, so `f 3` proves
  `Eq (Option Nat) (some 3) (some 3)`.
  In a definition body the argument at such a position must be a parameter
  of the body until D4c. A computed side is refused in a signature with a type
  parameter, when it names a function parameter, or with `fun`. A function
  parameter elsewhere in the signature is allowed. A side with the name of
  an earlier definition was refused until D4.
- D4b (done). The type of a proof parameter can have a computed side, as in
  `(e : Eq (Option Nat) (some n) (some m))`. An application evaluates these
  sides with the earlier arguments. Then it checks the proof argument. The
  run binds the proof parameter with the evaluated type. In a definition
  body, the argument at such a position follows the rules of D4a and D4c.
- D4c (done). Closed arguments in a body. In a definition body, a literal
  or the name of an earlier definition at the position of a marker gives
  its own node to the computed side. A side with no marker left is
  evaluated to a closed value, so `fun (m : Nat) => f 3` proves
  `Eq (Option Nat) (some 3) (some 3)`. A side that keeps a marker keeps the
  argument node, so `pf m 1` proves
  `Eq (Prod Nat Nat) (pair m 1) (pair m 1)`. Until D4, such a side did not
  evaluate the name of an earlier definition, so with
  `def one : Nat := 1`, `pf m one` did not prove `(pair m 1)`, and a
  parenthesized argument was refused.
- D3 (syntax tree done). The checker checks a body once into a `Term` and
  keeps its tokens as a fallback. Applications try the term evaluator;
  body evaluation can still fall back to parsing the tokens. The work
  budget and JSON output stay the same. D4 adds neutral evaluation and
  read-back for computed sides. A computed side keeps only its `Term`
  node, with a marker variable for each parameter. Computed sides compare with
  `same_term`; shifting and renaming markers walk the tree. `close_side`
  evaluates the tree with `eval_term` and refuses an unknown answer without
  replaying tokens. These token uses remain after D6:
  - `synth_term`, `eval_apply` and `apply_body` (`compiler/checker.c`):
    body evaluation can fall back to `parse_term`.
  - `unary_of`, `stepper_argument` and the inline, partial and bound
    callback helpers (`compiler/checker.c`): parser routes for structure
    forms and folds keep token-only `TERM_BODY` carriers, which
    `apply_body` parses again.
  - `mark_side` and `marker_bindings` (`compiler/program.c`) and
    `body_term_side` (`compiler/checker.c`): the parse input of a computed
    side and of a parenthesized argument in a body. A `Val` keeps no
    tokens.
  - `pack_term` and `neutral_witness` (`compiler/checker.c`, D5): the
    argument tokens of `pack` and of a projection give the side of the
    witness, as for a parenthesized argument in a body.
  - `eval_synth` (`compiler/checker.c`, D6): the `TERM_TRANSPORT` node
    keeps the source tokens of the motive. Each evaluation parses the
    motive again in the scope of the application, so a type parameter or a
    value parameter of the body gets its argument.
- D4 (done). Computed sides. A side can be a term of value parameters,
  literals, constructor forms, names of earlier definitions and
  applications of earlier definitions, such as `(natAdd n 1)` or
  `(pair n one)`. The checker evaluates the side to a normal form and keeps
  it as the syntax tree of a `valTerm`. A normal form is a parameter, a
  literal, a constructor form of normal forms, or a neutral application: an
  earlier definition applied to normal forms, with a parameter in an
  argument. Two sides are equal when their normal forms are equal. The
  checker evaluates a side when it makes the definition and again after an
  application renames the markers. A side with no parameter left becomes a
  closed value. A closed name evaluates, so with `def one : Nat := 1`,
  `pf m one` proves `(pair m 1)`. If the side of `p1` is `(pair n one)`,
  `p1 m` proves `(pair m 1)` and `p1 3` proves `(pair 3 1)`.
  D4 does not unfold a definition, so `refl` does not prove
  `Eq Nat (natAdd 1 n) (natAdd n 1)`. The work budget of a closed part
  stays 1, so a closed application of an earlier definition does not
  close: `(pair n (inc 3))` keeps the node `(inc 3)` and does not become a
  pair of numbers. If the side of `f` is `(some (inc n))`, `f 3` does not
  prove `Eq (Option Nat) (some 3) (some 3)`.
  In a definition body, a parenthesized argument at the position of a
  neutral side gives its normal form to the side. The application puts the
  node of the argument in place of the marker. So
  `fun (m : Nat) => e (natAdd m 1)` proves
  `Eq Nat (natAdd m 1) (natAdd m 1)`, and `pf m (one)` proves
  `(pair m 1)`. A group around a parameter stays a group, so `pf (m) 1`
  does not prove `(pair m 1)`. A parenthesized argument gets its type from
  the type arguments: with `polyProof : (A : Type 0) -> (n : A) -> Eq A n n`,
  `polyProof Nat (identity m)` proves `Eq Nat (identity m) (identity m)`,
  and `polyProof Text (identity m)` is refused.
  A computed side is still refused with `fun`, in a signature with a type
  parameter, or when it names a function parameter. A signature can have a
  function parameter that the side does not name.
- D5 (done). Sigma. In `Sigma (x : A) B`, B can name the binder x, also in
  an `Eq` side. The short form `Sigma A B` has no binder. `pack a b` checks
  only against an expected Sigma type, also in a function body. It checks a
  against A, puts the value of a for x in B and checks b against that B.
  Thus `def one : Sigma (x : Nat) (Eq Nat x 1) := pack 1 refl` checks, and
  `fun (n : Nat) => pack n refl` has the type
  `(n : Nat) -> Sigma (x : Nat) (Eq Nat x n)`. `witness s` has the type A.
  `payload s` has B with the witness for x. On a closed value, a projection
  gives the value. If `u` is `pack 1 (pack 1 refl)` of the type
  `Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat x y))`, `payload u` has the
  type `Sigma (y : Nat) (Eq Nat 1 y)`. On a parameter of a function body, a
  projection gives the null value, and `payload s` has B with `(witness s)`
  for x. Thus for `s : Sigma (x : Nat) (Eq Nat x x)`, `payload s` proves
  `Eq Nat (witness s) (witness s)`, and `pack (witness s) (payload s)` has
  the type of s. A declared side can name a projection of a parameter, as
  in `Eq Nat (payload s) (payload s)` for `s : Sigma Nat Nat`. A
  projection can be nested, as in `witness (payload s)`. A neutral value
  does not prove a false `Eq`: for two parameters s and t, `refl` does not
  prove `Eq Nat (witness s) (witness t)`.
  An instance of a Sigma type is the JSON object
  `{"witness": a, "payload": b}` (`SPEC.md`). An `Eq` payload writes null.
  The "type" text puts each argument in parentheses and names x by its
  binder, as in `Sigma (x : Nat) (Eq (Nat) (x) (x))`. The short form
  writes `Sigma (Nat) (Text)`.
  `pack` with no expected Sigma type, and a projection of a value that is
  not a Sigma, give "expected a Sigma type". A literal argument, as in
  `witness 1`, does not synthesize its type, as for `first`. A projection
  with a different type, such as `payload s` for `Eq Nat 2 2` when the
  witness of s is 1, gives "term does not have the declared type". A
  `refl` payload for unequal sides gives "refl needs two equal sides".
  A closed witness substitutes its JSON encoding for x in B, including
  a record witness. In a function body, a parameter or a projection stays
  as a neutral side.
- D6 (done). `cong` and `transport`. `cong f e` proves
  `Eq B (f x) (f y)` from `e : Eq A x y`. f is the name of an earlier
  definition with one data parameter, and its result type B is a data type
  that does not name the parameter. Else the checker gives "cong needs a
  function with one data parameter". A and B come from e and f, so
  `cong f refl` gives "cannot infer the type of this term". The sides are
  computed sides (D4). An application with a parameter marker stays
  neutral. A closed `Nat` side evaluates f and keeps the JSON encoding of
  its result. `cong` is a proof.
  `transport (z : A) B e t` checks t against B with x for z. Its type is B
  with y for z, and its value is the value of t, so
  `def u : Option Nat := transport (z : Nat) (Option Nat) pf (some 1)`
  writes `{"name":"u","type":"Option (Nat)","value":1}`. The motive has
  the binder form of D5. B can name z and the type and value parameters
  of the function body, and B can be a Sigma type. If A is not the type of
  e, the checker gives "the parameter type does not match the equality
  type". If e is not an equality, it gives "expected an equality proof".
  A t that does not check against B with x, or a declared type other than
  B with y, gives "term does not have the declared type". A closed side of
  e keeps only its JSON text, and the compiler has no JSON reader. Thus a
  closed side of a type other than `Nat` gives the same refusal in both
  forms. A neutral side gives null for z. A named family `P` in place of
  the motive moves to D7 or a later step.
- D7 (done). `Query` parameters and `ReadPath` (STATUS item 2). A function
  parameter can have the type `Query T`, also with a type parameter `T`.
  `ReadPath` is the function type
  `(answer : Type 0) -> (log : Log) -> (query : Query answer) -> answer`
  in `Type 1`. A definition of type `ReadPath` is a function of the
  program, like `WritePath`, and writes no instance. A parameter can have a
  named function type with a type parameter, and an application
  `r Flag log ask` gives the type arguments first. A named signature at the
  end of a longer function type can bring its type parameter after value
  parameters, as in `(head : Hash) -> ReadPath`. A type argument after a
  value argument stays refused (an M0 limit). Two function types that
  differ only in the names of their type parameters are the same type.

## Limits that stay

- The output holds instances of data types only. Proofs and functions are
  not instances.
- Every check and evaluation uses fuel or structural recursion.
