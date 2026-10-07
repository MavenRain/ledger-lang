# Dependent types plan

This plan covers items 1 and 2 of "Remaining M0 work" in `STATUS.md`:
dependent function types, Sigma, `transport`, `cong`, and `ReadPath`. Each
step is one slice with its own tests. Each step keeps all earlier tests.

## Current model

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

## Steps

- D1 (done). A function type can end in `Eq A x y`. A side is the name of a
  value parameter of type A, or an atom that names no value parameter and
  applies no function. The definition checks the body against the neutral
  sides. `refl` needs the same parameter or the same closed value on both
  sides. A side such as `(some n)` that contains a parameter is refused.
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
  such a position is refused until D4. An application in an inline function
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
- D3. Syntax tree and value domain, as above. The checker checks a body
  once into a `Term`. An application evaluates the `Term`, not the tokens.
  The work budget stays the same. The JSON output stays the same.
- D4. Computed sides. A side can be any term, such as `(natAdd n 1)` or
  `(some n)`. The checker evaluates it to a `Val`, which can be neutral.
  Two sides are equal when their read-backs are equal.
- D5. Sigma. `Sigma (x : A) B` with `pack`, `witness` and `payload`. B can
  name x, also in an `Eq`. An instance of a Sigma type is the JSON object of
  its witness and payload, as `SPEC.md` gives.
- D6. `transport` and `cong`. `cong f e` gives `Eq B (f x) (f y)` from
  `e : Eq A x y`. `transport P e t` moves `t : P x` to `P y`. Both need the
  value domain of D3 and the computed sides of D4.
- D7. `ReadPath` (STATUS item 2). It has a type parameter and a `Query`
  parameter, and `Query` is an indexed family in `Type 1`. The type parser
  then accepts the name, and a definition of type `ReadPath` is a function
  of the program, like `WritePath`.

## Limits that stay

- The output holds instances of data types only. Proofs and functions are
  not instances.
- Every check and evaluation uses fuel or structural recursion.
