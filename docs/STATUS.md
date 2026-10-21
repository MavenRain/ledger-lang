# Compiler status

M0 now implements construction, checking, and JSON encoding for every family
in `core/schema.def` and every `Type 0` family in `core/ops.def`. It does
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
  of a data type A. The compiler compares them by their JSON encoding.
  Definitions of an equality type are proofs and are not instances.
  `symm` and `trans` synthesize their types like `first`.
- Sigma types, step D5 of `docs/DEPENDENT-TYPES.md`: `Sigma (x : A) B` and
  the short form `Sigma A B`, with `pack`, `witness` and `payload`. `pack`
  checks only against an expected Sigma type. On a parameter of a function
  body, a projection is neutral, and `payload s` has B with `(witness s)`
  for x. An instance is `{"witness": a, "payload": b}`. An `Eq` payload
  writes null.
- `cong` and `transport`, step D6 of `docs/DEPENDENT-TYPES.md`.
  `cong f e` proves `Eq B (f x) (f y)` from `e : Eq A x y`, where f is an
  earlier definition with one data parameter and a data result that does
  not name the parameter. `cong` is a proof and is not an instance.
  `transport (z : A) B e t` checks t against B with x for z. Its type is B
  with y for z, and its value is the value of t. Both forms accept closed
  sides of data types such as `Text`, `Option Nat` and `List Nat`, reading
  the values back from their canonical JSON text.
- Dependent equality results, steps D1, D2, D2b, D3, D3a, D4a, D4b, D4c and D4
  of `docs/DEPENDENT-TYPES.md`. A function type can end in `Eq A x y`, and
  a side can be the name of a value parameter of type A. Such a side is
  neutral. The definition checks the body with the neutral sides, so `refl`
  needs the same parameter, the same closed value or the same computed side
  on both sides. Step D2: an application replaces
  each neutral side with the side of its argument. In a definition body, an
  argument that names a parameter of the body gives the neutral side of
  that parameter. Step D2b: the type of a proof parameter `(e : Eq A x y)`
  can name earlier value parameters, and an application checks a proof
  argument with the sides of the earlier arguments. Step D3: the checker
  checks a body once into a `Term`, and applications evaluate that `Term`
  with no token fallback (see step D3 in `docs/DEPENDENT-TYPES.md`).
  Step D3a: a side is a
  closed, neutral or computed value, and `refl` and `trans` compare sides
  the same way. Step D4a: a side can be an atom of constructor forms and
  literals that names a value parameter, such as `(some n)` (a computed
  side). Step D4b: the type of a proof parameter can hold a computed side.
  Step D4c: in a definition body, the argument for a computed side can be a
  parameter of the body, a literal or a name. Step D4: a computed side can
  also name earlier definitions and apply them, such as `(natAdd n 1)`.
  The checker keeps the side as a syntax tree in normal form and compares
  sides by these trees. It does not unfold a definition. In a definition
  body, the argument for a side can also be a parenthesized term.
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
- C compiler build (`build/ledgerc`, linked by TinyCC), command-line
  launcher, values and CRM examples, and integration tests against
  `build/ledgerc` and the CLI.
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
- Operation families of `core/ops.def`: `Moment`, `Missing`, `Verdict`,
  `Command`, `Write`, `Outcome`, `Step`, `PipelineKey`, `Bucket`,
  `StageStat`, `Renewal` and `Account360`. Construction, checking and JSON
  encoding follow the schema rules. `Log` is an alias of `List Entry`, so
  the output shows `List (Entry)`. The compiler runs the write path (see
  `## M1`) and the read path of eighteen queries (see `## M2` to `## M4`).
- `Query T` is the indexed `Query` family of `core/ops.def` as a `Type 1`
  type. The compiler checks each of the 29 constructors against its answer
  type. A Query value is not an instance. A Query type is not an argument of
  a type former. A Query type can be a function parameter or result. A
  function type containing a Query parameter or result, also inside the
  type of a function parameter, is in `Type 1`.
- Function types in type definitions. A type definition in `Type 0` names a
  function type without type parameters. The name stands for the function
  type as the type of a function definition, in another type definition,
  and at the end of a longer function type. `WritePath` is the built-in function type
  `(log : Log) -> (write : Write) -> Step`.
- `ReadPath` is the built-in function type
  `(answer : Type 0) -> (log : Log) -> (query : Query answer) -> answer` in
  `Type 1` (step D7). A type definition in `Type 1` can name it, a parameter
  can have it, and a longer function type can end with it after value
  parameters, as in `(head : Hash) -> ReadPath`. `ReadPath` and `WritePath`
  are reserved definition names.
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
  applied, forwarded, or used by a structure or algebra form. A named
  function type with a type parameter can be a parameter type, and an
  application of the parameter gives the type arguments first. A function
  type with a type parameter that has no name cannot be a parameter type.

- Type parameters. A function type can start with type parameters
  `(A : Type 0)`. The types of the later parameters and the result type can
  use the name of a type parameter. The definition checks its body one time
  with an opaque type for each type parameter. An application gives one data
  type for each type parameter, and the checker replaces all type parameters
  in one step. A binder can give a new name to a type parameter. A type
  definition of a function type with a type parameter is in `Type 1`. Two
  function types that differ only in the names of their type parameters are
  the same type.
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

## M1

M1 is the write path (C6).

- The entry hash: the hash of an entry is the SHA-256 of the compact JSON
  of the entry, as 64 hex digits.
- The builtin `write : WritePath`. `write log x` gives a `Step`. A Command
  with a Body appends one entry and gives `outcomeAppended` with the hash
  of the entry. The `prev` of the entry is the hash of the last entry. An
  `expect` that is not the hash of the last entry gives `outcomeConflict`.
  An `expect` on an empty log or a Command with no Body gives
  `outcomeDenied`.
- The records. The compiler reads each instance of type `Log`, and the log
  of each `Step` instance that `write` gives (a Step from `makeStep` makes no
  record), in program order. Each entry with a `creates...` Body makes one
  record, in log order. The identity of a record is the hash
  of its entry. Thus the same entry in two logs, or two times in one log,
  is one record. The first state of a record is the value in the Body.
- The updates. A later `createsEvent` entry sets `lastEvent = some (refTo
  h)` on the Party or Commercial record whose identity is the hash of the
  `subject` Ref. h is the hash of the Event entry. A subject hash that names
  no record changes nothing. `deletedBy`, `endedBy` and `verifiedBy` stay
  `none`.
- The target has the key `records` after `instances` only when a record
  exists. Each record is one object `{"ref", "type", "value"}`: the hash,
  the family name and the final state. The records are in the order of the
  first entry of each record.
- The hash of each entry of a log takes one work step. A budget or output
  failure of the projection gives the position and the name of the `Log` or
  `Step` definition.

## M2

M2 is the read path (parts A, B and C).

- The builtin `read : ReadPath`. `read T log q` gives the answer of the
  Query `q` on the log `log`. `q` has the type `Query T`. A definition
  that binds the name `read` hides the builtin. The read path answers
  eighteen Query constructors: `queryReplay`, `queryTail`,
  `queryAuditByActor`, `queryCommercial` and `queryProjectionSound` (M2),
  after M3 the four Commitment and the three Membership constructors (see
  `## M3`), and after M4 the six Rollups constructors (see `## M4`). Each
  other constructor gives the refusal
  "the read path does not answer this query" at the read application.
- The log queries (part B). `queryReplay momentNow` gives the full log.
  `queryReplay (momentAsOf h)` gives the entries up to and including the
  entry whose hash is `h`. `queryTail (momentAsOf h)` gives the entries
  after that entry. `queryTail momentNow` gives the empty log. A hash that
  names no entry gives the empty log. `queryAuditByActor a` gives one
  `Ref kindEvent` for each `createsEvent` entry of the actor `a`, in log
  order.
- The record queries (part C). The read path makes the M1 records of the
  log argument, as an index by entry hash. `queryCommercial r momentNow`
  gives `some` with the final state of the Commercial record whose
  identity is the hash of `r`. `queryCommercial r (momentAsOf h)` gives
  the state after the entry whose hash is `h`. The answer is `none` when
  no Commercial record has that identity, or when `h` names no entry.
  `queryProjectionSound r s` gives `flagYes` when `s` is the final state
  of the Commercial record of `r`. In each other case it gives `flagNo`.
- The work budget. The read application takes one work step. Each entry
  that a log query visits takes one work step. Each entry that a record
  query projects takes one work step. The projection stops after the
  entry of `momentAsOf`. A budget of 0 gives the budget failure at the
  read application.
- The output. The entries of a `Log` answer make no second record: the
  identity of a record is the hash of its entry (see `## M1`).
- Out of M2: the other 24 Query constructors (the Membership, Commitment,
  Artifact, Assignment, Policy and Rollups groups, and `queryTimeline`,
  `queryThread` and `queryAuditByPolicy`; after M3, 17 (see `## M3`)), a
  policy check (M7 part A: see `## M7`), a host runtime, the find by
  merge key of `commandResolveParty` (M7 part B1: see `## M7`),
  `commandExtract` with more than one entry for each write, and the 21
  Commands with no body (after M7 part A, 20; after part B1, 15).

## M3

M3 is the Commitment group (part A) and the Membership group (part B) of
the read path.

- The Commitment queries (part A). A Commitment record of a commercial
  is in force at a moment when its `status` is not
  `commitmentSuperseded` and no Commitment record up to the moment has
  `supersedes = some` a Ref whose hash is the ref of the record.
  `queryTermsInForce c m` gives the in-force Commitment records of the
  commercial `c` as of `m`, as `Ref kindCommitment` items in log order;
  no record gives `nil`. `queryTermHistory r` gives the `supersedes`
  chain of the Commitment record `r` as `Ref kindCommitment` items,
  oldest first, the given record last; the walk stops at
  `supersedes = none`, at a hash that names no record, or after as many
  steps as there are records; an unknown ref gives `nil`.
  `queryAmountReconciled c` gives `flagYes` when the Commercial record
  `c` has `amountCents = some n` and an in-force `commitmentPrice` record
  of `c` with `status = commitmentAgreed` has the value `n`; in each
  other case it gives `flagNo`. `queryDiscountPct c` gives
  `some ((first - agreed) * 100 / first)` with the Nat division, where
  `agreed` is the value of that in-force agreed price record and `first`
  is the value of the oldest `commitmentPrice` record of `c` earlier in
  the log than the agreed record; it gives `none` with no agreed price,
  no earlier price record, `first = 0`, or `agreed > first`.
- The Membership queries (part B). A Membership record is current at a
  moment when it is in the records up to the moment and its `endedBy`
  field is `none`. `queryMembersOf o m` gives the current Membership
  records of the org `o` as of `m`, as `Ref kindMembership` items in log
  order; no record gives `nil`. `queryEmployer p m` gives the `org` of
  the first current record of the person `p` whose `isPrimary` is
  `flagYes`; else the `org` of the first current record of `p`; else
  `none`. `queryJobChanges (momentAsOf h)` gives the `person` of each
  Membership record after the entry whose hash is `h`, as
  `Ref kindParty` items in log order. `queryJobChanges momentNow` gives
  `nil`. A hash that names no entry gives `nil`.
- The work budget. The read application takes one work step. Each entry
  that a query projects takes one work step. A filter walk and the
  chain walk take no step. A budget of 0 gives the budget failure at the
  read application.
- Out of M3: the other 17 Query constructors (the Artifact, Assignment,
  Policy and Rollups groups, and `queryTimeline`, `queryThread` and
  `queryAuditByPolicy`; after M4, 11 (see `## M4`)).

## M4

M4 is the Rollups group of the read path: the pipeline queries (part A),
the renewal and account queries (part B) and the review queue (part C).
The position of a record is its index in log order, and L is the number
of records.

- The pipeline (part A). `queryPipeline k m` gives one `Bucket` for each
  distinct key text of the Commercial records as of `m`, in the log order
  of the first record of each key. The key text is the `stage` field for
  `pipelineByStage` and the `expectedCloseOn` field for
  `pipelineByCloseDate`. The `count` of a Bucket is the number of its
  records. Its `amountCents` is the saturating sum of the
  `amountCents = some n` values of its records; a `none` adds 0.
  `momentAsOf h` reads the entries up to and including the first entry
  whose hash is `h`; a hash that names no entry gives `nil`. The keys
  `pipelineByOwner` and `pipelineByTerritory` give the refusal of the
  read path.
- The stage statistics (part A). A stage change is an Event record with
  the type `eventStageChanged`, the subject `subjectCommercial` and a Text
  `after` in its payload. `queryStageStats` gives one `StageStat` for each
  stage text of the full log, in first-seen log order: a Commercial record
  names its `stage`, and a stage change names its `before`, then its
  `after`. `entered` is the number of stage changes whose `after` is the
  stage, and `advanced` is the number of stage changes whose `before` is
  the stage. `entriesInStage` is the sum of exit - enter over the stays
  in the stage. A stay starts at a Commercial record in the stage or at a
  stage change into the stage. Its exit is the position of the next stage
  change of the deal out of the stage, else L. The unit is log entries,
  because the schema has no clock. The stage of a Commercial record here
  is its stage as created (its Body), not the stage that the M7
  projection sets (`## M7`; delta A-8).
- The stale deals (part A). The last position of a Commercial record is
  the larger of its position and the position of its `lastEvent` record.
  `queryStaleDeals q` gives each Commercial record of the full log whose
  last position p has p + q < L, as `Ref kindCommercial` items in log
  order.
- The renewals (part B). `queryRenewals` gives one `Renewal` for each
  Commercial record of the full log that has an in-force `commitmentDate`
  record, in log order. The `date` is the Text of the value of the oldest
  such record (`""` for a value that is not a Text). The `term` is the
  `Ref kindCommitment` item of the oldest in-force `commitmentTerm`
  record of the deal, else `none`.
- The account view (part B). `queryAccount360 p m` gives the `Account360`
  of the Party record `p` as of `m`: the party record, its current
  Membership records, and the Commercial, Assignment, Artifact and Event
  (timeline) records that name the party or one of its deals. Each list
  is in log order, and an empty list is `nil`. `momentAsOf h` reads the
  entries up to and including the first entry whose hash is `h`. When the
  Party record is not in these records (an unknown ref, a ref of a record
  of another kind, or a hash that names no entry), the query gives the
  refusal of the read path, because an `Account360` is not an Option.
- The review queue (part C). `queryReviewQueue n` gives the ref of each
  record of the full log whose `provenance` field has
  `confidence = some k` with k < n, as `Hash` items in log order. The
  kinds with a `provenance` field are Membership, Commitment and
  Assignment. A record with no `provenance` field, or with
  `confidence = none`, is not in the list. `n = 0` gives `nil`.
- The work budget. The read application takes one work step. Each entry
  that a query projects takes one work step. A walk over the records takes
  no step. A budget of 0 gives the budget failure at the read application.
- Out of M4: the other 11 Query constructors (the Artifact, Assignment and
  Policy groups, and `queryTimeline`, `queryThread` and
  `queryAuditByPolicy`), and the keys `pipelineByOwner` and
  `pipelineByTerritory` of `queryPipeline`.

## M5

M5 part A lets the compiler take long logs and cuts the memory of the read
path. Part A2 removes the walks of the read path that grew with the square
of the log length. The bench is `build/bench-gen N` (test/bench-gen.c): a
program with a Log of N entries with distinct texts, one `write`, and one
`read` for each of the 18 queries.

- The limits. A source has at most 8388608 bytes (8 MiB, `SOURCE_LIMIT`).
  A longer source gives "source exceeds 8388608 bytes" (in file mode, after
  the path). The output has at most 67108864 bytes (64 MiB,
  `OUTPUT_LIMIT`). A longer output gives "compiler output exceeds 67108864
  bytes". The output of a bench log is about 1180 bytes for each entry,
  thus the output of an 8 MiB bench log (about 49000 entries) stays under
  the output limit. A `read` of a log of more than 65536 entries gives
  "the read path takes at most 65536 log entries".
- The bridge limits. `bin/bridge.mjs` has the limits of `build/ledgerc`:
  `sourceLimit` is 8388608 bytes and `outputLimit` is 64 MiB (`maxBuffer`
  is 2 * `outputLimit`). `compile` refuses a longer source with
  "source exceeds 8388608 bytes" before it runs `build/ledgerc --stdin`.
- The `cons` chain. In the scope of a value definition (no binder and no
  checking frame), the checker reads a right-nested `cons` chain in a loop.
  The tail of the chain takes no depth fuel, thus the chain has no nesting
  limit. A log is a value definition, thus the bench uses this scope.
- The limit of the D3 term evaluator. The evaluator takes one step of the
  depth fuel for each level of a term. A function body, and each other
  scope with a binder or a checking frame, keeps that fuel on the parse
  path too, thus the two paths give the same failure. There a `cons` chain
  has the depth fuel cap of 512 steps: 127 nested `cons` terms compile, and
  128 give `compiler fuel exhausted`.
- The indexes. The read path puts the entry hashes in one array sorted by
  hash, and finds the place of a hash by binary search. On equal hashes the
  lower place wins, as the walk did. The records get an index sorted by
  ref. Item 3b gives these indexes to the projection of the records
  (`project_find`), which walked the records for each entry. The walks over
  the log are loops, thus a log of 16000 entries does not overflow the C
  stack.
- The speed (item 3b). The bench on macOS with `/usr/bin/time -l`, as
  seconds and peak memory footprint. "Before" is the tree before the
  indexes.
  - 1000 entries: 2.00 s, 148 MB (before: 1.77 s, 356 MB).
  - 4000 entries: 13.88 s, 842 MB (before: 15.06 s, 4.15 GB).
  - 16000 entries: 119.41 s, 7.54 GB (before: 60.1 GB, and the 16 MiB
    output limit of that tree stopped the run).

  Part A did not meet the Q-M5-4 time target: t(16000) / t(1000) was 59.7,
  and the target is at most 24. The target of no stack overflow at 16000
  entries is met. The time target moved to part A2 (Q-M5-23). The profile
  of the 4000 entry run ranked `text_of_bytes`, `same_text`, `write_field`,
  `renewal_first` and `write_attr` first.
- The walks of part A2. Three walks grew with the square of the log length.
  Now each query makes its index once, and each lookup is one `index_find`.
  The output bytes and the refusals do not change.
  - `renewal_first` walked all the records for each Commercial record.
    `renewal_index` keys each in-force Commitment record by the hash of its
    commercial and its kind tag. On equal keys the oldest record wins.
  - `commitment_superseded` walked all the records for each in-force test.
    `supersedes_index` keys the `supersedes` Ref of each Commitment record,
    and `commitment_in_force` is the status test and one lookup.
  - `account_listed` walked the list of commercials for each entry.
    `account_index` keys each commercial by the hash of its Ref.
- The speed after part A2 (the same bench):
  - 1000 entries: 0.53 s, 127 MB.
  - 4000 entries: 2.28 s, 507 MB.
  - 16000 entries: 7.95 s, 2.04 GB, with no stack overflow.

  t(16000) / t(1000) is 15.00, thus the Q-M5-4 growth target (at most 24)
  is met. The Q-M5-4 target of the 16000 entry case under 1 s is not met.
  It moves to a later part.
- The tests. The Makefile has `test: build build/bench-gen`, because the
  node rows "m5 cons chain keeps the bytes" and "m5 long log keeps the
  answers" compile the bench logs of 64 and 1000 entries through the
  bridge. The rows hash the bridge output and a final newline, because the
  `--stdin` output has no final newline and the digests are of the CLI
  output. The row "m5 source limit" checks the source limit of the bridge.
- The certificate (parts B to E). `build/ledgerc --certificate` writes one
  mechanism-lang module, and the mechanism-lang kernel (`MECH_BIN`) checks
  it in a separate run. `--certificate-core` writes the rows of
  `core/schema.def` and `core/ops.def` as one module. The module of a
  program holds the instances, SHA-256 in mech (`core/certificate.def`),
  the entry hashes, the write outcomes, the records and the `records` key
  of the target. Its last def claims that the render of the instances is
  the JSON document and its newline. Part E adds the eighteen queries of
  the read path in the groups of M2 (5), M3 (7) and M4 (6), and removes
  the subject `the read path` of the refusal "the certificate does not
  cover SUBJECT yet". A `read` of one of the eleven other `Query`
  constructors keeps the refusal "the read path does not answer this
  query".
- The certificate lines. `make certificate-check` runs the C certificate
  tests (39 kernel checks). Then it checks the core module, the programs
  of `CERT_PROGRAMS` and the programs of `CERT_EXTRA` (default empty). A
  watchdog kills a check above `CERT_LIMIT` bytes (default 4294967296,
  4 GB). The max RSS and the peak footprint of each check, in bytes, on
  2026-10-18 (the bytes change from run to run):
  - the core module: 21987328 and 20808328.
  - `examples/crm.ledger`: 397410304 and 342229832.
  - `test/certificate-small.ledger`: 403783680 and 325780296.
  - `test/certificate-write1.ledger`: 668631040 and 432997288.
  - `test/certificate-write3.ledger`: 1428422656 and 745194624.
  - `test/certificate-read-m2.ledger`: 1213693952 and 636142600.
  - `test/certificate-read-m3.ledger`: 1469612032 and 742573184.
  - `test/certificate-read-m4.ledger`: 1428471808 and 871613664.

  With `CERT_EXTRA`, the gate also checks three more programs with a
  `read`. The largest check is a program with all the entry queries: max
  RSS 2658140160 and peak footprint 3312077920, under the 4 GB limit.
- Out of M5: the 16000 entry case under 1 s (a later part) and the forms
  of the refusal "the certificate does not cover SUBJECT yet" (README.md).

## M6

M6 answers the remaining queries of the read path. Part A answers the two
Artifact queries from the records of the projection (`read_artifact` in
compiler/checker.c, beside the M4 readers). Each entry takes one work step
and the walks take no step (the D10 budget model).

- `queryEvidence fact`: the entry whose hash is `fact`. An Event entry gives
  its `artifact` as a list of one ref, or `nil` when the field is `none`. An
  Artifact entry gives the ref of kind `kindArtifact` to `fact`. Each other
  entry, and no entry at that hash, gives `nil`.
- `queryArtifactIntact artifact digest`: `flagYes` when the Artifact record
  named by the ref has a `sha256` equal to `digest`, else `flagNo`. No record
  gives `flagNo`.
- The certificate. The core module answers the two queries with the arms
  `evidenceRead` and `intactRead` of `readWithH` (core/certificate.def). The
  program test/certificate-read-m6a.ledger (3 entries, 7 reads, 14 hash
  blocks) is in CERT_PROGRAMS of `make certificate-check`: max RSS 968998912 B,
  footprint 634340384 B (the kernel fc80b5d). The d3 case 109 holds the
  same program; its certificate case runs through CERT_EXTRA of the gate
  script.
- The refusal "the read path does not answer this query" now names four
  constructors: twenty-five of the 29 `Query` constructors have an answer.
- Tests: `test_m6_evidence` and `test_m6_intact` in test/c-modules.c; the
  rows "m6 queryEvidence lists the artifact of an event", "m6
  queryArtifactIntact compares the sha256" and "m6 certificate of the
  Artifact queries checks" in test/paths.test.mjs. The refusal rows (the
  row "m5 certificate refuses an out query", the C rows
  `test_m2_read_callback_check` and `test_m2_read_check_parity`, the d3
  case 78) now read `queryDryRun`, a part D constructor.

Part B answers the three Event queries from the same records (`read_event`
in compiler/checker.c, beside `read_artifact`). Two refs are equal when
their constructor and their ref text are equal. Each entry takes one work
step and the walks take no step.

- `queryTimeline subject moment`: the refs of the Event records whose
  `subject` equals `subject`, in log order, as of `moment`. `momentNow`
  reads the full log; `momentAsOf h` reads the entries up to and including
  the entry whose hash is `h`; a hash that names no entry gives `nil`.
  `subjectParty` does not widen to the commercials or the memberships of
  the party.
- `queryThread root`: `root` first, then the refs of the Event records
  whose `parent` chain reaches `root`, in log order. A `root` that names no
  Event entry gives `nil`. Parent lookup uses the full record set, so a
  manually constructed log can list descendants before their parents.
- `queryAuditByPolicy policy`: the refs of the Event records whose `policy`
  is `some policy`, in log order, over the full log.
- The certificate. The core module answers the three queries with the arms
  `timelineRead`, `threadRead` and `auditPolicyRead` of `readWithH`
  (core/certificate.def). The program test/certificate-read-m6b.ledger (3
  entries, 10 reads, 17 hash blocks) is in CERT_PROGRAMS of `make
  certificate-check`: max RSS 1004929024 B, footprint 742245456 B (the
  kernel fc80b5d). It includes a reversed log for the thread regression.
  The d3 case 110 holds the original nine-read program; its certificate
  case runs through CERT_EXTRA of the gate script.
- Tests: `test_m6_timeline`, `test_m6_thread` and `test_m6_audit_policy` in
  test/c-modules.c; the rows "m6 queryTimeline lists the events of a
  subject as of a moment", "m6 queryThread lists the root then its
  descendants", "m6 queryAuditByPolicy lists the events of a policy" and
  "m6 certificate of the Event queries checks" in test/paths.test.mjs.

Part C answers the two Assignment queries and the two remaining pipeline
keys from the same records (`read_assignment` in compiler/checker.c, beside
`read_event`; `pipeline_key` takes the key kind). An Assignment record is
current when its `endedBy` is `none`. Two Accounts are equal when their
constructor and their ref text are equal. Each entry takes one work step
and the walks take no step.

- `queryOwner account moment`: `some` the assignee of the last current
  Assignment record whose `subject` equals `account` and whose `role` is
  `roleOwner`, in log order, as of `moment`; `none` when there is no such
  record.
- `queryBook assignee moment`: the subjects of the current Assignment
  records whose `assignee` is `assignee`, any role, distinct, in the order
  of their first record, as of `moment` (ruling Q-M6-8 (a)).
- `queryPipeline pipelineByOwner moment` and `queryPipeline
  pipelineByTerritory moment`: the owner of a Commercial record is the
  `queryOwner` answer of `accountCommercial c`, else of `accountParty p` for
  its party (ruling Q-M6-10 (a)). The owner key is the ref text of the
  assignee and the territory key is the `territory` of that Assignment
  record; no owner or no territory gives the empty key. Every Commercial
  record gets a key (ruling Q-M6-19 (a)). The refusal of the two keys goes.
- The certificate. The core module answers the queries with the arms
  `ownerRead` and `bookRead` of `readWithH` and the key function `pipeKey`
  of the pipeline arms (core/certificate.def). The program
  test/certificate-read-m6c.ledger (4 entries, 8 reads, 23 hash blocks) is
  in CERT_PROGRAMS of `make certificate-check`: max RSS 1550663680 B,
  footprint 2998930144 B (the kernel fc80b5d). The d3 case 111 holds the
  same program; its certificate case runs through CERT_EXTRA of the gate
  script.
- Tests: `test_m6_owner`, `test_m6_book` and `test_m6_pipeline_keys` in
  test/c-modules.c; the rows "m6 queryOwner gives the last current owner",
  "m6 queryBook lists the distinct accounts of an assignee", "m6
  queryPipeline by owner and by territory key on the owner assignment" and
  "m6 certificate of the Assignment queries checks" in test/paths.test.mjs.
  The row "queryPipeline by owner keeps the refusal" is now "queryPipeline
  by owner gives the empty key with no assignments".

Part D1 answers the two Policy check queries from the same records
(`read_policy` in compiler/checker.c, beside `read_assignment`), over the
full log (no moment). A Policy record takes part when its `active` is
`true`. It applies to a subject when its `appliesTo` is `scopeAll`,
`scopeParty` with `subjectParty`, or `scopeCommercial k` with
`subjectCommercial c` whose Commercial record has the kind `k` (ruling
Q-M6-11 (a)). An AclRule allows a request when its `principal` is the
principal, the action is in its `can` list, and its `fields` are `none`,
or the requested fields are `none`, or each requested field is in its
`fields`. Each entry takes one work step and the walks take no step.

- `queryCan principal action subject fields`: `verdictAllow` with the ref
  of the first active applying Policy record (in log order) that has an
  allowing rule; else `verdictDeny` with `some` the ref of the first active
  applying Policy record; else `verdictDeny none`.
- `queryRedacted principal subject`: the attrs of the Party record of
  `subjectParty` or of the Commercial record of `subjectCommercial`, in
  order, with only the keys `k` that an active applying Policy record lets
  the principal read (`permissionRead` on the fields `some [k]`; a rule
  with the fields `none` keeps each key). Each other subject, and a ref with
  no record of that family, gives `attrsEnd`.
- The certificate. The core module answers the two queries with the arms
  `canRead` and `redactRead` of `readWithH` (core/certificate.def). The
  answer type `Verdict` is in the ops families of compiler/certificate.c
  (ruling Q-M6-21 (a)). The program test/certificate-read-m6d.ledger (3
  entries, 7 reads, 18 hash blocks) is in CERT_PROGRAMS of `make
  certificate-check`: max RSS 728612864 B, footprint 950207928 B (the kernel
  fc80b5d). The d3 case 112 holds the same program; its certificate case
  runs through CERT_EXTRA of the gate script.
- The refusal "the read path does not answer this query" now names two
  constructors, `queryDryRun` and `querySimulatePolicy`: twenty-seven of
  the 29 `Query` constructors have an answer.
- Tests: `test_m6_can` and `test_m6_redacted` in test/c-modules.c; the rows
  "m6 queryCan gives the verdict of the first applying policy", "m6
  queryRedacted keeps the fields that a rule lets the principal read" and
  "m6 certificate of the Policy queries checks" in test/paths.test.mjs.

Part D2 answers the two remaining queries from the entries and the records
(`read_rule` in compiler/checker.c, beside `read_policy`), over the full
log (no moment). A Policy record takes part and applies to a subject as in
part D1.

- `queryDryRun commercial stage`: the `Missing` values of each active
  Policy record (in log order) that applies to `subjectCommercial
  commercial`, whose `toStage` is `some stage` and whose `fromStage` is
  `none` or the `stage` of the Commercial record. For each such record:
  `missingField` for each key of the `require` fields that is not a key of
  the attrs of the Commercial record; then `missingCommitment` for each
  kind of `commitmentKinds` with no Commitment record of the commercial
  with that kind and the status `commitmentAgreed`, superseded or not
  (ruling Q-M6-23 (3) (a)); then `missingApproval` for each role of
  `approvalFrom` with no `eventApproval` Event record on the commercial
  whose payload has the role as a key (ruling Q-M6-23 (1) (a)).
  `maxDiscountPct` gives no `Missing` value. Each entry takes one work
  step.
- `querySimulatePolicy policy`: the refs of the entries (in log order)
  that create an Event with a `policy`, when the verdict changes with
  `policy` in place of each Policy record of the same `name` (ruling
  Q-M6-23 (4) (a)). An `eventPolicyDenied` event was a deny, each other
  event an allow. The request is the actor of the entry (the party ref
  text of `actorHuman`, else the name; ruling Q-M6-23 (2) (a)), the action
  of the event type (ruling Q-M6-13 (a)), the event subject and the fields
  `none`. Each entry takes two work steps: its hash, then its record
  (delta D-2).
- The certificate. The core module answers the two queries with the arms
  `dryRead` and `simWalk` of `readWithH` (core/certificate.def). The
  program test/certificate-read-m6e.ledger (3 entries, 4 reads, 19 hash
  blocks) is in CERT_PROGRAMS of `make certificate-check`: max RSS
  1022394368 B, footprint 836945480 B (the kernel fc80b5d). The d3 case
  113 holds the same program; its certificate case runs through
  CERT_EXTRA of the gate script.
- Each of the 29 `Query` constructors has an answer (ruling Q-M6-20 (a)).
  The refusal "the read path does not answer this query" stays only for
  `queryAccount360` of a party with no Party record (ruling Q-M6-22 (a)).
  The refusal rows (the row "m5 certificate refuses an unknown party", the
  C rows `test_m2_read_callback_check` and `test_m2_read_check_parity`,
  the d3 case 78) now read that query.
- Tests: `test_m6_dry` and `test_m6_simulate` in test/c-modules.c; the
  rows "m6 queryDryRun and querySimulatePolicy answer over the m6e
  program" and "m6 certificate of the dry run and simulate queries checks"
  in test/paths.test.mjs.

## M7

M7 gives the Commands their bodies and checks the policy on the write
path. Part A checks each write that has a Body (`write_step` in
compiler/checker.c), gives `commandTransition` its Body, and lets the
projection set the stage (`projection_rows` in compiler/program.c).

- The order. `write log x` makes the Body, checks the policy, compares
  the `expect`, then appends (the default of Q-M7-7).
- The ask. The principal is the actor of the Write (`actor_text`; the
  default of Q-M7-6). The action and the subject come from the table of
  the Command (`write_asks`; the default of Q-M7-8): `commandTransition`
  asks `permissionTransition` on `subjectCommercial c`, `commandAssign`
  asks `permissionAssign` on the Account, and each other Command with a
  Body asks `permissionWrite` on the parent record of the create (the
  `org` of `commandStartMembership`, the `party` of
  `commandOpenCommercial`, the `commercial` of `commandPropose`, the
  subject of the event of `commandRecord`, each subject of the artifact
  of `commandIngest`). `commandResolveParty` asks with no subject, so
  only a `scopeAll` Policy record applies to it (delta A-7). The fields
  of each ask are `none`.
- The verdict. The check is the policy check of `queryCan` over the
  records of the input log. The first active applying Policy record that
  allows the request: the write goes on with `policy = some p`. Active
  applying Policy records and none that allows: `outcomeDenied (some p)
  nil`, where `p` is the first of them, and the log does not change
  (ruling Q-M7-3 (a)). No active applying Policy record: the write goes
  on with `policy = none` (ruling Q-M7-5 (a)). On the read path,
  `queryCan` gives `verdictDeny none` for that case. With more than one
  subject, the first deny denies; else the policy is that of the first
  allow (delta A-6). `commandIngest` with no subjects asks once with no
  subject.
- The missing record. The Ref of a Command that changes a record must
  name a record of its kind; else the write gives `outcomeDenied none
  [missingField "<field>"]` (the default of Q-M7-10, delta A-2). In part
  A this is the `commercial` of `commandTransition`. The parent Ref of a
  create is not checked.
- `commandTransition c s`. The entry is `createsEvent (makeEvent
  eventStageChanged (subjectCommercial c) none none [before, after]
  policy)`: `before` is the stage of the record of `c`, `after` is `s`,
  and `policy` is the allowing Policy record, or `none` (the default of
  Q-M7-11). After an allow, the dry run of `queryDryRun` for `c` and `s`
  is the guard: a missing list that is not empty gives `outcomeDenied
  (some g) missing`, where `g` is the first guard Policy record in log
  order with a missing item of its own (delta A-5).
- The projection. A table of rows (EventType, record type, field,
  payload key) sets a field of a record from the payload of an Event.
  Part A has one row: an `eventStageChanged` Event sets the `stage` of
  its Commercial record to the `after` of its payload. `lastEvent` is as
  in `## M1`. The records, `queryPipeline pipelineByStage` and the
  `fromStage` check of `queryDryRun` see the new stage;
  `queryStageStats` reads the stage of each record as created (delta
  A-8, see `## M4`).
- The work budget. The check projects the input log on a private
  budget, and the walk takes no work step (delta A-1). No budget output
  of M1 to M6 changes.
- The expect (ruling Q-M7-9 (a)). An `expect` is compared with the hash
  of the last entry of the whole log, not with the hash of the last
  entry on the subject of the Command (core/ops.def:69-70). This gap
  stays open.
- The certificate. The `writeBody` arm of `commandTransition`, the
  policy check (`canRead` inside `writeWith`), the guard through the dry
  run mirror of M6 part D2 and the stage row of `ledgerLastEvent`
  (core/certificate.def, compiler/certificate.c) cover part A. The
  program test/certificate-write-m7a.ledger (one Policy record with a
  `toStage` guard and one `permissionTransition` rule, one Commercial
  record, an allowed and a denied transition; 21 hash blocks) is in
  CERT_PROGRAMS of `make certificate-check`: max RSS 920092672 B,
  footprint 1153812160 B (the kernel fc80b5d). The d3 case 114 holds an
  allowed, a denied and a no-policy write; its certificate case runs
  through CERT_EXTRA of the gate script.
- Part B1, the Party find. `commandResolveParty k n ids` finds the
  first Party record in log order that has `deletedBy = none` and an
  Identifier that matches an Identifier of `ids`: the same system tag,
  the same name for `systemOther`, and the same value. For a found
  Party, the write asks, then compares the `expect`, then gives
  `outcomeAppended [h] policy`, where `h` is the hash of the entry of
  the Party. The log does not change. If no Party is found, the write
  appends the `createsParty` entry as before.
- Part B1, the Party edits. `commandAddIdentifier`,
  `commandVerifyIdentifier`, `commandEnrichParty`, `commandDeleteParty`
  and `commandRestoreParty` have a Body. The `party` Ref must name a
  Party record; else the write gives `outcomeDenied none [missingField
  "party"]`. Each asks `permissionWrite` on the Party; the fields of the
  Enrich ask are the keys of its attrs. The entry is a `createsEvent` of
  an Event on `subjectParty p`. AddIdentifier: `eventFieldsChanged`
  with the system, the name (`systemOther` only) and the value.
  VerifyIdentifier: `eventIdentifierVerified` with the same payload; if
  no Identifier of the record matches, `outcomeDenied none
  [missingField "identifier"]`. EnrichParty: `eventFieldsChanged` with
  `attrs`; the artifact and the parent come from the provenance.
  DeleteParty: `eventDeleted` with an empty payload. RestoreParty:
  `eventFieldsChanged` with `restored = true`.
- Part B1, the Party projection. `eventDeleted` sets `deletedBy` to the
  Event. `eventFieldsChanged` with `restored` sets `deletedBy` to
  `none`; with a system and a value it adds the Identifier at the end (a
  duplicate gives no change); with `attrs`, each key replaces the same
  key and a new key goes at the end. `eventIdentifierVerified` sets
  `verifiedBy` of each matching Identifier to the Event.
- Free Identifier payloads require a known system tag and a text value;
  `systemOther` also requires a text name. Missing or non-text fields
  leave the Identifiers unchanged in C and the kernel, including on
  `eventIdentifierVerified`. Explicit empty text is valid. Every Event
  still sets `lastEvent`.
- The certificate of part B1. `systemText`, `identMatch`, `partyFind`,
  `writeFound`, the missing-record check of `party` and the 5 `writeGo`
  arms (core/certificate.def), and the Party arm of `ledgerLastEvent`
  (compiler/certificate.c). The 6 writes in one program take 40 hash
  blocks (the cap is 24), so CERT_PROGRAMS has two programs:
  test/certificate-write-m7b.ledger (the find, AddIdentifier and
  VerifyIdentifier; 19 hash blocks; max RSS 1628389376 B, footprint 750978104
  B) and test/certificate-write-m7b2.ledger (EnrichParty, DeleteParty
  and RestoreParty; 24 hash blocks; max RSS 1599832064 B, footprint
  858981552 B), with the kernel fc80b5d.
- Tests: `test_m7_check`, `test_m7_transition`, `test_m7_find`,
  `test_m7_identity`, `test_m7_stage_payload` and
  `test_m7_identifier_payload` in test/c-modules.c; 7 m7 rows in
  test/paths.test.mjs. The Identifier payload matrix in
  test/c-certificate.c also checks both Event types in the kernel.

## Remaining M0 work

1. Add dependent function types and support computed function
   expressions.
   These need an internal value domain with neutral terms. Then
   add Sigma checking and evaluation, `transport`, and `cong`, and allow
   `Eq` inside Sigma and Pi types. `docs/DEPENDENT-TYPES.md` gives the plan
   in steps D1 to D7. Steps D1, D2, D2b, D3, D3a, D4a, D4b, D4c, D4, D5, D6
   and D7 are done. D5 adds Sigma checking and evaluation and `Eq` inside
   Sigma. D6 adds `cong` and `transport`. D7 adds `Query` parameters and
   `ReadPath`.
2. `ReadPath` is done (step D7). It is a function type in `Type 1`. The
   compiler runs the read path of M2, M3 and M4 for eighteen queries
   (see `## M2` to `## M4`).
3. Diagnostics with declaration context are done (D11 part C). In file
   mode, a checking or printing refusal in a declaration gives
   "byte N: message (in NAME)". UTF-8 and lexer failures happen before
   declaration parsing and give a byte offset without a declaration name.
   The source and output budgets do not change, because no measurement
   shows the need.
4. Type families are done (D12). A family
   `def P : (x : A) -> Type 0 := fun (x : A) => T` has one binder. `P a`
   in a type reduces to T with a for x, and `transport P e t` takes a named
   family as the motive. `docs/DEPENDENT-TYPES.md` gives the forms and the
   refusals. No item of this section is open.

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
  is a function of the program or the builtin `write` of M1.
- Hash wraps a Text value. The compiler computes the SHA-256 hash of each
  log entry (M1). It does not validate the digest strings of the source. It
  resolves a reference to a log entry only for the `subject` of a
  `createsEvent` entry in the record projection.
  Schema comments about business rules, such as a person's Party kind or a
  confidence percentage, do not add constraints beyond the declared types.
- The compiler reserves all schema names and every form name of SPEC.md. It
  also reserves every family, constructor and definition name of
  `core/ops.def`, including `Query` and its constructors. Field names are
  not reserved.
- Each constructor argument costs one parsing fuel step. The host requires a
  structurally recursive definition to examine its recursive argument at the
  start of its body, so the argument parser cannot skip this step. README.md
  gives the measured limits for the original scalar and container forms.
- A function keeps its body as a checked syntax tree (`Term`). Each
  application evaluates the body again. A body can apply an
  earlier function, so the work budget limits the number of evaluated
  bodies to 8 per source byte plus 64. The body check at the definition
  binds each parameter to null. Thus a constructor error that depends on a
  parameter is reported at the application.

M1 adds the write path, the entry hashes and the record projection (see
`## M1`). M2, M3 and M4 add the read path of eighteen queries from the
log and from its record index (see `## M2` to `## M4`). The core files and full
specification retain their original meaning.

- Type parameters come before the value parameters. Only a named function
  type at the end of a longer function type, such as `ReadPath`, brings its
  type parameter after value parameters. An application gives the type
  arguments first: a type argument after a value argument is read as a term
  and stops with `unknown name or constructor`. A type argument is in
  the position of an argument, so a type former such as `Prod Nat Nat` needs
  parentheses. The checker does not infer a type argument. The name of a
  function with a type parameter is a function argument only for a
  parameter of a named function type with a type parameter. A partial
  application that gives its type arguments is a function argument. A data type cannot depend on a value parameter. Only a side of an
  equality result can name one, as the whole side or inside an atom of
  constructor forms and literals such as `(some n)` (step D4a), or of names
  and applications of earlier definitions such as `(natAdd n 1)` (step D4).
  An application of a
  function with such a result replaces each neutral side with the side of
  its argument (step D2). In a definition body such an argument is a
  parameter of the body, a literal, a name or a parenthesized term, also for
  a computed side (steps D4c and D4). The type of a proof parameter
  can name earlier value parameters the same way, also inside a computed
  side (steps D2b and D4b). Partial
  applications of such a function are refused. The name of a
  type parameter is not a reserved name.

## Internal boundaries

The compiler is `compiler/*.c`. `ledger.h` declares the shared types and
functions. `runtime.c` holds compiler data types and common operations.
`lexer.c` turns Text into tokens. `schema.c` describes schema constructors
and fields from `core/schema.def`; `operations.c` describes the operation
families in the same form from `core/ops.def`; `types.c` describes
primitive and container forms. `literals.c` holds the literal texts.
`parser.c`, `checker.c`, and `evaluate.c` check and evaluate terms.
`json.c` serializes checked runtime values. `program.c` compiles
definitions and produces the success or error document. `main.c` reads the
source from a file or stdin and writes the document.

`test/schema.test.mjs` derives conformance cases from the original schema,
independently of compiler metadata. It checks every newly added constructor,
field name, field order, argument type, and arity, plus indexed references.
`test/operations.test.mjs` does the same from `core/ops.def`. Both read the
core rows through `test/core.mjs`.

Internal families such as Fuel, Token, LType, Result, Plan, and Binding cannot
be used as ledger types. The only boundary is bytes: `build/ledgerc` reads
source bytes and writes the document bytes. Node contains no language
parser, type checker, or evaluator.
