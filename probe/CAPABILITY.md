# Host capability probe: mechanism-lang

Date: 2026-10-04. Host tree: `/Users/oobi/Documents/mechanism-lang` at HEAD 58bdc3b, read only. Driver: `_bend2/bin/mech.exe`, a shell wrapper for `_bend2/bin/mechanism-native` (built 2026-10-02). Other sessions loaded the machine during the probe, so each wall time is an upper bound.

To run the probe again: `python3 probe/probe.py` runs all steps, and `python3 probe/probe.py check build` runs the steps whose label contains one of the words. Each step runs below `probe/guard.py`, which stops a command above 4096 MB resident memory or above its time limit. `MECH` selects a different driver. The probe writes only below a new temporary directory. The largest process in the probe used 83 MB.

## 1. Commands

| Job | Command | Result |
| --- | --- | --- |
| Check | `mech.exe check FILE` | Exit 0 and no output, or exit 1 and one error line on stderr. One file only. |
| Build | `mech.exe build FILE... -o OUT.wasm --export NAME...` | A Wasm GC reactor module. The driver joins the files in order. |
| Run | `mech.exe run FILE --export NAME --host kernel\|node\|wasmtime\|both` | Prints one Nat in decimal. NAME must be a definition of type Nat with no argument. |

- `check` and `run` accept one file, so the probe joins `core/schema.mech` and the probe file into one temporary file. `build` accepts many files.
- No prelude file is necessary. The initial environment holds `Nat` and five primitives. All other types in the probe are `mu` declarations in user code.
- Cost: check of `schema.mech` 0.08 s to 0.27 s and 5.5 MB; check of schema plus ops (450 lines) 0.2 s and 6 MB; build of schema plus `out.mech` 0.13 s and 9.5 MB. `run` of a small file 0.2 s to 0.6 s. `run` of a file that includes the schema 2 s to 6.5 s on all three hosts, so `run` is the slow path and `build` is the fast path. Resident memory: kernel 9.5 MB, wasmtime 15 MB, node 42 MB.
- Not probed: `check --print`, `check --erased`, and imports between files.

## 2. Core files

`core/schema.mech` checks. `core/schema.mech` plus `core/ops.mech` checks, which includes the indexed `Query` family at `Type 1`. This was the first time that the two files went through the host.

## 3. Recursion and totality

`probe/rec.mech` checks and its four results agree on the three hosts (4, 2, 42, 4).

- `def rec` works over `Text`, over `List A` with an erased type parameter, with the structural argument in the second position, and with a function argument (a fold).
- A mutual group is `def rec f : T := ... and g : U := ... and h : V := ...`. It works over the mutual `Value`, `Values`, `Attrs` group.
- A constructor takes no type parameter argument: write `cons head tail` and `nil`. A pattern binds an erased constructor field as `0 name`.
- The host refuses a recursive call on the same argument and on a larger argument: `termination: recursive definition NAME failed the structural termination guard` (exit 1).

## 4. Nat

- The primitives are `natAdd`, `natSub`, `natMul`, `natEq`, `natLt`. There is no division and no remainder.
- `natSub 3 5` is 0.
- `natEq` and `natLt` return the built-in sum with two legs. Leg 0 is false and leg 1 is true: `case (natLt a b) as v return T with | 0 (x : prod ()) => ... | 1 (t : prod ()) => ...`.
- `Nat` has no constructors, so a definition cannot recurse on a Nat. A recursion over numbers needs a separate structural argument (a `Fuel` family). The probe divides 255 by ten with fuel: quotient 25, last digit 5.
- The checker accepts large literals and products (`natMul 100000 100000`). A value above the i31 range cannot cross to a host: kernel `10000000000 is outside the i31 range`, node `illegal cast`, wasmtime `cast failure` (exit 4). Thus only bytes and small counts can cross the boundary.
- A decimal printer for `valueNat` needs long division from `natLt`, `natSub`, `natMul` and fuel.

## 5. How a Text leaves the host

`run` returns one small Nat, so a Text cannot leave through `run`. The reactor path works:

- `build` with `--export` for each function gives a module with no imports. Each export is a Wasm function, and a constant such as `emptyText` is a function with no argument.
- A Nat crosses as a JavaScript number. A Text crosses as an opaque reference that the driver gives back to other exports.
- `probe/drive.mjs` pushes bytes with `consText`, calls `transform`, and pulls the result with `textLength`, `textHead`, `textTail`. The host tree uses the same pattern in `test/veil/runtime/reactor.kan` and `reactor.mjs`.

## 6. Cost of the byte path

- 1,000 bytes, default node stack: wrong=0, push 0.96 ms, transform 0.2 ms, length 0.06 ms, pull 0.54 ms, process 0.16 s, 45 MB.
- 10,000 and 100,000 bytes, default node stack: `RangeError: Maximum call stack size exceeded`. A recursion that is not a tail call (`textLength`, `mapBump`) uses one Wasm frame for each byte.
- 10,000 bytes, node --stack-size=7000: wrong=0, push 37.81 ms, transform 4.38 ms, length 0.37 ms, pull 3.22 ms, process 0.191 s, 50.6 MB
- 100,000 bytes, node --stack-size=7000: FAILED (RangeError: Maximum call stack size exceeded)
- 100,000 bytes, ulimit -s 65520, node --stack-size=60000: wrong=0, push 41.74 ms, transform 58.27 ms, length 3.28 ms, pull 30.57 ms, process 0.294 s, 83.1 MB

## 7. Dependent constructors

`probe/dep.mech` checks with no prelude file and its result agrees on the three hosts (2). It uses an indexed family with an erased index, a Sigma type `(n : Count) * Vec Nat n` with the pair `(a, b)` and the projections `.1` and `.2`, an equality family in `Prop` with erased endpoints, transport through `case e as self in Same right return B right`, a function over an erased type, and a definition at `Type 1`. With architecture A the ledger-lang checker supplies its own type formers, so the compiler source needs these host features only for its own data.

## Consequences for M0 (architecture A)

1. The compiler is one reactor module: `mech.exe build core/schema.mech compiler/*.mech -o ledgerc.wasm --export ...`. A small node driver pushes the source bytes, calls `compile : Text -> Text`, and pulls the JSON bytes or the error text.
2. Write each pass over `Text` as an accumulator recursion (a tail call) followed by a reverse, or give node a larger stack. The measurements in section 6 show the limit.
3. Use a `Fuel` family for each recursion that has no structural argument (the checker, the evaluator, long division).
4. Only bytes and counts below 2^30 cross the boundary.
5. Use `check` and `build` in the edit loop. Keep `run` for small files.
