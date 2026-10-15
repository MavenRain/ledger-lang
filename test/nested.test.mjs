import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';
import { createCompiler } from '../bin/bridge.mjs';

const compile = await createCompiler();
const encoder = new TextEncoder();
const run = source => JSON.parse(compile(encoder.encode(source)));
const values = source => {
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify(result));
  return result.instances.map(item => item.value);
};
// Each case names the last occurrence of `at` in the source as the error byte.
const reject = (source, message, at) => {
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['error'], JSON.stringify(result));
  assert.equal(result.error.message, message);
  assert.equal(result.error.byte, source.lastIndexOf(at));
};
const budgetError = 'work budget exceeded';
const overBudget = source => {
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['error'], JSON.stringify(result));
  assert.equal(result.error.message, budgetError);
};

const id = 'def id : (n : Nat) -> Nat := fun (n : Nat) => n ';
const double = 'def double : (n : Nat) -> Prod Nat Nat := fun (n : Nat) => pair n n ';
const both = 'def both : (n : Nat) -> Prod Nat Nat := fun (n : Nat) => double (id n) ';
// f0 is the identity. Each later function applies the previous function
// twice, so one application of fK evaluates 2^(K+1) - 1 bodies.
const link = k => k === 0 ? 'def f0 : (n : Nat) -> Nat := fun (n : Nat) => n '
  : `def f${k} : (n : Nat) -> Nat := fun (n : Nat) => f${k - 1} (f${k - 1} n) `;
const chain = depth => Array.from({ length: depth + 1 }, (_, k) => link(k)).join('');
const padTo = (source, bytes) => {
  assert.ok(source.length <= bytes, `the source has ${source.length} bytes`);
  return source + ' '.repeat(bytes - source.length);
};

test('a function body applies earlier functions', () => {
  const left = 'def left : (n : Nat) -> Nat := fun (n : Nat) => first (double n) ';
  const source = `${id}${double}${both}${left}def x : Prod Nat Nat := both 4 ` +
    'def y : Nat := first (both (second x)) def z : Nat := left 9';
  assert.deepEqual(values(source), [{ first: 4, second: 4 }, 4, 9]);
});

test('map applies a function whose body applies other functions', () => {
  const source = `${id}${double}${both}def xs : List (Prod Nat Nat) := map both (cons 1 (cons 2 nil))`;
  assert.deepEqual(values(source), [[{ first: 1, second: 1 }, { first: 2, second: 2 }]]);
});

test('a body evaluates in the scope of its definition', () => {
  const source = 'def k : Nat := 5 def g : (n : Nat) -> Nat := fun (n : Nat) => k ' +
    'def f : (k : Nat) -> Nat := fun (k : Nat) => g k def x : Nat := f 7';
  assert.deepEqual(values(source), [5, 5]);
  const inner = `${double}def h : (n : Nat) -> (m : Nat) -> Prod Nat Nat := fun (n : Nat) (m : Nat) => double m ` +
    'def y : Prod Nat Nat := h 1 2';
  assert.deepEqual(values(inner), [{ first: 2, second: 2 }]);
});

test('the check of a body checks an application by type', () => {
  const mismatch = 'term does not have the declared type';
  reject(`${id}def g : (n : Nat) -> Nat := fun (n : Nat) => id "a"`, mismatch, '"a"');
  reject(`${double}def g : (n : Nat) -> Nat := fun (n : Nat) => double n`, mismatch, 'double n');
  assert.deepEqual(Object.keys(run('def g : (n : Nat) -> Nat := fun (n : Nat) => g n')), ['error']);
  assert.deepEqual(Object.keys(run(`def g : (n : Nat) -> Nat := fun (n : Nat) => id n ${id}`)), ['error']);
});

test('constructor errors in a nested body surface at the application', () => {
  const byte = 'def b : (n : Nat) -> Text := fun (n : Nat) => textByte n textEnd ' +
    'def c : (n : Nat) -> Text := fun (n : Nat) => b n ';
  assert.deepEqual(values(`${byte}def t : Text := c 65`), ['A']);
  reject(`${byte}def t : Text := c 300`, 'textByte requires a byte below 256', 'textByte');
});

test('the work budget is 8 bodies for each source byte plus 64', () => {
  // id and f12 evaluate 1 + 8191 = 8192 bodies. 8 * 1016 + 64 = 8192.
  const source = `${id}${chain(12)}def x : Nat := id (f12 1)`;
  assert.deepEqual(values(padTo(source, 1016)), [1]);
  overBudget(padTo(source, 1015));
});

test('all definitions of a program share the work budget', () => {
  // Each application of f11 evaluates 4095 bodies. 8 * 1016 + 64 >= 8190.
  const one = `${chain(11)}def x : Nat := f11 1 `;
  const two = `${one}def y : Nat := f11 2`;
  assert.deepEqual(values(one), [1]);
  assert.deepEqual(values(padTo(two, 1016)), [1, 2]);
  overBudget(padTo(two, 1015));
});

test('a deep doubling chain stops at the work budget', () => {
  overBudget(`${chain(40)}def x : Nat := f40 1`);
});

test('the nested example compiles', () => {
  const source = readFileSync(new URL('../examples/nested.ledger', import.meta.url), 'utf8');
  assert.deepEqual(values(source), [{ first: 4, second: 4 }, 9]);
});

test('the sides of an equality type use the work budget', () => {
  assert.deepEqual(values(`${chain(3)}def p : Eq Nat (f3 2) 2 := refl def q : Nat := f3 5`), [5]);
  overBudget(`${chain(40)}def p : Eq Nat (f40 1) 1 := refl`);
});

// D9: the side helpers run on the remaining work budget.
const idX = 'def id : (x : Nat) -> Nat := fun (x : Nat) => x\n';
const doubled = depth =>
  Array.from({ length: depth + 1 }, (_, k) =>
    k === 0
      ? 'def f0 : (x : Nat) -> Nat := fun (x : Nat) => x\n'
      : `def f${k} : (x : Nat) -> Nat := fun (x : Nat) => f${k - 1} (f${k - 1} x)\n`,
  ).join('');
const closedSides = name =>
  `def k : (n : Nat) -> Eq Nat (${name} n) (${name} n) := fun (n : Nat) => refl\n` +
  `def p : Eq Nat (${name} 2) (${name} 2) := k 2\n`;
const types = source => {
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify(result));
  return result.instances.map(item => item.type);
};

test('a computed side closes on the remaining work budget', () => {
  assert.deepEqual(values(`${idX}${closedSides('id')}`), []);
  assert.deepEqual(values(`${doubled(1)}${closedSides('f1')}`), []);
  const proof = 'Eq Nat (id n) (id n)';
  const u = `def u : (n : Nat) -> (p : ${proof}) -> Nat := fun (n : Nat) (p : ${proof}) => n\n`;
  assert.deepEqual(values(`${idX}${u}def r : Eq Nat 2 2 := refl\ndef v : Nat := u 2 r\n`), [2]);
});

test('the work of a computed side is charged to the work budget', () => {
  // Each side of k 2 and of p evaluates 2047 bodies. 8 * 716 + 64 < 4 * 2047.
  overBudget(`${doubled(10)}${closedSides('f10')}`);
});

test('a Sigma type text gives the side terms with the bound name', () => {
  const s = `${idX}def s : Sigma (x : Nat) (Eq Nat (id x) (id x)) := pack 2 refl\n`;
  assert.deepEqual(types(`${s}def e : Eq Nat (id 2) (id 2) := payload s\n`), [
    'Sigma (x : Nat) (Eq (Nat) ((id x)) ((id x)))',
  ]);
  assert.deepEqual(types('def s : Sigma (x : Nat) (Eq (List Nat) (cons x nil) (cons x nil)) := pack 2 refl\n'), [
    'Sigma (x : Nat) (Eq (List (Nat)) ((cons x [])) ((cons x [])))',
  ]);
});

// D10: a Sigma side in a type runs on the remaining work budget.
const checks = source => {
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify(result));
};
const transported = name =>
  'def e : Eq Nat 2 2 := refl\ndef t : Eq Nat 2 2 := refl\n' +
  `def p : Eq Nat 2 2 := transport (z : Nat) (Eq Nat (${name} 2) z) e t\n`;

test('a Sigma side in a type runs on the remaining work budget', () => {
  checks(`${idX}def s : Sigma (x : Nat) (Eq Nat (id 2) (id 2)) := pack 2 refl\n`);
  const sigma = 'Sigma (x : Nat) (Eq Nat (id 2) x)';
  checks(`${idX}def g : (s : ${sigma}) -> Nat := fun (s : ${sigma}) => witness s\n`);
  checks(`${idX}def g : (n : Nat) -> ${sigma} := fun (n : Nat) => pack 2 refl\n`);
  checks(`${idX}def s : Sigma (x : Nat) (Sigma (y : Nat) (Eq Nat (id 2) y)) := pack 1 (pack 2 refl)\n`);
  checks(`${idX}${transported('id')}`);
});

test('the work of a Sigma side is charged to the work budget', () => {
  overBudget(`${doubled(11)}def s : Sigma (x : Nat) (Eq Nat (f11 2) (f11 2)) := pack 2 refl\n`);
  overBudget(`${doubled(12)}${transported('f12')}`);
  // The motive (4095 bodies) and the proof k 2 (4094 bodies) are each below 8 * 833 + 64 and together above it.
  const k = 'def k : (n : Nat) -> Eq Nat (f10 n) (f10 n) := fun (n : Nat) => refl\n';
  overBudget(
    `${doubled(11)}${k}def t : Eq Nat 2 2 := refl\ndef p : Eq Nat 2 2 := transport (z : Nat) (Eq Nat (f11 2) z) (k 2) t\n`,
  );
});

// D11 part A: a closed side in a function body is evaluated, as at the top level.
test('a closed side in a function body closes on its value', () => {
  const tr = side =>
    'def tr : (x : Nat) -> (y : Nat) -> (e : Eq Nat x y) -> ' +
    `(t : Eq Nat ${side} x) -> Eq Nat ${side} y := fun (x : Nat) (y : Nat) (e : Eq Nat x y) (t : Eq Nat ${side} x) => ` +
    'transport (z : Nat) (Eq Nat (id 2) z) e t\n';
  checks(`${idX}${tr('2')}`);
  checks(`${idX}${tr('(id 2)')}`);
  checks(
    `${idX}def k : (n : Nat) -> Eq Nat (id n) (id n) := fun (n : Nat) => refl\n` +
      'def h : (m : Nat) -> Eq Nat (id 2) (id 2) := fun (m : Nat) => k 2\n',
  );
  const list = '(cons m (cons 2 nil))';
  checks(
    `${idX}def k : (xs : List Nat) -> Eq (List Nat) xs xs := fun (xs : List Nat) => refl\n` +
      `def h : (m : Nat) -> Eq (List Nat) ${list} ${list} := fun (m : Nat) => k (cons m (cons (id 2) nil))\n`,
  );
  checks(
    `${idX}def fst : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => a\n` +
      'def k : (a : Nat) -> (b : Nat) -> Eq Nat (fst a b) (fst a b) := fun (a : Nat) (b : Nat) => refl\n' +
      'def h : (m : Nat) -> Eq Nat (fst m 2) (fst m 2) := fun (m : Nat) => k m (id 2)\n',
  );
});

test('the work of a closed side in a function body is charged to the work budget', () => {
  // The type side (f10 2) and the body side of k 2 are each below the budget and together above it.
  const k = 'def k : (n : Nat) -> Eq Nat (f10 n) (f10 n) := fun (n : Nat) => refl\n';
  checks(`${doubled(10)}${k}def h : (m : Nat) -> Eq Nat 2 2 := fun (m : Nat) => k 2\n`);
  overBudget(`${doubled(10)}${k}def h : (m : Nat) -> Eq Nat (f10 2) (f10 2) := fun (m : Nat) => k 2\n`);
});

// D11 part B: a closed side of a type other than Nat reads back from its JSON text.
test('cong and transport read a closed side back from its text', () => {
  const tx = 'def tx : (t : Text) -> Text := fun (t : Text) => t\ndef tp : Eq Text "a" "a" := refl\n';
  checks(`${tx}def c : Eq Text (tx "a") (tx "a") := cong tx tp\n`);
  checks(`${tx}def p : Eq Text "a" "a" := transport (z : Text) (Eq Text z "a") tp tp\n`);
  checks(`${tx}def u : Option Nat := transport (z : Text) (Option Nat) tp (some 1)\n`);
  const so = 'def so : (o : Option Nat) -> Option Nat := fun (o : Option Nat) => o\n';
  checks(`${so}def po : Eq (Option Nat) (some 7) (some 7) := refl\ndef c : Eq (Option Nat) (so (some 7)) (so (some 7)) := cong so po\n`);
  const list = '(cons 1 (cons 2 nil))';
  checks(
    `def pl : Eq (List Nat) ${list} ${list} := refl\n` +
      `def p : Eq (List Nat) ${list} ${list} := transport (z : List Nat) (Eq (List Nat) z ${list}) pl pl\n`,
  );
});

// D11 part C: in file mode, a refusal line names the declaration that fails.
test('a file-mode refusal line names the declaration', () => {
  const directory = mkdtempSync(join(tmpdir(), 'ledger-lang-test-'));
  const path = join(directory, 'program.ledger');
  const launcher = fileURLToPath(new URL('../bin/ledgerc', import.meta.url));
  const invoke = () => spawnSync('sh', [launcher, path], { encoding: 'utf8', timeout: 30_000 });
  try {
    writeFileSync(path, 'def a : Nat := 1\ndef b : Nat := c\n');
    const named = invoke();
    assert.equal(named.status, 1);
    assert.equal(named.stdout, '');
    assert.equal(named.stderr, `${path}: byte 32: unknown name or constructor (in b)\n`);
    writeFileSync(path, 'a : Nat := 1\n');
    const outside = invoke();
    assert.equal(outside.status, 1);
    assert.match(outside.stderr, /: byte 0: /);
    assert.doesNotMatch(outside.stderr, /\(in /);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

// D12 part A: a one-binder type family `def P : (x : A) -> Type 0 := fun (x : A) => T`
// checks and writes no instance. Each other result, and a family name with no argument
// in a type, give "expected a data type".
const familyNat = 'def P : (x : Nat) -> Type 0 := fun (x : Nat) => Nat';
[
  ['a family with a data body', familyNat],
  ['a family with the binder n', 'def F : (n : Nat) -> Type 0 := fun (n : Nat) => Nat'],
  ['a family with an equality body', 'def P : (z : Nat) -> Type 0 := fun (z : Nat) => Eq Nat z 1'],
].forEach(([label, source]) =>
  test(`${label} checks with no instance`, () => {
    assert.deepEqual(values(source), []);
    assert.deepEqual(run(source), { 'ledger-lang': 1, instances: [] });
  }),
);

[
  ['the result Type 1', 'def G : (T : Type 0) -> Type 1 := fun (T : Type 0) => Query T', 'Type 1'],
  ['a domain of level 1', 'def P : (T : Type 0) -> Type 0 := fun (T : Type 0) => Nat', 'Type 0 :='],
  ['two binders', 'def P : (x : Nat) -> (y : Nat) -> Type 0 := fun (x : Nat) (y : Nat) => Nat', 'Type 0'],
  ['a body of level 1', 'def P : (x : Nat) -> Type 0 := fun (x : Nat) => Type 0', 'Type 0'],
  ['a proof domain', 'def P : (e : Eq Nat 1 1) -> Type 0 := fun (e : Eq Nat 1 1) => Nat', 'Type 0'],
  ['a family name with no argument', `${familyNat}\ndef v : P := 3`, 'P :='],
].forEach(([label, source, at]) =>
  test(`a type family refuses ${label}`, () => reject(source, 'expected a data type', at)),
);

// D12 part B: `P a` in a result type, a parameter type or the type of a definition
// gives the reduced type of the family. A proof type writes no instance.
const familyEq = 'def Q : (z : Nat) -> Type 0 := fun (z : Nat) => Eq Nat z 1';
[
  ['a result type', `${familyNat}\ndef f : (x : Nat) -> P x := fun (x : Nat) => x`, []],
  [
    'a parameter type',
    `${familyNat}\ndef g : (x : Nat) -> (y : P x) -> Nat := fun (x : Nat) (y : P x) => y`,
    [],
  ],
  ['the type of a definition', `${familyNat}\ndef v : P 3 := 3`, [{ name: 'v', type: 'Nat', value: 3 }]],
  ['a proof type', `${familyEq}\ndef r : Q 1 := refl`, []],
].forEach(([label, source, instances]) =>
  test(`a family application in ${label} checks`, () =>
    assert.deepEqual(run(source), { 'ledger-lang': 1, instances })),
);

[
  ['an argument that does not check against A', `${familyNat}\ndef v : P "a" := 3`, '"a" :='],
  ['a value that does not check against the reduced type', `${familyNat}\ndef v : P 3 := "a"`, '"a"'],
].forEach(([label, source, at]) =>
  test(`a family application refuses ${label}`, () =>
    reject(source, 'term does not have the declared type', at)),
);
