import assert from 'node:assert/strict';
import test from 'node:test';
import { createCompiler } from '../bin/bridge.mjs';

const compile = await createCompiler();
const encoder = new TextEncoder();
const run = source => JSON.parse(compile(encoder.encode(source)));
const last = source => {
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify(result));
  return result.instances.at(-1);
};
// Each case names the last occurrence of `at` in the source as the error byte.
const reject = (source, message, at) => {
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['error'], JSON.stringify(result));
  assert.equal(result.error.message, message);
  assert.equal(result.error.byte, source.lastIndexOf(at));
};

const id = 'def id : (n : Nat) -> Nat := fun (n : Nat) => n ';
// The bodies of `one` and `pick` use the global x. A caller that has a
// parameter x must not replace it.
const scoped = 'def x : Nat := 1 def one : (y : Nat) -> Nat := fun (y : Nat) => x ' +
  'def pick : (item : Nat) -> (acc : Nat) -> Nat := fun (item : Nat) (acc : Nat) => x ';
// b0 gives two copies. Each later function binds the previous function over
// its own result, so bK gives 2^(2^K) copies.
const fan = k => k === 0 ? 'def b0 : (n : Nat) -> List Nat := fun (n : Nat) => cons n (cons n nil) '
  : `def b${k} : (n : Nat) -> List Nat := fun (n : Nat) => bind b${k - 1} (b${k - 1} n) `;
const fans = depth => Array.from({ length: depth + 1 }, (unused, k) => fan(k)).join('');

test('a function body applies a function with a structure form', () => {
  assert.deepEqual(last(id + 'def h : (n : Nat) -> List Nat := fun (n : Nat) => map id (cons n (cons 7 nil)) ' +
    'def r : List Nat := h 9'), { name: 'r', type: 'List (Nat)', value: [9, 7] });
  assert.deepEqual(last(id + 'def inner : (n : Nat) -> List Nat := fun (n : Nat) => map id (cons n nil) ' +
    'def outer : (n : Nat) -> List (List Nat) := fun (n : Nat) => map inner (cons n (cons 3 nil)) ' +
    'def r : List (List Nat) := outer 4').value, [[4], [3]]);
  assert.deepEqual(last(fans(1) + 'def r : List Nat := b1 5').value, [5, 5, 5, 5]);
});

test('a function that a form applies evaluates in the scope of its definition', () => {
  assert.deepEqual(last(scoped + 'def g : (x : Nat) -> List Nat := fun (x : Nat) => map one (cons x (cons 7 nil)) ' +
    'def r : List Nat := g 9').value, [1, 1]);
  assert.equal(last(scoped + 'def g : (x : Nat) -> Nat := fun (x : Nat) => either one one (inl x) ' +
    'def r : Nat := g 9').value, 1);
  assert.equal(last(scoped + 'def g : (x : List Nat) -> Nat := fun (x : List Nat) => fold pick 0 x ' +
    'def r : Nat := g (cons 5 nil)').value, 1);
});

test('the definition checks a form in a function body and does not evaluate it', () => {
  assert.equal(last(id + 'def n : Nat := 2 def h : (k : Nat) -> List Nat := fun (k : Nat) => map id (cons k nil)').name, 'n');
  reject('def add : (a : Nat) -> (b : Nat) -> Nat := fun (a : Nat) (b : Nat) => a ' +
    'def g : (x : Nat) -> List Nat := fun (x : Nat) => map add (cons x nil)',
    'expected a function with one parameter', 'add');
  reject(id + 'def g : (x : Nat) -> Option (List Nat) := fun (x : Nat) => some map id (cons x nil)',
    'argument needs parentheses', 'map');
});

test('forms in function bodies use the shared work budget', () => {
  assert.equal(last(fans(2) + 'def r : List Nat := b2 5').value.length, 16);
  const result = run(fans(4) + 'def r : List Nat := b4 5');
  assert.deepEqual(Object.keys(result), ['error'], JSON.stringify(result).slice(0, 200));
  assert.equal(result.error.message, 'work budget exceeded');
  // The budget ends in the body of b0.
  assert.equal(result.error.byte, fans(4).indexOf('cons'));
});
