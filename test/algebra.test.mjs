import assert from 'node:assert/strict';
import test from 'node:test';
import { createCompiler } from '../bin/bridge.mjs';

const compile = await createCompiler();
const run = source => JSON.parse(compile(new TextEncoder().encode(source)));
const values = source => {
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify(result));
  return result.instances.map(item => item.value);
};
const reject = (source, message, at) => {
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['error'], JSON.stringify(result));
  assert.equal(result.error.message, message);
  assert.equal(result.error.byte, source.lastIndexOf(at));
};

const fieldStep = 'def step : (n : Nat) -> Option (Prod (Prod Text Value) Nat) := ' +
  'fun (n : Nat) => some (pair (pair "key" (valueNat n)) 2) ';

test('unfold rejects duplicate attribute keys instead of emitting lossy JSON', () => {
  reject(fieldStep + 'def result : Attrs := unfold step 2 1', 'duplicate attribute key', 'unfold');
});

test('unfold checks duplicate keys even when the Attrs result is consumed by a fold', () => {
  const consume = 'def keep : (field : Prod Text Value) -> (acc : Nat) -> Nat := ' +
    'fun (field : Prod Text Value) (acc : Nat) => acc ';
  const wrap = 'def id : (a : Attrs) -> Attrs := fun (a : Attrs) => a ';
  reject(fieldStep + consume + wrap +
    'def result : Nat := fold keep 0 (id (unfold step 2 1))', 'duplicate attribute key', 'unfold');
});

test('unfold stops at the requested limit before generating a duplicate field', () => {
  assert.deepEqual(values(fieldStep +
    'def empty : Attrs := unfold step 0 1 def one : Attrs := unfold step 1 1'), [{}, { key: 1 }]);
});

test('unfold and filter preserve distinct attribute keys and field order', () => {
  const source = 'def step : (s : Prod Text Text) -> Option (Prod (Prod Text Value) (Prod Text Text)) := ' +
    'fun (s : Prod Text Text) => some (pair (pair (first s) valueNull) (pair (second s) (first s))) ' +
    'def yes : (field : Prod Text Value) -> Flag := fun (field : Prod Text Value) => flagYes ' +
    'def no : (field : Prod Text Value) -> Flag := fun (field : Prod Text Value) => flagNo ' +
    'def fields : Attrs := unfold step 2 (pair "z" "a") ' +
    'def kept : Attrs := filter yes fields def removed : Attrs := filter no fields';
  const result = values(source);
  assert.deepEqual(result, [{ z: null, a: null }, { z: null, a: null }, {}]);
  assert.deepEqual(Object.keys(result[0]), ['z', 'a']);
  assert.deepEqual(Object.keys(result[1]), ['z', 'a']);
});

test('fold traverses lists from the right and returns the initial value for an empty list', () => {
  const step = 'def prepend : (n : Nat) -> (acc : List Nat) -> List Nat := ' +
    'fun (n : Nat) (acc : List Nat) => cons n acc ';
  assert.deepEqual(values(step + 'def xs : List Nat := cons 1 (cons 2 nil) ' +
    'def empty : List Nat := nil def result : List Nat := fold prepend (cons 3 nil) xs ' +
    'def initial : List Nat := fold prepend (cons 3 nil) empty'), [[1, 2], [], [1, 2, 3], [3]]);
});

test('fold over Nat applies its unary step exactly n times', () => {
  const step = 'def prepend : (acc : List Nat) -> List Nat := fun (acc : List Nat) => cons 7 acc ';
  assert.deepEqual(values(step + 'def n : Nat := 3 def z : Nat := 0 ' +
    'def three : List Nat := fold prepend nil n ' +
    'def zero : List Nat := fold prepend (cons 9 nil) z'), [3, 0, [7, 7, 7], [9]]);
});

for (const [carrier, element, input, expected] of [
  ['Text', 'Nat', '"é"', [195, 169]],
  ['Values', 'Value', 'valuesItem valueNull (valuesItem (valueNat 2) valuesEnd)', [null, 2]],
  ['Attrs', 'Prod Text Value', 'attrsField "z" valueNull (attrsField "a" (valueNat 2) attrsEnd)',
    [{ first: 'z', second: null }, { first: 'a', second: 2 }]],
]) {
  test(`fold exposes the ordered elements of ${carrier}`, () => {
    const item = element.includes(' ') ? `(${element})` : element;
    const step = `def prepend : (x : ${element}) -> (acc : List ${item}) -> List ${item} := ` +
      `fun (x : ${element}) (acc : List ${item}) => cons x acc `;
    assert.deepEqual(values(step + `def source : ${carrier} := ${input} ` +
      `def result : List ${item} := fold prepend nil source`).at(-1), expected);
  });
}

test('unfold threads its seed and preserves element order', () => {
  const step = 'def step : (s : Prod Nat Nat) -> Option (Prod Nat (Prod Nat Nat)) := ' +
    'fun (s : Prod Nat Nat) => some (pair (first s) (pair (second s) (first s))) ';
  assert.deepEqual(values(step + 'def result : List Nat := unfold step 3 (pair 1 2) ' +
    'def text : Text := unfold step 2 (pair 65 66)'), [[1, 2, 1], 'AB']);
});

test('unfold into Nat counts successful steps and distinguishes some none from none', () => {
  const next = 'def next : (s : Option Nat) -> Option (Option Nat) := ' +
    'fun (s : Option Nat) => some none ';
  const stop = 'def stop : (s : Option Nat) -> Option (Option Nat) := ' +
    'fun (s : Option Nat) => none ';
  assert.deepEqual(values(next + stop + 'def count : Nat := unfold next 3 none ' +
    'def empty : Nat := unfold stop 3 none'), [3, 0]);
});

test('unfold into Values retains null payloads and accepts an Option seed', () => {
  const step = 'def step : (s : Option Nat) -> Option (Prod Value (Option Nat)) := ' +
    'fun (s : Option Nat) => some (pair valueNull none) ';
  assert.deepEqual(values(step + 'def result : Values := unfold step 2 (some 7)'), [[null, null]]);
});

test('unfold into Text rejects a non-byte element', () => {
  const step = 'def step : (n : Nat) -> Option (Prod Nat Nat) := fun (n : Nat) => some (pair n n) ';
  reject(step + 'def result : Text := unfold step 1 256', 'textByte requires a byte below 256', 'unfold');
});

for (const [carrier, element, input, expected, empty] of [
  ['Text', 'Nat', '"é"', 'é', ''],
  ['Values', 'Value', 'valuesItem valueNull (valuesItem (valueNat 2) valuesEnd)', [null, 2], []],
]) {
  test(`filter retains or removes all elements of ${carrier}`, () => {
    const predicates = `def yes : (x : ${element}) -> Flag := fun (x : ${element}) => flagYes ` +
      `def no : (x : ${element}) -> Flag := fun (x : ${element}) => flagNo `;
    assert.deepEqual(values(predicates + `def source : ${carrier} := ${input} ` +
      `def kept : ${carrier} := filter yes source def removed : ${carrier} := filter no source`),
    [expected, expected, empty]);
  });
}
