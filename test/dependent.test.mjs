import assert from 'node:assert/strict';
import test from 'node:test';
import { createCompiler } from '../bin/bridge.mjs';

const compile = await createCompiler();
const encoder = new TextEncoder();
const run = source => JSON.parse(compile(encoder.encode(source)));
const instances = source => {
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify(result));
  return result.instances;
};
const reflError = 'refl needs two equal sides';
// Each case names the last occurrence of `at` in the source as the error byte.
const reject = (source, message, at) => {
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['error'], JSON.stringify(result));
  assert.equal(result.error.message, message);
  assert.equal(result.error.byte, source.lastIndexOf(at));
};
const refuse = source => {
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['error'], JSON.stringify(result));
};
const k = ' def k : Nat := 1';
const kOut = [{ name: 'k', type: 'Nat', value: 1 }];

test('an equality result can name a value parameter on both sides', () => {
  assert.deepEqual(instances('def f : (n : Nat) -> Eq Nat n n := fun (n : Nat) => refl' + k), kOut);
  assert.deepEqual(instances('def f : (n : Text) -> Eq Text n n := fun (m : Text) => refl' + k), kOut);
  assert.deepEqual(instances(
    'def f : (n : Nat) -> (c : Option Nat) -> Eq (Option Nat) c c := fun (n : Nat) (c : Option Nat) => refl' + k), kOut);
});

test('an equality result can use a type parameter and closed sides', () => {
  assert.deepEqual(instances('def f : (A : Type 0) -> (x : A) -> Eq A x x := fun (A : Type 0) (x : A) => refl' + k), kOut);
  assert.deepEqual(instances('def f : (n : Nat) -> Eq Nat 3 3 := fun (n : Nat) => refl' + k), kOut);
  assert.deepEqual(instances('def three : Nat := 3 def f : (n : Nat) -> Eq Nat three 3 := fun (n : Nat) => refl'),
    [{ name: 'three', type: 'Nat', value: 3 }]);
});

test('a parameter is equal only to itself', () => {
  reject('def f : (n : Nat) -> (m : Nat) -> Eq Nat n m := fun (n : Nat) (m : Nat) => refl', reflError, 'refl');
  reject('def f : (n : Nat) -> Eq Nat n 3 := fun (n : Nat) => refl', reflError, 'refl');
  reject('def n : Nat := 3 def f : (n : Nat) -> Eq Nat n 3 := fun (n : Nat) => refl', reflError, 'refl');
});

test('a side names a parameter of the side type, and only as a whole side', () => {
  refuse('def f : (t : Text) -> Eq Nat t t := fun (t : Text) => refl');
  refuse('def f : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl');
  refuse('def f : (n : Nat) -> Eq (Prod Nat Nat) (pair n 1) (pair n 1) := fun (n : Nat) => refl');
});

test('an application instantiates a dependent result', () => {
  const f = 'def f : (n : Nat) -> Eq Nat n n := fun (n : Nat) => refl';
  assert.deepEqual(instances(f + ' def p : Eq Nat 3 3 := f 3' + k), kOut);
  assert.deepEqual(instances(f + ' def three : Nat := 3 def p : Eq Nat 3 3 := f three' + k), [{ name: 'three', type: 'Nat', value: 3 }, ...kOut]);
  assert.deepEqual(instances('def f : (A : Type 0) -> (x : A) -> Eq A x x := fun (A : Type 0) (x : A) => refl' +
    ' def p : Eq Text "a" "a" := f Text "a"' +
    ' def q : Eq (Option Nat) (some 1) (some 1) := f (Option Nat) (some 1)' + k), kOut);
  refuse(f + ' def p : Eq Nat 3 4 := f 3');
  refuse(f + ' def x : Nat := f 3');
});

test('a function body can apply a proof function to its parameters', () => {
  const f = 'def f : (n : Nat) -> Eq Nat n n := fun (n : Nat) => refl';
  assert.deepEqual(instances(f + ' def g : (n : Nat) -> Eq Nat n n := fun (n : Nat) => f n' +
    ' def p : Eq Nat 5 5 := g 5' + k), kOut);
  assert.deepEqual(instances(f + ' def g : (n : Nat) -> (m : Nat) -> Eq Nat m m :=' +
    ' fun (n : Nat) (m : Nat) => trans (f m) (symm (f m)) def p : Eq Nat 2 2 := g 1 2' + k), kOut);
  assert.deepEqual(instances(f + ' def three : Nat := 3' +
    ' def g : (n : Nat) -> Eq Nat 3 3 := fun (n : Nat) => f three def p : Eq Nat 3 3 := g 0' + k), [{ name: 'three', type: 'Nat', value: 3 }, ...kOut]);
  assert.deepEqual(instances('def f : (A : Type 0) -> (x : A) -> Eq A x x := fun (A : Type 0) (x : A) => refl' +
    ' def g : (B : Type 0) -> (y : B) -> Eq B y y := fun (B : Type 0) (y : B) => (f B y)' +
    ' def p : Eq Text "t" "t" := g Text "t"' + k), kOut);
  refuse(f + ' def g : (n : Nat) -> (m : Nat) -> Eq Nat n n := fun (n : Nat) (m : Nat) => f m');
  refuse(f + ' def g : (n : Nat) -> Eq Nat n 3 := fun (n : Nat) => f n');
  refuse(f + ' def g : (n : Nat) -> Eq Nat 3 3 := fun (n : Nat) => f n');
  refuse(f + ' def id : (n : Nat) -> Nat := fun (n : Nat) => n' +
    ' def g : (n : Nat) -> Eq Nat n n := fun (n : Nat) => f (id n)');
  refuse(f + ' def g : (n : Nat) -> Eq Nat 3 3 := fun (n : Nat) => f 4');
});

test('prefixed named signatures rebase their equality parameters', () => {
  const prefix = 'def P : Type 0 := (n : Nat) -> Eq Nat n n' +
    ' def Q : Type 0 := (t : Text) -> P' +
    ' def use : (f : Q) -> Nat := fun (f : Q) => 1';
  assert.deepEqual(instances(prefix +
    ' def proof : (t : Text) -> (n : Nat) -> Eq Nat n n := fun (t : Text) (n : Nat) => refl' +
    ' def answer : Nat := use proof'), [{ name: 'answer', type: 'Nat', value: 1 }]);
  assert.deepEqual(instances(prefix +
    ' def R : Type 0 := (b : Flag) -> Q' +
    ' def useR : (f : R) -> Nat := fun (f : R) => 2' +
    ' def proof : (b : Flag) -> (t : Text) -> (n : Nat) -> Eq Nat n n := fun (b : Flag) (t : Text) (n : Nat) => refl' +
    ' def answer : Nat := useR proof'), [{ name: 'answer', type: 'Nat', value: 2 }]);
});

test('applications cannot capture a neutral from another function scope', () => {
  const prefix = 'def same : (n : Nat) -> Eq Nat n n := fun (n : Nat) => refl';
  for (const body of ['same 0', 'symm (same 0)', 'trans (same 0) (same 1)',
    'either same same (left 0)']) {
    refuse(prefix + ' def proof : (n : Nat) -> Eq Nat n n := fun (n : Nat) => ' + body);
  }
  refuse('def P : Type 0 := (n : Nat) -> Eq Nat n n' +
    ' def proof : (n : Nat) -> (f : P) -> Eq Nat n n := fun (n : Nat) (f : P) => f 0');
  const bridges = 'def L : Type 0 := (n : Nat) -> Eq Nat 0 n' +
    ' def R : Type 0 := (n : Nat) -> Eq Nat n 1';
  for (const body of ['trans (f 0) (g 1)',
    'trans (either f f (left 0)) (either g g (right 1))']) {
    refuse(bridges + ' def proof : (f : L) -> (g : R) -> Eq Nat 0 1 :=' +
      ' fun (f : L) (g : R) => ' + body);
  }
});

test('partial applications cannot retain a bound equality parameter', () => {
  refuse('def P : Type 0 := (n : Nat) -> Eq Nat n n' +
    ' def use : (f : P) -> Nat := fun (f : P) => 1' +
    ' def proof : (n : Nat) -> (m : Nat) -> Eq Nat n n := fun (n : Nat) (m : Nat) => refl' +
    ' def answer : Nat := use (proof 0)');
});

test('dependent function references and closed equality applications still work', () => {
  assert.deepEqual(instances('def P : Type 0 := (n : Nat) -> Eq Nat n n' +
    ' def use : (f : P) -> Nat := fun (f : P) => 1' +
    ' def same : P := fun (n : Nat) => refl' +
    ' def answer : Nat := use same'), [{ name: 'answer', type: 'Nat', value: 1 }]);
  assert.deepEqual(instances('def proof : (n : Nat) -> Eq Nat 3 3 := fun (n : Nat) => refl' +
    ' def p : Eq Nat 3 3 := proof 0' + k), kOut);
});
