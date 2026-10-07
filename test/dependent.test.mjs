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
const typeError = 'term does not have the declared type';
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

test('a side names a parameter of the side type', () => {
  refuse('def f : (t : Text) -> Eq Nat t t := fun (t : Text) => refl');
  assert.deepEqual(instances('def f : (n : Nat) -> Eq (Prod Nat Nat) (pair n 1) (pair n 1) := fun (n : Nat) => refl' + k), kOut);
});

test('a computed side names value parameters inside an atom', () => {
  const f = 'def f : (n : Nat) -> Eq (Option Nat) (some n) (some n) := fun (n : Nat) => refl';
  const g = ' def g : (m : Nat) -> Eq (Option Nat) (some m) (some m) := fun (m : Nat) =>';
  assert.deepEqual(instances(f + k), kOut);
  assert.deepEqual(instances(f + ' def p : Eq (Option Nat) (some 3) (some 3) := f 3' + k), kOut);
  assert.deepEqual(instances(f + g + ' f m def p : Eq (Option Nat) (some 4) (some 4) := g 4' + k), kOut);
  reject(f + ' def p : Eq (Option Nat) (some 4) (some 4) := f 3', typeError, 'f 3');
  reject('def f : (n : Nat) -> (m : Nat) -> Eq (Option Nat) (some n) (some m) := fun (n : Nat) (m : Nat) => refl',
    reflError, 'refl');
  reject(f + g + ' f 3', typeError, 'f 3');
  refuse('def f : (A : Type 0) -> (x : A) -> Eq (Option A) (some x) (some x) := fun (A : Type 0) (x : A) => refl');
  refuse('def f : (n : Nat) -> (e : Eq (Option Nat) (some n) (some n)) -> Nat :=' +
    ' fun (n : Nat) (e : Eq (Option Nat) (some n) (some n)) => n');
  refuse('def same : (x : Nat) -> Nat := fun (x : Nat) => x' +
    ' def f : (n : Nat) -> Eq Nat (same n) (same n) := fun (n : Nat) => refl');
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

const flip = 'def flip : (n : Nat) -> (m : Nat) -> (e : Eq Nat n m) -> Eq Nat m n :=' +
  ' fun (n : Nat) (m : Nat) (e : Eq Nat n m) => symm e';
const pick = ' def pick : (n : Nat) -> (m : Nat) -> (e : Eq Nat n m) -> Nat :=' +
  ' fun (n : Nat) (m : Nat) (e : Eq Nat n m) => m';
const answer = [{ name: 'answer', type: 'Nat', value: 4 }];

test('a proof parameter can name earlier parameters', () => {
  const chain = ' def chain : (a : Nat) -> (b : Nat) -> (c : Nat) -> (e : Eq Nat a b) -> (d : Eq Nat b c) -> Eq Nat a c :=' +
    ' fun (a : Nat) (b : Nat) (c : Nat) (e : Eq Nat a b) (d : Eq Nat b c) => trans e d';
  assert.deepEqual(instances(flip + chain + pick + ' def p : Eq Nat 2 2 := flip 2 2 refl' +
    ' def q : Eq Nat 3 3 := chain 3 3 3 refl (flip 3 3 refl)' +
    ' def answer : Nat := pick 4 4 (flip 4 4 refl)'), answer);
  assert.deepEqual(instances(flip + ' def back : (n : Nat) -> (m : Nat) -> (e : Eq Nat n m) -> Eq Nat n m :=' +
    ' fun (n : Nat) (k : Nat) (h : Eq Nat n k) => flip k n (flip n k h)' + pick +
    ' def answer : Nat := pick 4 4 (back 4 4 refl)'), answer);
  assert.deepEqual(instances('def same : (A : Type 0) -> (x : A) -> (y : A) -> (e : Eq A x y) -> Eq A y x :=' +
    ' fun (A : Type 0) (x : A) (y : A) (e : Eq A x y) => symm e' +
    ' def p : Eq Text "t" "t" := same Text "t" "t" refl def answer : Nat := 4'), answer);
});

test('a proof parameter refuses a wrong proof', () => {
  refuse(flip + ' def p : Eq Nat 1 2 := flip 2 1 refl');
  refuse(flip + ' def p : Eq Nat 1 1 := flip 1 2 refl');
  refuse(flip + pick + ' def answer : Nat := pick 4 5 refl');
  refuse('def bad : (n : Nat) -> (m : Nat) -> (e : Eq Nat n m) -> Eq Nat n n :=' +
    ' fun (n : Nat) (m : Nat) (e : Eq Nat n m) => e');
  refuse('def bad : (n : Nat) -> (m : Nat) -> (e : Eq Nat n m) -> Eq Nat m n :=' +
    ' fun (n : Nat) (m : Nat) (e : Eq Nat m n) => symm e');
  refuse(flip + ' def bad : (a : Nat) -> (b : Nat) -> (e : Eq Nat a b) -> Eq Nat a b :=' +
    ' fun (a : Nat) (b : Nat) (e : Eq Nat a b) => flip b a e');
  refuse('def bad : (e : Eq Nat n n) -> Nat := fun (e : Eq Nat n n) => 0');
  refuse('def use : (g : (n : Nat) -> (e : Eq Nat n n) -> Nat) -> Nat :=' +
    ' fun (g : (n : Nat) -> (e : Eq Nat n n) -> Nat) => g 0 refl');
});

test('prefixed named signatures rebase dependent proof parameters', () => {
  const signature = 'def S : Type 0 := (n : Nat) -> (e : Eq Nat n 0) -> Nat';
  assert.deepEqual(instances(signature +
    ' def f : (m : Nat) -> S := fun (m : Nat) (n : Nat) (e : Eq Nat n 0) => m' +
    ' def answer : Nat := f 4 0 refl'), answer);
  assert.deepEqual(instances(signature +
    ' def T : Type 0 := (t : Text) -> S' +
    ' def f : (m : Nat) -> T := fun (m : Nat) (t : Text) (n : Nat) (e : Eq Nat n 0) => m' +
    ' def answer : Nat := f 4 "x" 0 refl'), answer);
  assert.deepEqual(instances(signature +
    ' def f : (A : Type 0) -> S := fun (B : Type 0) (n : Nat) (e : Eq Nat n 0) => 4' +
    ' def answer : Nat := f Text 0 refl'), answer);
  const local = 'def P : Type 0 := (x : Nat) -> Eq Nat x x' +
    ' def S : Type 0 := (p : P) -> (n : Nat) -> (e : Eq Nat n 0) -> Nat';
  assert.deepEqual(instances(local +
    ' def f : (m : Nat) -> S := fun (m : Nat) (p : P) (n : Nat) (e : Eq Nat n 0) => m' +
    ' def proof : P := fun (x : Nat) => refl' +
    ' def answer : Nat := f 4 proof 0 refl'), answer);
});

test('prefixed proof parameters cannot capture a prefix argument', () => {
  const signature = 'def S : Type 0 := (n : Nat) -> (e : Eq Nat n 0) -> Nat';
  refuse(signature +
    ' def f : (m : Nat) -> S := fun (m : Nat) (n : Nat) (e : Eq Nat m 0) => n' +
    ' def answer : Nat := f 0 9 refl');
  refuse(signature +
    ' def f : (m : Nat) -> S := fun (m : Nat) (n : Nat) (e : Eq Nat n 0) => n' +
    ' def answer : Nat := f 0 9 refl');
});

test('inline bodies cannot reinterpret a proof from an outer parameter scope', () => {
  const prefix = 'def zero : Eq Nat 0 0 := refl' +
    ' def P : Type 0 := (m : Nat) -> Eq Nat m 0' +
    ' def ignore : (p : P) -> Nat := fun (p : P) => 4';
  for (const body of ['e', '(e)', 'trans e zero']) {
    refuse(prefix +
      ' def f : (n : Nat) -> (e : Eq Nat n 0) -> Nat :=' +
      ' fun (n : Nat) (e : Eq Nat n 0) => ignore (fun (m : Nat) => ' + body + ')' + k);
  }
  refuse('def P : Type 0 := (m : Nat) -> Eq Nat 0 m' +
    ' def ignore : (p : P) -> Nat := fun (p : P) => 4' +
    ' def f : (n : Nat) -> (e : Eq Nat n 0) -> Nat :=' +
    ' fun (n : Nat) (e : Eq Nat n 0) => ignore (fun (m : Nat) => symm e)' + k);
});

test('inline bodies can still capture closed proof parameters', () => {
  assert.deepEqual(instances('def P : Type 0 := (m : Nat) -> Eq Nat 0 0' +
    ' def apply : (p : P) -> Eq Nat 0 0 := fun (p : P) => p 7' +
    ' def f : (e : Eq Nat 0 0) -> Eq Nat 0 0 :=' +
    ' fun (e : Eq Nat 0 0) => apply (fun (m : Nat) => symm e)' +
    ' def proof : Eq Nat 0 0 := f refl' + k), kOut);
});
