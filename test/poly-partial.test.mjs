import assert from 'node:assert/strict';
import test from 'node:test';
import { readFile } from 'node:fs/promises';
import { createCompiler } from '../bin/bridge.mjs';

const compile = await createCompiler();
const encoder = new TextEncoder();
const run = source => JSON.parse(compile(encoder.encode(source)));
const last = source => {
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify(result));
  return result.instances.at(-1).value;
};
const rule = 'def Rule : Type 0 := (n : Nat) -> Nat ';
const apply = 'def apply : (f : Rule) -> (n : Nat) -> Nat := fun (f : Rule) (n : Nat) => f n ';
const use = 'def use : (h : Rule) -> Nat := fun (h : Rule) => h 1 ';
const konst = 'def konst : (A : Type 0) -> (a : A) -> (n : Nat) -> A := fun (A : Type 0) (a : A) (n : Nat) => a ';
const same = 'def same : (A : Type 0) -> (a : A) -> A := fun (A : Type 0) (a : A) => a ';
const xs = 'def xs : List Nat := cons 4 (cons 7 nil) ';
const keep = 'def keepWith : (f : Rule) -> (x : Nat) -> (acc : Nat) -> Nat := fun (f : Rule) (x : Nat) (acc : Nat) => f x ';
const prefix = rule + apply + use + konst + same + xs + keep;

test('a function argument partially applies a function with type parameters', () => {
  assert.equal(last(`${prefix}def n : Nat := use (konst Nat 6)`), 6);
  assert.equal(last(`${prefix}def n : Nat := use (same Nat)`), 1);
  assert.equal(last(`${prefix}def n : Nat := apply (konst Nat 3) 9`), 3);
  assert.equal(last(`${prefix}def n : Nat := apply (same Nat) 9`), 9);
});

test('the closure binds the type arguments for its body', () => {
  const second = 'def snd : (A : Type 0) -> (p : Prod A Nat) -> (n : Nat) -> Nat := ' +
    'fun (A : Type 0) (p : Prod A Nat) (n : Nat) => second p ';
  assert.equal(last(`${prefix}${second}def pr : Prod Text Nat := pair "x" 5 def n : Nat := use (snd Text pr)`), 5);
  const count = 'def countFrom : (A : Type 0) -> (ys : List A) -> (n : Nat) -> Nat := ' +
    'fun (A : Type 0) (ys : List A) (n : Nat) => fold (fun (y : A) (acc : Nat) => acc) n ys ';
  assert.equal(last(`${prefix}${count}def names : List Text := cons "a" (cons "b" nil) def n : Nat := use (countFrom Text names)`), 1);
});

test('type arguments and bound arguments resolve in the scope of the application', () => {
  const tag = 'def tag : (k : Nat) -> Nat := fun (k : Nat) => use (konst Nat k) ';
  assert.equal(last(`${prefix}${tag}def n : Nat := tag 9`), 9);
  const second = 'def snd : (A : Type 0) -> (p : Prod A Nat) -> (n : Nat) -> Nat := ' +
    'fun (A : Type 0) (p : Prod A Nat) (n : Nat) => second p ';
  const outer = 'def outer : (B : Type 0) -> (b : B) -> Nat := fun (B : Type 0) (b : B) => use (snd B (pair b 5)) ';
  assert.equal(last(`${prefix}${second}${outer}def n : Nat := outer Text "x"`), 5);
});

test('nested partial applications, structure forms and folds take type arguments', () => {
  assert.equal(last(`${prefix}def n : Nat := use (apply (konst Nat 5))`), 5);
  assert.deepEqual(last(`${prefix}def ys : List Nat := map (konst Nat 2) xs`), [2, 2]);
  assert.equal(last(`${prefix}def n : Nat := fold (keepWith (same Nat)) 0 xs`), 4);
  const pick = 'def pickA : (A : Type 0) -> (k : A) -> (x : Nat) -> (acc : A) -> A := ' +
    'fun (A : Type 0) (k : A) (x : Nat) (acc : A) => k ';
  assert.equal(last(`${prefix}${pick}def n : Nat := fold (pickA Nat 3) 0 xs`), 3);
});

test('partial applications with type parameters refuse wrong arguments', () => {
  const source = `${prefix}def n : Nat := apply (konst Text "x") 7`;
  assert.deepEqual(run(source), { error: {
    byte: source.lastIndexOf('konst'), message: 'term does not have the declared type',
  } });
  for (const term of ['use (konst 6)', 'use (konst Nat "x")', 'apply same 7', 'map (konst 2) xs']) {
    const result = run(`${prefix}def n : Nat := ${term}`);
    assert.ok(result.error, `${term}: ${JSON.stringify(result)}`);
  }
});

test('the example compiles', async () => {
  const source = await readFile(new URL('../examples/poly-partial.ledger', import.meta.url), 'utf8');
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify(result));
  assert.deepEqual(result.instances.map(item => item.value), [6, 1, 9, [4, 7], [2, 2]]);
});
