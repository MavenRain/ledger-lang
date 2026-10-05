import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
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
const values = source => instances(source).map(item => [item.name, item.value]);
const funError = 'expected fun with the declared parameters';
const dataError = 'expected a data type';
const universeError = 'type is not in the declared universe';
const termError = 'term does not have the declared type';
const laterError = 'this type belongs to a later milestone';
// Each case names the last occurrence of `at` in the source as the error byte.
const reject = (source, message, at) => {
  const result = run(source);
  const context = `${source} -> ${JSON.stringify(result)}`;
  assert.deepEqual(Object.keys(result), ['error'], context);
  assert.equal(result.error.message, message, context);
  assert.equal(result.error.byte, source.lastIndexOf(at), context);
};

const rule = 'def Rule : Type 0 := (n : Nat) -> Prod Nat Nat ';
const actors = 'def acme : Ref kindParty := refTo (hashOf "party-acme") ' +
  'def deal : Ref kindCommercial := refTo (hashOf "deal-1") ' +
  'def advance : Write := makeWrite (actorHuman acme) none (commandTransition deal "negotiation") ' +
  'def history : Log := nil ';
const refuse = 'def refuse : WritePath := ' +
  'fun (log : Log) (write : Write) => makeStep log (outcomeDenied none nil) ';
const denied = { log: [], outcome: { tag: 'outcomeDenied', policy: null, missing: [] } };

test('a type definition names a function type and is not an instance', () => {
  assert.deepEqual(instances(rule), []);
  assert.deepEqual(values(`${rule}def double : Rule := fun (n : Nat) => pair n n def d : Prod Nat Nat := double 3`),
    [['d', { first: 3, second: 3 }]]);
});

test('binder names are free and binder types follow the named function type', () => {
  assert.deepEqual(values(`${rule}def f : Rule := fun (k : Nat) => pair k 0 def d : Prod Nat Nat := f 5`),
    [['d', { first: 5, second: 0 }]]);
  reject(`${rule}def f : Rule := fun (k : Text) => pair 1 1`, funError, '(k');
  reject(`${rule}def f : Rule := fun (n : Nat) (m : Nat) => pair n m`, funError, '(m');
  reject(`${rule}def f : Rule := 3`, funError, '3');
});

test('the body checks against the result of the named function type', () => {
  reject(`${rule}def f : Rule := fun (n : Nat) => n`, termError, 'n');
});

test('a named function type can be curried and applied in full', () => {
  const source = 'def Mk : Type 0 := (a : Text) -> (b : Nat) -> Prod Text Nat ' +
    'def mk : Mk := fun (a : Text) => fun (b : Nat) => pair a b def x : Prod Text Nat := mk "k" 2';
  assert.deepEqual(values(source), [['x', { first: 'k', second: 2 }]]);
});

test('a name of a function type stands for it in another type definition', () => {
  const source = `${rule}def Same : Type 0 := Rule ` +
    'def g : Same := fun (n : Nat) => pair 0 n def d : Prod Nat Nat := g 4';
  assert.deepEqual(values(source), [['d', { first: 0, second: 4 }]]);
});

test('a name of a function type can end a longer function type', () => {
  const source = `${rule}def Tagged : Type 0 := (label : Text) -> Rule ` +
    'def t : Tagged := fun (label : Text) (n : Nat) => pair n n ' +
    'def u : (flag : Flag) -> Tagged := fun (flag : Flag) (label : Text) (n : Nat) => pair n 1 ' +
    'def a : Prod Nat Nat := t "x" 2 def b : Prod Nat Nat := u flagYes "y" 3';
  assert.deepEqual(values(source), [['a', { first: 2, second: 2 }], ['b', { first: 3, second: 1 }]]);
  reject(`${rule}def t : (label : Text) -> Rule := fun (n : Nat) (label : Text) => pair n n`,
    funError, '(n : Nat) (label');
});

test('a function type of data types is in Type 0', () => {
  reject('def R : Type 1 := (n : Nat) -> Nat', universeError, '(n');
  reject(`${rule}def R : Type 1 := Rule`, universeError, 'Rule');
  reject('def R : Type 1 := WritePath', universeError, 'WritePath');
});

test('parentheses group function type names and arrow types', () => {
  const source = `${rule}def Same : Type 0 := ((Rule)) ` +
    'def Direct : Type 0 := ((n : Nat) -> Prod Nat Nat) ' +
    'def Tagged : Type 0 := (label : Text) -> (Same) ' +
    'def f : ((Same)) := fun (n : Nat) => pair n 0 ' +
    'def g : ((label : Text) -> (Rule)) := fun (label : Text) (n : Nat) => pair 1 n ' +
    'def h : Tagged := fun (label : Text) (n : Nat) => pair n n ' +
    'def d : (Direct) := fun (n : Nat) => pair 0 n ' +
    'def a : Prod Nat Nat := f 2 def b : Prod Nat Nat := g "x" 3 ' +
    'def c : Prod Nat Nat := h "y" 4 def e : Prod Nat Nat := d 5';
  assert.deepEqual(values(source), [
    ['a', { first: 2, second: 0 }], ['b', { first: 1, second: 3 }],
    ['c', { first: 4, second: 4 }], ['e', { first: 0, second: 5 }],
  ]);
  assert.deepEqual(instances(`${rule}def R : Type 0 := ${'('.repeat(511)}Rule${')'.repeat(511)}`), []);
  const exhausted = run(`${rule}def R : Type 0 := ${'('.repeat(512)}Rule${')'.repeat(512)}`);
  assert.deepEqual(Object.keys(exhausted), ['error']);
  assert.equal(exhausted.error.message, 'compiler fuel exhausted');
});

test('parentheses group WritePath in definitions and longer signatures', () => {
  const source = `${actors}def Path : Type 0 := ((WritePath)) ` +
    'def Guard : Type 0 := (head : Hash) -> (Path) ' +
    'def p : (WritePath) := fun (log : Log) (write : Write) => makeStep log (outcomeDenied none nil) ' +
    'def g : (Guard) := fun (head : Hash) (log : Log) (write : Write) => makeStep log (outcomeConflict head) ' +
    'def a : Step := p history advance def b : Step := g (hashOf "e9") history advance';
  assert.deepEqual(values(source).slice(-2),
    [['a', denied], ['b', { log: [], outcome: { tag: 'outcomeConflict', head: 'e9' } }]]);
});

test('grouping preserves function type restrictions and parameter shadowing', () => {
  reject(`${rule}def x : List ((Rule)) := nil`, dataError, 'Rule))');
  reject('def x : Option (WritePath) := none', dataError, 'WritePath');
  reject(`${rule}def f : (r : (Rule)) -> Nat := fun (r : Nat) => 1`, dataError, 'Rule))');
  reject(`${rule}def R : Type 1 := ((Rule))`, universeError, '((Rule))');
  reject(`${rule}def f : (Rule : Nat) -> (Rule) := fun (n : Nat) => n`,
    'expected a supported type', 'Rule)');
});

test('grouped function types require every closing parenthesis', () => {
  for (const type of ['(Rule', '((Rule)', '((n : Nat) -> Nat', '(WritePath']) {
    const source = `${rule}def R : Type 0 := ${type}`;
    const result = run(source);
    assert.deepEqual(Object.keys(result), ['error'], source);
    assert.equal(result.error.byte, source.length, source);
  }
});

test('a function type is not a data type', () => {
  const cases = [
    [`${rule}def x : List Rule := nil`, 'Rule :='],
    [`${rule}def x : Option Rule := none`, 'Rule :='],
    [`${rule}def P : Type 0 := Prod Rule Nat`, 'Rule Nat'],
    [`${rule}def f : (r : Rule) -> Nat := fun (r : Nat) => 1`, 'Rule)'],
    [`${rule}def e : Eq Rule 1 1 := refl`, 'Rule 1'],
    ['def x : List WritePath := nil', 'WritePath'],
    ['def f : (w : WritePath) -> Nat := fun (w : Nat) => 1', 'WritePath'],
  ];
  cases.forEach(([source, at]) => reject(source, dataError, at));
});

test('a name of a function type is not a term', () => {
  reject(`${rule}def x : Nat := Rule`, termError, 'Rule');
  reject(`${rule}def xs : List Nat := nil def ys : List (Prod Nat Nat) := map Rule xs`,
    'expected a function with one parameter', 'Rule xs');
});

test('a name of a function type is a definition name', () => {
  reject(`${rule}def Rule : Nat := 1`, 'duplicate definition name', 'Rule :');
});

test('a function of type WritePath is checked and applied', () => {
  assert.deepEqual(values(`${actors}${refuse}def s : Step := refuse history advance`).at(-1), ['s', denied]);
});

test('WritePath checks the binders and the result', () => {
  const conflict = 'makeStep log (outcomeConflict (hashOf "h"))';
  reject(`def bad : WritePath := fun (log : Log) (write : Step) => ${conflict}`, funError, '(write');
  reject(`def bad : WritePath := fun (log : Log) => ${conflict}`, funError, '=>');
  reject('def bad : WritePath := fun (log : Log) (write : Write) => log', termError, 'log');
  reject('def x : WritePath := nil', funError, 'nil');
});

test('a type definition names WritePath and a function type can end with it', () => {
  const source = `${actors}def Path : Type 0 := WritePath def Guard : Type 0 := (head : Hash) -> Path ` +
    'def p : Path := fun (log : Log) (write : Write) => makeStep log (outcomeDenied none nil) ' +
    'def g : Guard := fun (head : Hash) (log : Log) (write : Write) => makeStep log (outcomeConflict head) ' +
    'def a : Step := p history advance def b : Step := g (hashOf "e9") history advance';
  assert.deepEqual(values(source).slice(-2),
    [['a', denied], ['b', { log: [], outcome: { tag: 'outcomeConflict', head: 'e9' } }]]);
});

test('an application of a WritePath function takes both arguments', () => {
  assert.deepEqual(Object.keys(run(`${actors}${refuse}def s : Step := refuse history`)), ['error']);
});

test('ReadPath stays a type of a later milestone', () => {
  reject('def r : ReadPath := nil', laterError, 'ReadPath');
  reject('def R : Type 1 := ReadPath', laterError, 'ReadPath');
});

test('the paths example compiles to its literal steps', async () => {
  const source = await readFile(new URL('../examples/paths.ledger', import.meta.url), 'utf8');
  const found = instances(source);
  assert.deepEqual(found.map(item => item.name), ['acme', 'deal', 'advance', 'history', 'refused', 'raced']);
  assert.deepEqual(found.slice(-2), [
    { name: 'refused', type: 'Step', value: denied },
    { name: 'raced', type: 'Step', value: { log: [], outcome: { tag: 'outcomeConflict', head: 'entry-9' } } },
  ]);
});
