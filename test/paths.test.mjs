import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import test from 'node:test';
import { fileURLToPath } from 'node:url';
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
  reject(`${rule}def f : (r : (Rule)) -> Nat := fun (r : Nat) => 1`, funError, '(r : Nat)');
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
    [`${rule}def f : (r : List Rule) -> Nat := fun (r : Nat) => 1`, 'Rule)'],
    [`${rule}def e : Eq Rule 1 1 := refl`, 'Rule 1'],
    ['def x : List WritePath := nil', 'WritePath'],
    ['def f : (w : List WritePath) -> Nat := fun (w : Nat) => 1', 'WritePath'],
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

// M1 part B: the builtin write. Each hash is the SHA-256 of the compact JSON of its Entry.
const note = 'def note : Event := makeEvent eventNoteAdded (subjectParty acme) none none attrsEnd none ' +
  'def noted : Write := makeWrite (actorHuman acme) none (commandRecord note) ';
const named = source => Object.fromEntries(values(source));
const sha256 = value => createHash('sha256').update(JSON.stringify(value)).digest('hex');
const human = { tag: 'actorHuman', party: { kind: 'kindParty', hash: 'party-acme' } };
const appended = (log, entry) => ({ log, outcome: { tag: 'outcomeAppended', entries: [sha256(entry)], policy: null } });
const chained = head => 'def e1 : Entry := makeEntry none (actorHuman acme) (createsEvent note) ' +
  `def log1 : Log := cons e1 nil def next : Write := makeWrite (actorHuman acme) (some (hashOf "${head}")) ` +
  '(commandRecord note) ';

test('the builtin write is the body of a WritePath definition', () => {
  assert.deepEqual(instances('def w : WritePath := write'), []);
});

test('write of a Command with no Body gives outcomeDenied and the same log', () => {
  assert.deepEqual(values(`${actors}def s : Step := write history advance`).at(-1), ['s', denied]);
});

test('write appends one entry and gives the hash of the entry', () => {
  const { note: event, s } = named(`${actors}${note}def s : Step := write history noted`);
  const entry = { prev: null, actor: human, body: { tag: 'createsEvent', event } };
  assert.deepEqual(s, appended([entry], entry));
  assert.match(s.outcome.entries[0], /^[0-9a-f]{64}$/);
});

test('a second write gives the chain: prev is the hash of the last entry', () => {
  const { note: event, e1 } = named(`${actors}${note}${chained('h')}`);
  const head = sha256(e1);
  const { s } = named(`${actors}${note}${chained(head)}def s : Step := write log1 next`);
  const entry = { prev: head, actor: human, body: { tag: 'createsEvent', event } };
  assert.deepEqual(s, appended([e1, entry], entry));
});

test('an expect that is not the hash of the last entry gives outcomeConflict', () => {
  const { e1, s } = named(`${actors}${note}${chained('e9')}def s : Step := write log1 next`);
  assert.deepEqual(s, { log: [e1], outcome: { tag: 'outcomeConflict', head: sha256(e1) } });
});

test('an expect on an empty log gives outcomeDenied', () => {
  const guarded = 'def guarded : Write := makeWrite (actorHuman acme) (some (hashOf "entry-0")) ';
  assert.deepEqual(values(`${actors}${guarded}(commandTransition deal "won") def s : Step := write history guarded`)
    .at(-1), ['s', denied]);
  assert.deepEqual(named(`${actors}${note}${guarded}(commandRecord note) def s : Step := write history guarded`).s,
    denied);
});

test('the def form, the argument form and a write in a function body give the same Step', () => {
  const source = `${actors}${note}def w : WritePath := write ` +
    'def apply : (p : WritePath) -> (log : Log) -> (x : Write) -> Step := ' +
    'fun (p : WritePath) (log : Log) (x : Write) => p log x ' +
    'def f : (log : Log) -> Step := fun (log : Log) => write log noted def a : Step := write history noted ' +
    'def b : Step := w history noted def c : Step := apply write history noted def d : Step := f history';
  const { a, b, c, d } = named(source);
  assert.deepEqual([b, c, d], [a, a, a]);
  assert.equal(a.log.length, 1);
});

test('a binding with the name write hides the builtin', () => {
  const { noted: made, s } = named(`${actors}${note}def write : Write := noted def s : Write := write`);
  assert.deepEqual(s, made);
  reject(`${actors}def write : Write := advance def w : WritePath := write`, funError, 'write');
});

test('a wrong use of write is refused', () => {
  reject(`${actors}def s : Step := write 3`, termError, '3');
  reject(`${actors}def s : Step := write history def t : Nat := 1`, 'unknown name or constructor', 'def t');
  reject(`${actors}def w : WritePath := write history`, 'expected def NAME : TYPE := TERM', 'history');
});

test('commandResolveParty gives createsParty with empty attrs', () => {
  const { s } = named(`${actors}def who : Write := makeWrite (actorHuman acme) none ` +
    '(commandResolveParty partyOrg "Acme" nil) def s : Step := write history who');
  const party = {
    kind: 'partyOrg', displayName: 'Acme', legalName: null, identifiers: [], attrs: {}, lastEvent: null, deletedBy: null,
  };
  const entry = { prev: null, actor: human, body: { tag: 'createsParty', party } };
  assert.deepEqual(s, appended([entry], entry));
});

// M1 part C: the records of the logs. The identity of a record is the hash of its entry.
const party = 'def company : Party := makeParty partyOrg "Acme" none nil attrsEnd none none ' +
  'def pe : Entry := makeEntry none (actorHuman acme) (createsParty company) ';
const about = hash => 'def about : Event := makeEvent eventNoteAdded ' +
  `(subjectParty (refTo (hashOf "${hash}"))) none none attrsEnd none ` +
  'def ee : Entry := makeEntry none (actorHuman acme) (createsEvent about) ';
const record = (entry, type, value) => ({ ref: sha256(entry), type, value });
const partyHash = () => sha256(named(`${actors}${party}`).pe);
const projected = source => {
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['ledger-lang', 'instances', 'records'], JSON.stringify(result));
  return { ...Object.fromEntries(result.instances.map(item => [item.name, item.value])), records: result.records };
};

test('a later createsEvent entry sets lastEvent on the Party record of its subject', () => {
  const { company, about: event, pe, ee, records } =
    projected(`${actors}${party}${about(partyHash())}def book : Log := cons pe (cons ee nil)`);
  assert.deepEqual(records, [
    record(pe, 'Party', { ...company, lastEvent: { kind: 'kindEvent', hash: sha256(ee) } }),
    record(ee, 'Event', event),
  ]);
});

test('a Step from write gives the records of its log', () => {
  const { s, records } = projected(`${actors}def who : Write := makeWrite (actorHuman acme) none ` +
    '(commandResolveParty partyOrg "Acme" nil) def s : Step := write history who');
  assert.deepEqual(records, [record(s.log[0], 'Party', s.log[0].body.party)]);
  assert.equal(records[0].ref, partyHash());
});

test('an M0 program and an empty log have no records key', () => {
  assert.deepEqual(Object.keys(run(`${rule}def n : Nat := 3`)), ['ledger-lang', 'instances']);
  assert.deepEqual(Object.keys(run(`${actors}${party}def book : Log := nil`)), ['ledger-lang', 'instances']);
});

test('an event with a subject that names no record changes no record', () => {
  const { company, about: event, pe, ee, records } =
    projected(`${actors}${party}${about('nobody')}def book : Log := cons pe (cons ee nil)`);
  assert.deepEqual(records, [record(pe, 'Party', company), record(ee, 'Event', event)]);
});

test('the same entry in two logs or two times in one log is one record', () => {
  const source = `${actors}${party}${about(partyHash())}def book : Log := cons pe (cons ee nil) `;
  const { records } = projected(source);
  assert.deepEqual(projected(`${source}def copy : Log := cons ee (cons pe (cons pe nil))`).records, records);
});

test('the records follow the program order of the logs and the order of each log', () => {
  const beta = `${actors}${party}def other : Party := makeParty partyOrg "Beta" none nil attrsEnd none none ` +
    'def po : Entry := makeEntry none (actorHuman acme) (createsParty other) ';
  const refs = source => projected(source).records.map(item => item.ref);
  const { pe, po } = named(beta);
  assert.deepEqual(refs(`${beta}def book : Log := cons po (cons pe nil)`), [sha256(po), sha256(pe)]);
  assert.deepEqual(refs(`${beta}def early : Log := cons pe nil def book : Log := cons po (cons pe nil)`),
    [sha256(pe), sha256(po)]);
  const { company, about: event, ee, records } =
    projected(`${actors}${party}${about(partyHash())}def book : Log := cons ee (cons pe nil)`);
  assert.deepEqual(records, [record(ee, 'Event', event), record(pe, 'Party', company)]);
});

test('a Step from makeStep has no records and each write form gives the records of its log', () => {
  const lone = actors.replace('def history : Log := nil ', '');
  const keys = step => Object.keys(run(`${lone}${party}${note}${refuse}def s : Step := ${step}`));
  assert.deepEqual(keys('makeStep (cons pe nil) (outcomeDenied none nil)'), ['ledger-lang', 'instances']);
  assert.deepEqual(keys('refuse (cons pe nil) noted'), ['ledger-lang', 'instances']);
  const forms = `${actors}${note}def w : WritePath := write ` +
    'def apply : (p : WritePath) -> (log : Log) -> (x : Write) -> Step := ' +
    'fun (p : WritePath) (log : Log) (x : Write) => p log x ' +
    'def f : (log : Log) -> Step := fun (log : Log) => write log noted ';
  ['w history noted', 'apply write history noted', 'f history'].forEach(step => {
    const { s, records } = projected(`${forms}def s : Step := ${step}`);
    assert.deepEqual(records, [record(s.log[0], 'Event', s.log[0].body.event)], step);
  });
});

test('ReadPath is a function type in Type 1', () => {
  reject('def r : ReadPath := nil', funError, 'nil');
  reject('def R : Type 0 := ReadPath', universeError, 'ReadPath');
  assert.deepEqual(instances('def R : Type 1 := ReadPath'), []);
  assert.deepEqual(instances('def Reader : Type 1 := (head : Hash) -> ReadPath'), []);
});

const lift = 'def lift : (r : ReadPath) -> ReadPath := fun (r : ReadPath) (answer : Type 0) (log : Log) ' +
  '(query : Query answer) => r answer log query';

test('a function of type ReadPath passes the call to a ReadPath parameter', () => {
  assert.deepEqual(instances(lift), []);
  assert.deepEqual(instances('def lift : (r : ReadPath) -> ReadPath := ' +
    'fun (q : ReadPath) (T : Type 0) (l : Log) (k : Query T) => q T l k'), []);
});

test('an application of a ReadPath parameter has the type of its type argument', () => {
  const apply = 'fun (r : ReadPath) (log : Log) (ask : Query Flag) => r Flag log ask';
  assert.deepEqual(instances(`def g : (r : ReadPath) -> (log : Log) -> (ask : Query Flag) -> Flag := ${apply}`), []);
  reject(`def g : (r : ReadPath) -> (log : Log) -> (ask : Query Flag) -> Verdict := ${apply}`, termError, 'r');
  reject('def g : (r : ReadPath) -> (log : Log) -> (ask : Query Flag) -> Verdict := ' +
    'fun (r : ReadPath) (log : Log) (ask : Query Flag) => r Verdict log ask', termError, 'ask');
  assert.deepEqual(instances('def c : (answer : Type 0) -> (r : ReadPath) -> (log : Log) -> ' +
    '(ask : Query answer) -> answer := fun (T : Type 0) (r : ReadPath) (log : Log) (ask : Query T) => r T log ask'), []);
});

test('ReadPath checks the binders and the result', () => {
  reject('def lift : (r : ReadPath) -> ReadPath := fun (r : ReadPath) (answer : Type 0) (log : Nat) ' +
    '(query : Query answer) => r answer log query', funError, '(log');
  reject('def lift : (r : ReadPath) -> ReadPath := fun (r : ReadPath) (answer : Type 0) (log : Log) ' +
    '(query : Query answer) => log', termError, 'log');
  reject('def x : Option (ReadPath) := none', dataError, 'ReadPath');
  reject('def f : (w : List ReadPath) -> Nat := fun (w : Nat) => 1', dataError, 'ReadPath');
});

test('a type argument after a value argument is not read (D-B5)', () => {
  reject(`${lift} def h : (r : ReadPath) -> (log : Log) -> (ask : Query Flag) -> Flag := ` +
    'fun (r : ReadPath) (log : Log) (ask : Query Flag) => lift r Flag log ask', 'unknown name or constructor', 'Flag');
});

const readError = 'the read path does not answer this query';
const readPre = 'def deal : Ref kindCommercial := refTo (hashOf "deal-1") def history : Log := nil ' +
  'def ask : Query Flag := queryArtifactIntact (refTo (hashOf "art-1")) "d" ';

test('read is a builtin ReadPath term', () => {
  assert.deepEqual(instances('def r : ReadPath := read'), []);
});

test('a binding of read hides the builtin', () => {
  assert.deepEqual(values('def read : Nat := 3 def x : Nat := read'), [['read', 3], ['x', 3]]);
});

test('read with the answer type first checks in a function body', () => {
  assert.deepEqual(instances('def f : (log : Log) -> (q : Query Flag) -> Flag := ' +
    'fun (log : Log) (q : Query Flag) => read Flag log q'), []);
});

test('a read of a query out of the read path gives the new refusal', () => {
  reject(`${readPre}def a : Flag := read Flag history ask`, readError, 'read');
});

test('read as a ReadPath argument', () => {
  const source = `${readPre}def lift : (r : ReadPath) -> (log : Log) -> (ask : Query Flag) -> Flag := ` +
    'fun (r : ReadPath) (log : Log) (ask : Query Flag) => r Flag log ask def a : Flag := lift read history ask';
  assert.ok(Array.isArray(instances(source.slice(0, source.lastIndexOf(' def a')))));
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['error'], JSON.stringify(result));
  assert.equal(result.error.message, readError);
});

test('a wrong answer type gives term does not have the declared type', () => {
  reject(`${readPre}def a : Log := read Log history ask`, termError, 'ask');
  reject(`${readPre}def b : Flag := read Log history ask`, termError, 'read');
});

test('a wrong argument gives term does not have the declared type', () => {
  reject(`${readPre}def a : Flag := read Flag history 3`, termError, '3');
});

// M2 part B: the entry queries. A read visits each entry of the log. Each hash is the SHA-256 of the compact JSON
// of its Entry.
const entryPre = 'def acme : Ref kindParty := refTo (hashOf "party-acme") ' +
  'def beta : Ref kindParty := refTo (hashOf "party-beta") ' +
  'def n1 : Event := makeEvent eventNoteAdded (subjectParty acme) none none attrsEnd none ' +
  'def n2 : Event := makeEvent eventNoteAdded (subjectParty beta) none none attrsEnd none ' +
  'def e1 : Entry := makeEntry none (actorHuman acme) (createsEvent n1) ' +
  'def e2 : Entry := makeEntry none (actorHuman beta) (createsEvent n1) ' +
  'def e3 : Entry := makeEntry none (actorHuman acme) (createsEvent n2) ' +
  'def book : Log := cons e1 (cons e2 (cons e3 nil)) ';
const answerOf = source => named(`${entryPre}${source}`).r;
const asOf = entry => `(momentAsOf (hashOf "${sha256(entry)}"))`;

test('queryReplay at momentNow gives the full log', () => {
  const { e1, e2, e3 } = named(entryPre);
  assert.deepEqual(answerOf('def r : Log := read Log book (queryReplay momentNow)'), [e1, e2, e3]);
});

test('queryReplay as of an entry stops at that entry', () => {
  const { e1, e2 } = named(entryPre);
  assert.deepEqual(answerOf(`def r : Log := read Log book (queryReplay ${asOf(e2)})`), [e1, e2]);
  assert.deepEqual(answerOf(`def r : Log := read Log book (queryReplay ${asOf(e1)})`), [e1]);
});

test('a hash that names no entry gives nil', () => {
  assert.deepEqual(answerOf('def r : Log := read Log book (queryReplay (momentAsOf (hashOf "e9")))'), []);
  assert.deepEqual(answerOf('def r : Log := read Log book (queryTail (momentAsOf (hashOf "e9")))'), []);
});

test('queryTail gives the entries after an entry', () => {
  const { e1, e2, e3 } = named(entryPre);
  assert.deepEqual(answerOf(`def r : Log := read Log book (queryTail ${asOf(e1)})`), [e2, e3]);
  assert.deepEqual(answerOf(`def r : Log := read Log book (queryTail ${asOf(e3)})`), []);
  assert.deepEqual(answerOf('def r : Log := read Log book (queryTail momentNow)'), []);
});

test('queryAuditByActor lists the events of one actor', () => {
  const { e1, e2, e3 } = named(entryPre);
  const party = 'def company : Party := makeParty partyOrg "Acme" none nil attrsEnd none none ' +
    'def e4 : Entry := makeEntry none (actorHuman acme) (createsParty company) def all : Log := cons e4 book ';
  const audit = actor => answerOf(`${party}def r : List (Ref kindEvent) := ` +
    `read (List (Ref kindEvent)) all (queryAuditByActor (actorHuman ${actor}))`);
  const ref = entry => ({ kind: 'kindEvent', hash: sha256(entry) });
  assert.deepEqual(audit('acme'), [ref(e1), ref(e3)]);
  assert.deepEqual(audit('beta'), [ref(e2)]);
});

test('a Log answer makes no second record of an entry', () => {
  const { records } = run(entryPre);
  assert.equal(records.length, 3);
  assert.deepEqual(run(`${entryPre}def r : Log := read Log book (queryReplay momentNow)`).records, records);
});

const recordPre = 'def acme : Ref kindParty := refTo (hashOf "party-acme") ' +
  'def plan : Commercial := makeCommercial commercialDeal "Annual plan" acme "negotiation" (some 250000) "USD" ' +
  '(some "2026-12-01") statusOpen attrsEnd none ' +
  'def other : Commercial := makeCommercial commercialDeal "Second plan" acme "negotiation" none "USD" none ' +
  'statusOpen attrsEnd none ' +
  'def ce : Entry := makeEntry none (actorHuman acme) (createsCommercial plan) ' +
  'def oe : Entry := makeEntry none (actorHuman acme) (createsCommercial other) ';
const dealOf = entry => `(refTo (hashOf "${sha256(entry)}"))`;
const recordLog = () => `${recordPre}def note : Event := makeEvent eventNoteAdded ` +
  `(subjectCommercial ${dealOf(named(recordPre).ce)}) none none attrsEnd none ` +
  'def ne : Entry := makeEntry none (actorHuman acme) (createsEvent note) ' +
  'def book : Log := cons ce (cons oe (cons ne nil)) ';
const recordOf = source => named(`${recordLog()}${source}`).r;
const commercialOf = (deal, moment) =>
  recordOf(`def r : Option Commercial := read (Option Commercial) book (queryCommercial ${deal} ${moment})`);
const soundOf = (deal, stored) => recordOf(`def r : Flag := read Flag book (queryProjectionSound ${deal} ${stored})`);

test('queryCommercial at momentNow gives the record with lastEvent', () => {
  const { plan, other, ce, oe, ne } = named(recordLog());
  assert.deepEqual(commercialOf(dealOf(ce), 'momentNow'), { ...plan, lastEvent: { kind: 'kindEvent', hash: sha256(ne) } });
  assert.deepEqual(commercialOf(dealOf(oe), 'momentNow'), other);
});

test('queryCommercial as of the creating entry gives lastEvent none', () => {
  const { plan, ce, oe } = named(recordLog());
  assert.deepEqual(commercialOf(dealOf(ce), asOf(ce)), plan);
  assert.deepEqual(commercialOf(dealOf(ce), asOf(oe)), plan);
});

test('queryCommercial of an unknown ref gives none', () => {
  const { ce, ne } = named(recordLog());
  assert.equal(commercialOf('(refTo (hashOf "e9"))', 'momentNow'), null);
  assert.equal(commercialOf(dealOf(ne), 'momentNow'), null);
  assert.equal(commercialOf(dealOf(ce), '(momentAsOf (hashOf "e9"))'), null);
});

// M3 part A: the Commitment queries. The log: a deal with amountCents cents, a commitmentPrice 1000
// commitmentProposed, a commitmentPrice agreed commitmentAgreed that supersedes it, and a commitmentTerm.
const termPre = cents => 'def acme : Ref kindParty := refTo (hashOf "party-acme") ' +
  'def evidence : Ref kindArtifact := refTo (hashOf "email-entry") ' +
  'def provenance : Provenance := makeProvenance (some evidence) none (some 95) ' +
  `def plan : Commercial := makeCommercial commercialDeal "Annual plan" acme "negotiation" (some ${cents}) "USD" ` +
  'none statusOpen attrsEnd none def ce : Entry := makeEntry none (actorHuman acme) (createsCommercial plan) ';
const commitmentOf = (deal, kind, value, status, supersedes) =>
  `makeCommitment ${deal} ${kind} "Term" ${value} none ${status} ${supersedes} provenance`;
const termLog = (cents, agreed = 900) => {
  const pre = termPre(cents);
  const deal = dealOf(named(pre).ce);
  const proposed = `${pre}def proposed : Commitment := ` +
    `${commitmentOf(deal, 'commitmentPrice', '(valueNat 1000)', 'commitmentProposed', 'none')} ` +
    'def pe : Entry := makeEntry none (actorHuman acme) (createsCommitment proposed) ';
  const older = `(some (refTo (hashOf "${sha256(named(proposed).pe)}")))`;
  return `${proposed}def agreed : Commitment := ` +
    `${commitmentOf(deal, 'commitmentPrice', `(valueNat ${agreed})`, 'commitmentAgreed', older)} ` +
    'def ae : Entry := makeEntry none (actorHuman acme) (createsCommitment agreed) ' +
    `def term : Commitment := ${commitmentOf(deal, 'commitmentTerm', '(valueText "net_30")', 'commitmentProposed', 'none')} ` +
    'def te : Entry := makeEntry none (actorHuman acme) (createsCommitment term) ' +
    'def book : Log := cons ce (cons pe (cons ae (cons te nil))) ';
};
const termAnswer = (log, type, query) => {
  const wrapped = type.includes(' ') ? `(${type})` : type;
  return named(`${log}def r : ${type} := read ${wrapped} book (${query})`).r;
};
const termRef = entry => ({ kind: 'kindCommitment', hash: sha256(entry) });
const refs = 'List (Ref kindCommitment)';

test('queryTermsInForce lists the terms that no entry supersedes', () => {
  const log = termLog(900);
  const { ce, ae, te } = named(log);
  assert.deepEqual(termAnswer(log, refs, `queryTermsInForce ${dealOf(ce)} momentNow`), [termRef(ae), termRef(te)]);
});

test('queryTermsInForce as of an entry stops at that entry', () => {
  const log = termLog(900);
  const { ce, pe } = named(log);
  assert.deepEqual(termAnswer(log, refs, `queryTermsInForce ${dealOf(ce)} ${asOf(pe)}`), [termRef(pe)]);
});

test('queryTermHistory gives the chain oldest first', () => {
  const log = termLog(900);
  const { pe, ae } = named(log);
  assert.deepEqual(termAnswer(log, refs, `queryTermHistory (refTo (hashOf "${sha256(ae)}"))`), [termRef(pe), termRef(ae)]);
});

test('queryAmountReconciled gives flagYes on the agreed price', () => {
  const log = termLog(900);
  assert.equal(termAnswer(log, 'Flag', `queryAmountReconciled ${dealOf(named(log).ce)}`), true);
});

test('queryAmountReconciled gives flagNo on the superseded price', () => {
  const log = termLog(1000);
  assert.equal(termAnswer(log, 'Flag', `queryAmountReconciled ${dealOf(named(log).ce)}`), false);
});

test('queryDiscountPct gives the percent rounded down', () => {
  const even = termLog(900);
  assert.equal(termAnswer(even, 'Option Nat', `queryDiscountPct ${dealOf(named(even).ce)}`), 10);
  const odd = termLog(905, 905);
  assert.equal(termAnswer(odd, 'Option Nat', `queryDiscountPct ${dealOf(named(odd).ce)}`), 9);
});

test('queryDiscountPct gives none with no agreed price', () => {
  const log = termLog(900);
  const twoEntries = `${log.slice(0, log.indexOf('def agreed'))}def book : Log := cons ce (cons pe nil) `;
  assert.equal(termAnswer(twoEntries, 'Option Nat', `queryDiscountPct ${dealOf(named(log).ce)}`), null);
});

// M3 part B: the Membership queries. The log: p1 at orgB (not primary), p1 at orgA (primary), p2 at orgA
// (ended by an event), p2 at orgB (not primary), in this order.
const memberPre = 'def p1 : Ref kindParty := refTo (hashOf "party-p1") ' +
  'def p2 : Ref kindParty := refTo (hashOf "party-p2") ' +
  'def orgA : Ref kindParty := refTo (hashOf "party-org-a") ' +
  'def orgB : Ref kindParty := refTo (hashOf "party-org-b") ' +
  'def evidence : Ref kindArtifact := refTo (hashOf "email-entry") ' +
  'def provenance : Provenance := makeProvenance (some evidence) none (some 95) ';
const memberOf = (membership, entry, person, org, primary, endedBy) =>
  `def ${membership} : Membership := makeMembership ${person} ${org} none ${primary} ${endedBy} provenance attrsEnd ` +
  `def ${entry} : Entry := makeEntry none (actorHuman ${person}) (createsMembership ${membership}) `;
const memberLog = memberPre + memberOf('m1', 'e1', 'p1', 'orgB', 'flagNo', 'none') +
  memberOf('m2', 'e2', 'p1', 'orgA', 'flagYes', 'none') +
  memberOf('m3', 'e3', 'p2', 'orgA', 'flagNo', '(some (refTo (hashOf "left-a")))') +
  memberOf('m4', 'e4', 'p2', 'orgB', 'flagNo', 'none') +
  'def book : Log := cons e1 (cons e2 (cons e3 (cons e4 nil))) ';
const memberRef = entry => ({ kind: 'kindMembership', hash: sha256(entry) });
const partyRef = hash => ({ kind: 'kindParty', hash });
const memberRefs = 'List (Ref kindMembership)';
const employer = 'Option (Ref kindParty)';
const parties = 'List (Ref kindParty)';

test('queryMembersOf lists the current memberships of an org', () => {
  const { e2 } = named(memberLog);
  assert.deepEqual(termAnswer(memberLog, memberRefs, 'queryMembersOf orgA momentNow'), [memberRef(e2)]);
});

test('queryMembersOf as of an entry stops at that entry', () => {
  const { e1 } = named(memberLog);
  assert.deepEqual(termAnswer(memberLog, memberRefs, `queryMembersOf orgB ${asOf(e1)}`), [memberRef(e1)]);
  assert.deepEqual(termAnswer(memberLog, memberRefs, `queryMembersOf orgA ${asOf(e1)}`), []);
});

test('queryEmployer gives the primary org', () => {
  assert.deepEqual(termAnswer(memberLog, employer, 'queryEmployer p1 momentNow'), partyRef('party-org-a'));
});

test('queryEmployer gives the first current org with no primary', () => {
  assert.deepEqual(termAnswer(memberLog, employer, 'queryEmployer p2 momentNow'), partyRef('party-org-b'));
});

test('queryEmployer of a party with no current membership gives none', () => {
  assert.equal(termAnswer(memberLog, employer, 'queryEmployer (refTo (hashOf "party-p3")) momentNow'), null);
});

test('queryJobChanges lists the persons after an entry and nil at momentNow', () => {
  const { e1 } = named(memberLog);
  assert.deepEqual(termAnswer(memberLog, parties, `queryJobChanges ${asOf(e1)}`),
    [partyRef('party-p1'), partyRef('party-p2'), partyRef('party-p2')]);
  assert.deepEqual(termAnswer(memberLog, parties, 'queryJobChanges momentNow'), []);
});

test('queryProjectionSound gives flagYes on the replayed state', () => {
  const { ce, ne } = named(recordLog());
  const replayed = 'def replayed : Commercial := makeCommercial commercialDeal "Annual plan" acme "negotiation" ' +
    `(some 250000) "USD" (some "2026-12-01") statusOpen attrsEnd (some (refTo (hashOf "${sha256(ne)}"))) `;
  assert.equal(named(`${recordLog()}${replayed}def r : Flag := ` +
    `read Flag book (queryProjectionSound ${dealOf(ce)} replayed)`).r, true);
});

test('queryProjectionSound gives flagNo on another state', () => {
  const { ce, oe } = named(recordLog());
  assert.equal(soundOf(dealOf(ce), 'plan'), false);
  assert.equal(soundOf(dealOf(oe), 'plan'), false);
  assert.equal(soundOf('(refTo (hashOf "e9"))', 'other'), false);
});

// M4 part A: the pipeline queries. The log: a Party, then three deals (qualify with some 1000 and some "2026-11-01",
// qualify with none and none, propose with some 500 and some "2026-11-01"). stageLog adds an eventStageChanged of
// the first deal (qualify to propose) and an eventNoteAdded of the second deal.
const pipePre = 'def acme : Ref kindParty := refTo (hashOf "party-acme") ' +
  'def company : Party := makeParty partyOrg "Acme" none nil attrsEnd none none ' +
  'def pe : Entry := makeEntry none (actorHuman acme) (createsParty company) ' +
  'def d1 : Commercial := makeCommercial commercialDeal "First" acme "qualify" (some 1000) "USD" (some "2026-11-01") ' +
  'statusOpen attrsEnd none def e1 : Entry := makeEntry none (actorHuman acme) (createsCommercial d1) ' +
  'def d2 : Commercial := makeCommercial commercialDeal "Second" acme "qualify" none "USD" none ' +
  'statusOpen attrsEnd none def e2 : Entry := makeEntry none (actorHuman acme) (createsCommercial d2) ' +
  'def d3 : Commercial := makeCommercial commercialDeal "Third" acme "propose" (some 500) "USD" (some "2026-11-01") ' +
  'statusOpen attrsEnd none def e3 : Entry := makeEntry none (actorHuman acme) (createsCommercial d3) ';
const pipeLog = `${pipePre}def book : Log := cons pe (cons e1 (cons e2 (cons e3 nil))) `;
const stageLog = () => {
  const { e1, e2 } = named(pipePre);
  return `${pipePre}def move : Event := makeEvent eventStageChanged (subjectCommercial ${dealOf(e1)}) none none ` +
    '(attrsField "before" (valueText "qualify") (attrsField "after" (valueText "propose") attrsEnd)) none ' +
    'def me : Entry := makeEntry none (actorHuman acme) (createsEvent move) ' +
    `def note : Event := makeEvent eventNoteAdded (subjectCommercial ${dealOf(e2)}) none none attrsEnd none ` +
    'def ne : Entry := makeEntry none (actorHuman acme) (createsEvent note) ' +
    'def book : Log := cons pe (cons e1 (cons e2 (cons e3 (cons me (cons ne nil))))) ';
};
const bucketOf = (key, count, amountCents) => ({ key, count, amountCents });
const pipelineOf = (key, moment) => termAnswer(pipeLog, 'List Bucket', `queryPipeline ${key} ${moment}`);
const staleOf = (log, quiet) => termAnswer(log, 'List (Ref kindCommercial)', `queryStaleDeals ${quiet}`);
const dealRef = entry => ({ kind: 'kindCommercial', hash: sha256(entry) });

test('queryPipeline by stage groups the deals and sums amountCents', () => {
  assert.deepEqual(pipelineOf('pipelineByStage', 'momentNow'), [bucketOf('qualify', 2, 1000), bucketOf('propose', 1, 500)]);
});

test('queryPipeline by close date groups by expectedCloseOn with the empty key for none', () => {
  assert.deepEqual(pipelineOf('pipelineByCloseDate', 'momentNow'), [bucketOf('2026-11-01', 2, 1500), bucketOf('', 1, 0)]);
});

test('queryPipeline as of an entry stops at that entry', () => {
  assert.deepEqual(pipelineOf('pipelineByStage', asOf(named(pipeLog).e1)), [bucketOf('qualify', 1, 1000)]);
});

test('queryPipeline by owner keeps the refusal', () => {
  reject(`${pipeLog}def r : List Bucket := read (List Bucket) book (queryPipeline pipelineByOwner momentNow)`, readError, 'read');
});

test('queryStageStats counts entered, advanced and the entries in each stage', () => {
  const stat = (stage, entered, advanced, entriesInStage) => ({ stage, entered, advanced, entriesInStage });
  assert.deepEqual(termAnswer(stageLog(), 'List StageStat', 'queryStageStats'), [stat('qualify', 0, 1, 7), stat('propose', 1, 0, 5)]);
});

test('queryStaleDeals lists the deals with no entry in the last q entries', () => {
  const log = stageLog();
  const { e1, e3 } = named(log);
  assert.deepEqual(staleOf(log, 1), [dealRef(e1), dealRef(e3)]);
});

test('queryStaleDeals 0 lists every deal and the log length gives nil', () => {
  const { e1, e2, e3 } = named(pipeLog);
  assert.deepEqual(staleOf(pipeLog, 0), [dealRef(e1), dealRef(e2), dealRef(e3)]);
  assert.deepEqual(staleOf(pipeLog, 4), []);
});

test('queryStaleDeals counts the last event of a deal', () => {
  const log = stageLog();
  const { e1, e3 } = named(log);
  assert.deepEqual(staleOf(pipeLog, 2), [dealRef(e1)]);
  assert.deepEqual(staleOf(log, 2), [dealRef(e3)]);
});

// M4 part B: the account queries. The log: the Party records acme and beta (orgs) and pat (a person) (entries 0 to 2);
// the deal d1 of acme (3) and the deal d2 of beta (4); a commitmentDate "2027-01-31" commitmentAgreed of d1 (5), a
// commitmentTerm of d1 (6), a commitmentDate "2027-03-31" commitmentProposed of d2 (7), a commitmentDate "2027-06-30"
// commitmentAgreed of d2 that supersedes entry 7 (8); a current Membership of pat at acme (9), an ended Membership of
// another person at acme (10), an Assignment roleOwner of acme (11), an Artifact of d1 (12), an Event of d1 (13) and an
// Event of beta (14). Each stage names the entry hashes of the stage before it.
const accountPre = 'def who : Ref kindParty := refTo (hashOf "party-who") ' +
  'def evidence : Ref kindArtifact := refTo (hashOf "email-entry") ' +
  'def provenance : Provenance := makeProvenance (some evidence) none (some 95) ' +
  'def acmeParty : Party := makeParty partyOrg "Acme" none nil attrsEnd none none ' +
  'def pa : Entry := makeEntry none (actorHuman who) (createsParty acmeParty) ' +
  'def betaParty : Party := makeParty partyOrg "Beta" none nil attrsEnd none none ' +
  'def pb : Entry := makeEntry none (actorHuman who) (createsParty betaParty) ' +
  'def patParty : Party := makeParty partyPerson "Pat" none nil attrsEnd none none ' +
  'def pp : Entry := makeEntry none (actorHuman who) (createsParty patParty) ';
const accountDeals = () => {
  const { pa, pb, pp } = named(accountPre);
  return `${accountPre}def acme : Ref kindParty := ${dealOf(pa)} def beta : Ref kindParty := ${dealOf(pb)} ` +
    `def pat : Ref kindParty := ${dealOf(pp)} ` +
    'def d1 : Commercial := makeCommercial commercialDeal "First" acme "qualify" (some 1000) "USD" none statusOpen ' +
    'attrsEnd none def ce1 : Entry := makeEntry none (actorHuman who) (createsCommercial d1) ' +
    'def d2 : Commercial := makeCommercial commercialDeal "Second" beta "qualify" (some 500) "USD" none statusOpen ' +
    'attrsEnd none def ce2 : Entry := makeEntry none (actorHuman who) (createsCommercial d2) ';
};
const accountDates = () => {
  const pre = accountDeals();
  const { ce1, ce2 } = named(pre);
  return `${pre}def dealA : Ref kindCommercial := ${dealOf(ce1)} def dealB : Ref kindCommercial := ${dealOf(ce2)} ` +
    `def dateA : Commitment := ${commitmentOf('dealA', 'commitmentDate', '(valueText "2027-01-31")', 'commitmentAgreed', 'none')} ` +
    'def ca : Entry := makeEntry none (actorHuman who) (createsCommitment dateA) ' +
    `def termA : Commitment := ${commitmentOf('dealA', 'commitmentTerm', '(valueText "net_30")', 'commitmentAgreed', 'none')} ` +
    'def ta : Entry := makeEntry none (actorHuman who) (createsCommitment termA) ' +
    `def dateB : Commitment := ${commitmentOf('dealB', 'commitmentDate', '(valueText "2027-03-31")', 'commitmentProposed', 'none')} ` +
    'def cb : Entry := makeEntry none (actorHuman who) (createsCommitment dateB) ';
};
const accountLog = () => {
  const pre = accountDates();
  const older = `(some ${dealOf(named(pre).cb)})`;
  return `${pre}def dateC : Commitment := ` +
    `${commitmentOf('dealB', 'commitmentDate', '(valueText "2027-06-30")', 'commitmentAgreed', older)} ` +
    'def cc : Entry := makeEntry none (actorHuman who) (createsCommitment dateC) ' +
    'def current : Membership := makeMembership pat acme none flagYes none provenance attrsEnd ' +
    'def me : Entry := makeEntry none (actorHuman who) (createsMembership current) ' +
    'def ended : Membership := makeMembership (refTo (hashOf "party-sam")) acme none flagNo ' +
    '(some (refTo (hashOf "left-acme"))) provenance attrsEnd ' +
    'def ee : Entry := makeEntry none (actorHuman who) (createsMembership ended) ' +
    'def owner : Assignment := makeAssignment (accountParty acme) who roleOwner none none provenance ' +
    'def oe : Entry := makeEntry none (actorHuman who) (createsAssignment owner) ' +
    'def mail : Artifact := makeArtifact artifactEmail "abc123" "s3://mail/1" "message/rfc822" ' +
    '(cons (accountCommercial dealA) nil) attrsEnd ' +
    'def ae : Entry := makeEntry none (actorHuman who) (createsArtifact mail) ' +
    'def dealNote : Event := makeEvent eventNoteAdded (subjectCommercial dealA) none none attrsEnd none ' +
    'def ve : Entry := makeEntry none (actorHuman who) (createsEvent dealNote) ' +
    'def partyNote : Event := makeEvent eventNoteAdded (subjectParty beta) none none attrsEnd none ' +
    'def ne : Entry := makeEntry none (actorHuman who) (createsEvent partyNote) ' +
    'def book : Log := cons pa (cons pb (cons pp (cons ce1 (cons ce2 (cons ca (cons ta (cons cb (cons cc (cons me ' +
    '(cons ee (cons oe (cons ae (cons ve (cons ne nil)))))))))))))) ';
};
const accountRef = (kind, entry) => ({ kind, hash: sha256(entry) });
const renewalOf = (deal, date, term) => ({ commercial: dealRef(deal), date, term });
const renewalsOf = log => termAnswer(log, 'List Renewal', 'queryRenewals');
const accountOf = (log, moment) => named(`${log}def r : Account360 := read Account360 book (queryAccount360 acme ${moment})`);

test('queryRenewals lists the in-force date commitment of each deal with its term', () => {
  const log = accountLog();
  const { ce1, ce2, ta } = named(log);
  assert.deepEqual(renewalsOf(log), [renewalOf(ce1, '2027-01-31', termRef(ta)), renewalOf(ce2, '2027-06-30', null)]);
});

test('queryRenewals skips a superseded date', () => {
  const dates = `${accountDates()}def book : Log := cons pa (cons pb (cons pp (cons ce1 (cons ce2 (cons ca ` +
    '(cons ta (cons cb nil))))))) ';
  const { ce1, ce2, ta } = named(dates);
  assert.deepEqual(renewalsOf(dates), [renewalOf(ce1, '2027-01-31', termRef(ta)), renewalOf(ce2, '2027-03-31', null)]);
  assert.deepEqual(renewalsOf(accountLog())[1], renewalOf(ce2, '2027-06-30', null));
});

test('queryAccount360 gives the party record and its current memberships', () => {
  const { r, acmeParty, me } = accountOf(accountLog(), 'momentNow');
  assert.deepEqual(r.party, acmeParty);
  assert.deepEqual(r.memberships, [accountRef('kindMembership', me)]);
});

test('queryAccount360 lists the commercials, assignments, artifacts and timeline of the party', () => {
  const { r, ce1, oe, ae, ve } = accountOf(accountLog(), 'momentNow');
  assert.deepEqual(r.commercials, [dealRef(ce1)]);
  assert.deepEqual(r.assignments, [accountRef('kindAssignment', oe)]);
  assert.deepEqual(r.artifacts, [accountRef('kindArtifact', ae)]);
  assert.deepEqual(r.timeline, [accountRef('kindEvent', ve)]);
});

test('queryAccount360 as of an entry stops at that entry', () => {
  const log = accountLog();
  const { r, acmeParty, ce1 } = accountOf(log, asOf(named(log).ce1));
  assert.deepEqual(r, { party: acmeParty, memberships: [], commercials: [dealRef(ce1)], assignments: [], artifacts: [],
    timeline: [] });
});

test('queryAccount360 of an unknown party keeps the refusal', () => {
  const log = accountLog();
  const read = party => `${log}def r : Account360 := read Account360 book (queryAccount360 ${party} momentNow)`;
  reject(read('(refTo (hashOf "party-none"))'), readError, 'read');
  reject(read(dealOf(named(log).ce1)), readError, 'read');
});

// M4 part C: the review queue (delta C-1). The log: a Membership with confidence some 40 (entry 0), a Membership with
// confidence none (1), a Commercial (2; no provenance), a Commitment of it with some 50 (3) and an Assignment with some 80
// (4).
const reviewPre = 'def who : Ref kindParty := refTo (hashOf "party-who") ' +
  'def acme : Ref kindParty := refTo (hashOf "party-acme") ' +
  'def evidence : Ref kindArtifact := refTo (hashOf "email-entry") ' +
  'def low : Provenance := makeProvenance (some evidence) none (some 40) ' +
  'def unscored : Provenance := makeProvenance (some evidence) none none ' +
  'def provenance : Provenance := makeProvenance (some evidence) none (some 50) ' +
  'def high : Provenance := makeProvenance (some evidence) none (some 80) ' +
  'def lowJob : Membership := makeMembership who acme none flagYes none low attrsEnd ' +
  'def lj : Entry := makeEntry none (actorHuman who) (createsMembership lowJob) ' +
  'def openJob : Membership := makeMembership (refTo (hashOf "party-sam")) acme none flagNo none unscored attrsEnd ' +
  'def oj : Entry := makeEntry none (actorHuman who) (createsMembership openJob) ' +
  'def d1 : Commercial := makeCommercial commercialDeal "First" acme "qualify" (some 1000) "USD" none statusOpen ' +
  'attrsEnd none def ce : Entry := makeEntry none (actorHuman who) (createsCommercial d1) ';
const reviewLog = () => {
  const { ce } = named(reviewPre);
  return `${reviewPre}def dealOne : Ref kindCommercial := ${dealOf(ce)} ` +
    `def netTerm : Commitment := ${commitmentOf('dealOne', 'commitmentTerm', '(valueText "net_30")', 'commitmentAgreed', 'none')} ` +
    'def te : Entry := makeEntry none (actorHuman who) (createsCommitment netTerm) ' +
    'def owner : Assignment := makeAssignment (accountParty acme) who roleOwner none none high ' +
    'def oe : Entry := makeEntry none (actorHuman who) (createsAssignment owner) ' +
    'def book : Log := cons lj (cons oj (cons ce (cons te (cons oe nil)))) ';
};
const reviewOf = (log, below) => named(`${log}def r : List Hash := read (List Hash) book (queryReviewQueue ${below})`).r;

test('queryReviewQueue lists the records below the threshold in log order', () => {
  const log = reviewLog();
  const { lj, te, oe } = named(log);
  assert.deepEqual(reviewOf(log, 51), [sha256(lj), sha256(te)]);
  assert.deepEqual(reviewOf(log, 100), [sha256(lj), sha256(te), sha256(oe)]);
});

test('queryReviewQueue does not list a record at the threshold', () => {
  const log = reviewLog();
  assert.deepEqual(reviewOf(log, 50), [sha256(named(log).lj)]);
  assert.deepEqual(reviewOf(log, 40), []);
  assert.deepEqual(reviewOf(log, 0), []);
});

test('queryReviewQueue skips a record with no confidence', () => {
  const log = reviewLog();
  const { oj, ce } = named(log);
  const listed = reviewOf(log, 100);
  assert.ok(!listed.includes(sha256(oj)) && !listed.includes(sha256(ce)));
  assert.deepEqual(reviewOf(`${reviewPre}def book : Log := cons oj (cons ce nil) `, 100), []);
});

test('an M1 program keeps its records key', () => {
  const { ce } = named(recordLog());
  const { records } = run(recordLog());
  assert.deepEqual(records.map(record => record.type), ['Commercial', 'Commercial', 'Event']);
  assert.deepEqual(records.find(record => record.ref === sha256(ce)).value, commercialOf(dealOf(ce), 'momentNow'));
  assert.deepEqual(run(`${recordLog()}def r : Flag := read Flag book (queryProjectionSound ${dealOf(ce)} plan)`).records,
    records);
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

// M5 part A (items 0a, 0b and 3b): the bench log of N entries from build/bench-gen,
// and the SHA-256 of a bridge output with the final newline of the CLI output
// (`ledgerc <path>`, the form of the A1 digests; the `--stdin` output has none).
const benchLog = count => {
  const made = spawnSync(fileURLToPath(new URL('../build/bench-gen', import.meta.url)), [String(count)],
    { maxBuffer: 64 * 1024 * 1024 });
  assert.equal(made.status, 0, String(made.stderr));
  return made.stdout;
};
const digest = output => createHash('sha256').update(`${output}\n`).digest('hex');

test('m5 source limit', () => {
  const limit = 8_388_608;
  const source = 'def n : Nat := 7';
  const padded = source + ' '.repeat(limit - source.length);
  assert.equal(encoder.encode(padded).length, limit);
  assert.deepEqual(instances(padded).map(item => item.name), ['n']);
  assert.throws(() => run(`${padded} `), { message: `source exceeds ${limit} bytes` });
});

// The output of the b8ccdc5 ledgerc on the bench log of 64 entries.
test('m5 cons chain keeps the bytes', () => {
  assert.equal(digest(compile(benchLog(64))), '4423dabd8b0a2379506f5eee9030059bcc6c520567c5453fddb039a30c5bde60');
});

// The output of the ledgerc after items 0a to 0d, before item 2, on the bench
// log of 1000 entries.
test('m5 long log keeps the answers', () => {
  const output = compile(benchLog(1000));
  assert.equal(JSON.parse(output)['ledger-lang'], 1);
  assert.equal(digest(output), '3a0490a1d33a1c64272d3c0950284f33d1e552237fe551858726b1f45f42d502');
});
