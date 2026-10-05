import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import test from 'node:test';
import { createCompiler } from '../bin/bridge.mjs';

const compile = await createCompiler();
const encoder = new TextEncoder();
const run = source => JSON.parse(compile(encoder.encode(source)));
const accept = source => {
  const result = run(source);
  assert.equal(result['ledger-lang'], 1, JSON.stringify({ source, result }));
  return result.instances;
};
const reject = source => {
  const result = run(source);
  assert.deepEqual(Object.keys(result), ['error'], source);
  return result.error;
};

// Read the core files, never the compiler metadata. A change of a family,
// constructor, field name, field order or type in core/ops.mech changes the
// cases below.
const load = async path => (await readFile(new URL(path, import.meta.url), 'utf8')).replace(/--[^\n]*/g, '');
const families = new Map();
function readFamilies(source) {
  const found = [];
  for (const block of source.split(/^(?:mu|and) /m).slice(1)) {
    const [header, ...declarations] = block.split(/^\| /m);
    const family = header.match(/^\w+/)[0];
    families.set(family, declarations.map(raw => {
      const declaration = raw.split(/^def /m)[0];
      const name = declaration.match(/^\w+/)[0];
      const parts = declaration.slice(declaration.indexOf(':') + 1).split(/\s+->\s+/);
      const result = parts.pop().trim();
      // Query is an indexed family of a later milestone. Only its names are used.
      if (family === 'Query') return { name, fields: [] };
      assert.match(result, new RegExp(`^${family}(?:\\s+\\w+)?$`));
      return { name, fields: parts.map(part => {
        const match = part.trim().match(/^\((\w+)\s*:\s*(.+)\)$/s);
        assert.ok(match, part);
        return { name: match[1], type: match[2].trim() };
      }) };
    }));
    found.push(family);
  }
  return found;
}
readFamilies(await load('../core/schema.mech'));
const operations = readFamilies(await load('../core/ops.mech'));
const dataFamilies = operations.filter(family => family !== 'Query');
const kinds = families.get('Kind').map(constructor => constructor.name);

function typeShape(type) {
  let unwrapped = type.trim();
  while (unwrapped.startsWith('(') && unwrapped.endsWith(')')) unwrapped = unwrapped.slice(1, -1).trim();
  const [head, ...tail] = unwrapped.split(/\s+/);
  return [head, tail.join(' ')];
}

let serial = 0;
function sample(type, badRefs = false) {
  const [head, tail] = typeShape(type);
  const id = ++serial;
  const text = `field-${id}`;
  const literal = JSON.stringify(text);
  switch (head) {
    case 'Nat': return { term: String(id), value: id };
    case 'Text': return { term: literal, value: text };
    case 'Flag': return { term: id % 2 ? 'flagYes' : 'flagNo', value: Boolean(id % 2) };
    case 'Kind': return { term: kinds[id % kinds.length], value: kinds[id % kinds.length] };
    case 'Hash': return { term: `hashOf ${literal}`, value: text };
    case 'Ref': return {
      term: badRefs ? `wrong${tail}` : `refTo (hashOf ${literal})`,
      value: { kind: tail, hash: text },
    };
    case 'Value': return { term: `valueText ${literal}`, value: text };
    case 'Values': return { term: `valuesItem (valueText ${literal}) valuesEnd`, value: [text] };
    case 'Attrs': return { term: `attrsField ${literal} (valueNat ${id}) attrsEnd`, value: { [text]: id } };
    case 'Log': return sample('List Entry', badRefs);
    case 'Option': {
      const child = sample(tail, badRefs);
      const [inner] = typeShape(tail);
      return { term: `some (${child.term})`, value: ['Option', 'Value'].includes(inner) ? { some: child.value } : child.value };
    }
    case 'List': {
      const child = sample(tail, badRefs);
      return { term: `cons (${child.term}) nil`, value: [child.value] };
    }
    default: {
      const constructors = families.get(head);
      assert.ok(constructors, type);
      return construct(head, constructors[id % constructors.length]);
    }
  }
}

function construct(family, constructor) {
  const args = constructor.fields.map(field => sample(field.type));
  const fields = Object.fromEntries(constructor.fields.map((field, index) => [field.name, args[index].value]));
  const constructors = families.get(family);
  const value = constructors.every(item => item.fields.length === 0) ? constructor.name
    : constructors.length === 1 ? fields : { tag: constructor.name, ...fields };
  const term = [constructor.name, ...args.map(arg => `(${arg.term})`)].join(' ');
  return { term, value, args };
}

const wrongRefs = kinds.map((kind, index) =>
  `def wrong${kind} : Ref ${kinds[(index + 1) % kinds.length]} := refTo (hashOf "wrong")`).join('\n');

for (const family of dataFamilies) {
  for (const constructor of families.get(family)) {
    test(`operation ${family}.${constructor.name}: fields, order, types, and arity`, () => {
      const fixture = construct(family, constructor);
      const source = `def result : ${family} := ${fixture.term}`;
      const instances = accept(source);
      assert.deepEqual(instances, [{ name: 'result', type: family, value: fixture.value }]);
      // Object equality alone would not detect a change in field order.
      assert.equal(JSON.stringify(instances[0].value), JSON.stringify(fixture.value));
      reject(`${source} 0`);
      for (let index = 0; index < constructor.fields.length; index++) {
        const field = constructor.fields[index];
        const args = fixture.args.map(arg => `(${arg.term})`);
        args[index] = field.type === 'Nat' ? '"wrong"' : '0';
        reject(`def result : ${family} := ${constructor.name} ${args.join(' ')}`);
        if (/\bRef\b/.test(field.type)) {
          args[index] = `(${sample(field.type, true).term})`;
          reject(`${wrongRefs}\ndef result : ${family} := ${constructor.name} ${args.join(' ')}`);
        }
      }
      if (fixture.args.length) {
        reject(`def result : ${family} := ${constructor.name} ${fixture.args.slice(0, -1).map(arg => `(${arg.term})`).join(' ')}`);
      }
    });
  }
}

test('core/ops.mech has the expected operation families', () => {
  assert.deepEqual(operations, ['Moment', 'Missing', 'Verdict', 'Command', 'Write', 'Outcome', 'Step',
    'PipelineKey', 'Bucket', 'StageStat', 'Renewal', 'Account360', 'Query']);
  assert.equal(families.get('Command').length, 28);
  assert.equal(families.get('Query').length, 29);
});

test('Log is an alias of List Entry', () => {
  assert.deepEqual(accept('def log : Log := nil def copy : List Entry := log def back : Log := copy'), [
    { name: 'log', type: 'List (Entry)', value: [] },
    { name: 'copy', type: 'List (Entry)', value: [] },
    { name: 'back', type: 'List (Entry)', value: [] },
  ]);
  reject('def log : Log := 0');
  reject('def log : Log := cons momentNow nil');
});

test('Query, WritePath and ReadPath are types of a later milestone', () => {
  for (const type of ['Query Flag', 'Query', 'WritePath', 'ReadPath', 'List WritePath', 'Option (Query Flag)']) {
    assert.match(JSON.stringify(reject(`def x : ${type} := nil`)), /this type belongs to a later milestone/, type);
  }
  assert.doesNotMatch(JSON.stringify(reject('def x : Unknown := nil')), /later milestone/);
  reject('def q : Moment := queryStageStats');
});

test('every operation name is reserved', () => {
  const names = ['Log', 'WritePath', 'ReadPath',
    ...operations.flatMap(family => [family, ...families.get(family).map(constructor => constructor.name)])];
  assert.equal(new Set(names).size, names.length);
  for (const name of names) reject(`def ${name} : Nat := 1`);
  // Field names and other spellings stay free.
  accept('def log : Nat := 1 def moment : Nat := 2 def entries : Nat := 3');
});

test('an operation constructor belongs to one family', () => {
  accept('def now : Moment := momentNow def copy : Moment := now');
  reject('def now : Moment := momentNow def copy : PipelineKey := now');
  reject('def now : Moment := pipelineByStage');
  reject('def key : PipelineKey := momentNow');
  reject('def now : Moment := partyPerson');
  reject('def kind : KindParty := momentNow');
  reject('def now : Moment := "momentNow"');
});

test('operations example has the documented output', async () => {
  const source = await readFile(new URL('../examples/operations.ledger', import.meta.url), 'utf8');
  const acme = { kind: 'kindParty', hash: 'party-acme' };
  const deal = { kind: 'kindCommercial', hash: 'deal-1' };
  const advance = { tag: 'commandTransition', commercial: deal, stage: 'negotiation' };
  const denied = { tag: 'outcomeDenied', policy: null, missing: [{ tag: 'missingApproval', role: 'legal' }] };
  assert.equal(JSON.stringify(accept(source)), JSON.stringify([
    { name: 'acme', type: 'Ref (kindParty)', value: acme },
    { name: 'deal', type: 'Ref (kindCommercial)', value: deal },
    { name: 'now', type: 'Moment', value: { tag: 'momentNow' } },
    { name: 'before', type: 'Moment', value: { tag: 'momentAsOf', entry: 'entry-7' } },
    { name: 'advance', type: 'Command', value: advance },
    { name: 'write', type: 'Write', value: { actor: { tag: 'actorHuman', party: acme }, expect: 'entry-7', command: advance } },
    { name: 'denied', type: 'Outcome', value: denied },
    { name: 'history', type: 'List (Entry)', value: [] },
    { name: 'step', type: 'Step', value: { log: [], outcome: denied } },
    { name: 'key', type: 'PipelineKey', value: 'pipelineByStage' },
    { name: 'bucket', type: 'Bucket', value: { key: 'negotiation', count: 2, amountCents: 150000 } },
  ]));
});
