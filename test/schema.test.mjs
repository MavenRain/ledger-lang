import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import test from 'node:test';
import { fileURLToPath } from 'node:url';
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

// Read the language's source of truth, never the compiler metadata. This small
// test-only signature reader makes schema additions and field changes visible
// to the executable conformance checks below.
const schemaSource = (await readFile(new URL('../core/schema.mech', import.meta.url), 'utf8'))
  .replace(/--[^\n]*/g, '');
const families = new Map();
for (const block of schemaSource.split(/^(?:mu|and) /m).slice(1)) {
  const [header, ...declarations] = block.split(/^\| /m);
  const family = header.match(/^\w+/)[0];
  const constructors = declarations.map(declaration => {
    const name = declaration.match(/^\w+/)[0];
    const signature = declaration.slice(declaration.indexOf(':') + 1);
    const parts = signature.split(/\s+->\s+/);
    assert.match(parts.pop().trim(), new RegExp(`^${family}(?:\\s+\\w+)?$`));
    const fields = parts.map(part => {
      const match = part.trim().match(/^\((\w+)\s*:\s*(.+)\)$/s);
      assert.ok(match, part);
      return { name: match[1], type: match[2].trim() };
    });
    return { name, fields };
  });
  families.set(family, constructors);
}
const kinds = families.get('Kind').map(constructor => constructor.name);
const addedFamilies = [...families.keys()].slice([...families.keys()].indexOf('Account'));

function typeShape(type) {
  let unwrapped = type.trim();
  while (unwrapped.startsWith('(') && unwrapped.endsWith(')')) {
    unwrapped = unwrapped.slice(1, -1).trim();
  }
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

for (const family of addedFamilies) {
  for (const constructor of families.get(family)) {
    test(`schema ${family}.${constructor.name}: fields, order, types, and arity`, () => {
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

test('Hash wraps Text and retains its distinct type', () => {
  assert.deepEqual(accept('def h : Hash := hashOf "héllo\\n" def copy : Hash := h').map(item => item.value), ['héllo\n', 'héllo\n']);
  reject('def h : Hash := "digest"');
  reject('def h : Hash := hashOf 1');
  reject('def t : Text := "digest" def h : Hash := t');
  reject('def h : Hash := hashOf "digest" def t : Text := h');
});

test('Ref indices normalize Kind aliases and reject every different Kind', () => {
  for (const kind of kinds) {
    const preamble = `def index : Kind := ${kind} def alias : Kind := index
      def h : Hash := hashOf "digest" def reference : Ref ((alias)) := refTo h`;
    assert.deepEqual(accept(preamble).at(-1), {
      name: 'reference', type: `Ref (${kind})`, value: { kind, hash: 'digest' },
    });
    assert.deepEqual(accept(`${preamble} def copy : Ref ${kind} := reference`).at(-1).value, { kind, hash: 'digest' });
    for (const other of kinds.filter(value => value !== kind)) {
      reject(`${preamble} def copy : Ref ${other} := reference`);
    }
    reject(`def r : Ref ${kind} := refTo "digest"`);
  }
});

test('Ref indices are checked inside every container type', () => {
  const prefix = 'def k : Kind := kindParty def r : Ref k := refTo (hashOf "h")';
  const cases = [
    ['Option (Ref k)', 'some r', 'Option (Ref kindEvent)'],
    ['List (Ref k)', 'cons r nil', 'List (Ref kindEvent)'],
    ['Prod (Ref k) Nat', 'pair r 3', 'Prod (Ref kindEvent) Nat'],
    ['Sum Text (Ref k)', 'inr r', 'Sum Text (Ref kindEvent)'],
  ];
  for (const [type, term, wrong] of cases) {
    accept(`${prefix} def container : ${type} := ${term}`);
    reject(`${prefix} def container : ${type} := ${term} def mismatch : ${wrong} := container`);
  }
  reject('def x : Option Ref kindParty := none');
  reject('def x : List Hash := cons hashOf "h" nil');
  reject('def x : Actor := actorHuman refTo (hashOf "h")');
});

test('Ref kind mismatches are rejected inside List record fields', () => {
  // No List field type mentions Ref directly, so the per-constructor loop
  // above does not reach these Refs. Each wrong* Ref has the next Kind.
  const refs = `${wrongRefs}
    def partyRef : Ref kindParty := refTo (hashOf "party")
    def dealRef : Ref kindCommercial := refTo (hashOf "deal")
    def eventRef : Ref kindEvent := refTo (hashOf "event")`;
  const artifact = subjects =>
    `${refs}\ndef result : Artifact := makeArtifact artifactPdf "s" "u" "m" (${subjects}) attrsEnd`;
  const party = identifiers =>
    `${refs}\ndef result : Party := makeParty partyOrg "Acme" none (${identifiers}) attrsEnd none none`;
  const identifier = verifiedBy => `(makeIdentifier systemDomain "acme.example" (some ${verifiedBy}))`;
  accept(artifact('cons (accountParty partyRef) (cons (accountCommercial dealRef) nil)'));
  accept(party(`cons ${identifier('eventRef')} (cons ${identifier('eventRef')} nil)`));
  for (const source of [
    artifact('cons (accountParty wrongkindParty) (cons (accountCommercial dealRef) nil)'),
    artifact('cons (accountParty partyRef) (cons (accountCommercial wrongkindCommercial) nil)'),
    party(`cons ${identifier('wrongkindEvent')} nil`),
    party(`cons ${identifier('eventRef')} (cons ${identifier('wrongkindEvent')} nil)`),
  ]) {
    assert.match(reject(source).message, /declared type/, source);
  }
});

test('invalid Kind indices report the offending byte', () => {
  for (const index of ['missing', 'Party', 'partyPerson', '0', '"kindParty"', 'none']) {
    const source = `def r : Ref ${index} := refTo (hashOf "h")`;
    const error = reject(source);
    assert.equal(error.byte, source.indexOf(index, 12), source);
    assert.match(error.message, /Kind index/);
  }
  reject('def r : Ref later := refTo (hashOf "h") def later : Kind := kindParty');
  reject('def k : Text := "kindParty" def r : Ref k := refTo (hashOf "h")');
  reject('def r : Ref := refTo (hashOf "h")');
  reject('def r : Ref (kindParty := refTo (hashOf "h")');
  const error = reject(`def r : Ref ${'('.repeat(600)}kindParty${')'.repeat(600)} := refTo (hashOf "h")`);
  assert.match(error.message, /fuel exhausted/);
  assert.ok(error.byte > 0);
});

test('all added schema types and constructors are reserved definition names', () => {
  for (const family of ['Hash', 'Ref', ...addedFamilies]) {
    for (const name of [family, ...families.get(family).map(constructor => constructor.name)]) {
      assert.match(reject(`def ${name} : Nat := 0`).message, /reserved/);
    }
  }
  accept('def displayName : Text := "field names remain ordinary identifiers"');
});

test('record aliases preserve nominal types and nested Option presence', () => {
  const party = 'makeParty partyOrg "Acme" none nil attrsEnd none none';
  assert.deepEqual(accept(`def p : Party := ${party} def q : Party := p`).map(item => item.value), [
    { kind: 'partyOrg', displayName: 'Acme', legalName: null, identifiers: [], attrs: {}, lastEvent: null, deletedBy: null },
    { kind: 'partyOrg', displayName: 'Acme', legalName: null, identifiers: [], attrs: {}, lastEvent: null, deletedBy: null },
  ]);
  reject(`def p : Party := ${party} def q : Entry := p`);
  assert.deepEqual(accept('def r : Option (Option (Ref kindParty)) := some none')[0].value, { some: null });
  reject(`def p : Party := makeParty partyOrg (textByte 255 textEnd) none nil attrsEnd none none`);
});

test('CRM example compiles through the public CLI', () => {
  const result = spawnSync('sh', [
    fileURLToPath(new URL('../bin/ledgerc', import.meta.url)),
    fileURLToPath(new URL('../examples/crm.ledger', import.meta.url)),
  ], { encoding: 'utf8', timeout: 30_000 });
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stderr, '');
  const output = JSON.parse(result.stdout);
  assert.equal(output['ledger-lang'], 1);
  // Expected values are written from examples/crm.ledger and the field order
  // in core/schema.mech, never taken from compiler output.
  const ref = (kind, hash) => ({ kind, hash });
  const org = ref('kindParty', 'org-entry');
  const person = ref('kindParty', 'person-entry');
  const deal = ref('kindCommercial', 'deal-entry');
  const evidence = ref('kindArtifact', 'email-entry');
  const company = {
    kind: 'partyOrg', displayName: 'Acme', legalName: 'Acme Ltd',
    identifiers: [{ system: { tag: 'systemDomain' }, value: 'acme.example', verifiedBy: null }],
    attrs: {}, lastEvent: null, deletedBy: null,
  };
  const provenance = { artifact: evidence, event: null, confidence: 95 };
  const requirement = { fields: ['buyer'], commitmentKinds: ['commitmentTerm'], approvalFrom: null, maxDiscountPct: 15 };
  const rule = { principal: 'sales', can: ['permissionRead', 'permissionWrite'], fields: null };
  const expected = [
    ['orgKind', 'Kind', 'kindParty'],
    ['orgHash', 'Hash', 'org-entry'],
    ['org', 'Ref (kindParty)', org],
    ['person', 'Ref (kindParty)', person],
    ['deal', 'Ref (kindCommercial)', deal],
    ['evidence', 'Ref (kindArtifact)', evidence],
    ['company', 'Party', company],
    ['provenance', 'Provenance', provenance],
    ['membership', 'Membership', {
      person, org, role: 'Buyer', isPrimary: true, endedBy: null, provenance, attrs: {},
    }],
    ['commercial', 'Commercial', {
      kind: 'commercialDeal', name: 'Annual plan', party: org, stage: 'negotiation', amountCents: 250000,
      currency: 'USD', expectedCloseOn: '2026-12-01', status: 'statusOpen', attrs: {}, lastEvent: null,
    }],
    ['commitment', 'Commitment', {
      commercial: deal, kind: 'commitmentTerm', label: 'Payment terms', value: 'net_30', unit: null,
      status: 'commitmentProposed', supersedes: null, provenance,
    }],
    ['artifact', 'Artifact', {
      kind: 'artifactEmail', sha256: 'content-digest', uri: 'file:///mail/quote.eml', mime: 'message/rfc822',
      subjects: [{ tag: 'accountParty', party: org }, { tag: 'accountCommercial', commercial: deal }], attrs: {},
    }],
    ['event', 'Event', {
      type: 'eventNoteAdded', subject: { tag: 'subjectCommercial', commercial: deal }, artifact: evidence,
      parent: null, payload: { note: 'Quote received' }, policy: null,
    }],
    ['assignment', 'Assignment', {
      subject: { tag: 'accountCommercial', commercial: deal }, assignee: person, role: 'roleOwner',
      territory: null, endedBy: null, provenance,
    }],
    ['requirement', 'Requirement', requirement],
    ['rule', 'AclRule', rule],
    ['policy', 'Policy', {
      name: 'Deal approval', appliesTo: { tag: 'scopeCommercial', kind: 'commercialDeal' },
      fromStage: 'negotiation', toStage: 'closed', require: requirement, acl: [rule], active: true,
    }],
    ['entry', 'Entry', {
      prev: null, actor: { tag: 'actorAgent', name: 'crm-import' }, body: { tag: 'createsParty', party: company },
    }],
  ].map(([name, type, value]) => ({ name, type, value }));
  assert.deepEqual(output.instances, expected);
  // Object equality alone would not detect a change in field order.
  assert.equal(JSON.stringify(output.instances), JSON.stringify(expected));
});
