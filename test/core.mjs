import { readFile } from 'node:fs/promises';

// Reads a core .def file and returns its rows in mech surface syntax, so the
// conformance readers see the language's source of truth in one form. Rows
// (see core/schema.def): CARRIER and FAMILY open a family, AND opens a family
// of the same mu group, CONSTRUCTOR and FIELD give a constructor and its
// fields, DEFINE gives a definition. An argument never contains a comma.
function rows(text) {
  const found = [];
  const start = /\b(CARRIER|FAMILY|AND|CONSTRUCTOR|FIELD|DEFINE)\(/g;
  for (let match = start.exec(text); match !== null; match = start.exec(text)) {
    let at = start.lastIndex;
    for (let depth = 1; depth > 0; at += 1) {
      if (at >= text.length) throw new Error(`unclosed ${match[1]} row`);
      depth += text[at] === '(' ? 1 : text[at] === ')' ? -1 : 0;
    }
    const body = text.slice(start.lastIndex, at - 1);
    const comma = body.indexOf(',');
    if (comma < 0) throw new Error(`${match[1]} row has no comma`);
    found.push({ kind: match[1], name: body.slice(0, comma).trim(), rest: body.slice(comma + 1).trim() });
    start.lastIndex = at;
  }
  return found;
}

const line = ({ kind, name, rest, fields }) => {
  if (kind === 'CONSTRUCTOR') return `| ${name} : ${[...fields, rest].join(' -> ')}`;
  if (kind === 'DEFINE') return `def ${name} ${rest}`;
  return `${kind === 'AND' ? 'and' : 'mu'} ${name} ${rest} with`;
};

export async function readCore(url) {
  const text = (await readFile(url, 'utf8')).replace(/\/\*[\s\S]*?\*\//g, '');
  const entries = rows(text).reduce((done, { kind, name, rest }) => {
    if (kind !== 'FIELD') return [...done, { kind, name, rest, fields: [] }];
    const last = done.at(-1);
    if (last?.kind !== 'CONSTRUCTOR') throw new Error(`field ${name} does not follow a constructor`);
    return [...done.slice(0, -1), { ...last, fields: [...last.fields, `(${name} : ${rest})`] }];
  }, []);
  return entries.map(line).join('\n') + '\n';
}
