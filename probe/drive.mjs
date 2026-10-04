// Probe driver for the byte path. It pushes COUNT bytes into the reactor
// module, calls transform, pulls the result back and prints one JSON line.
// Usage: node drive.mjs OUT.wasm COUNT
import { readFile } from 'node:fs/promises';

const [wasmPath, countText] = process.argv.slice(2);
const count = Number(countText);
const module = await WebAssembly.compile(await readFile(wasmPath));
const imports = WebAssembly.Module.imports(module).map(entry => `${entry.module}.${entry.name}`);
const kinds = WebAssembly.Module.exports(module).map(entry => `${entry.name}:${entry.kind}`);
const { exports } = await WebAssembly.instantiate(module, {});
const constant = entry => (typeof entry === 'function' ? entry() : entry.value);
const byteAt = index => index % 251;
const expected = index => (byteAt(index) < 250 ? byteAt(index) + 1 : 0);
const timed = work => {
  const start = performance.now();
  const value = work();
  return { value, ms: Math.round((performance.now() - start) * 100) / 100 };
};
const attempt = work => {
  try {
    return work();
  } catch (error) {
    return { failed: `${error.name}: ${error.message}` };
  }
};

const report = attempt(() => {
  const pushed = timed(() =>
    Array.from({ length: count }, (_, index) => byteAt(count - 1 - index)).reduce(
      (text, byte) => exports.consText(byte, text),
      constant(exports.emptyText),
    ));
  const transformed = timed(() => exports.transform(pushed.value));
  const measured = timed(() => exports.textLength(transformed.value));
  const cursor = { rest: transformed.value };
  const pulled = timed(() =>
    Uint8Array.from({ length: measured.value }, () => {
      const byte = exports.textHead(cursor.rest);
      cursor.rest = exports.textTail(cursor.rest);
      return byte;
    }));
  const wrong = pulled.value.reduce((total, byte, index) => total + (byte === expected(index) ? 0 : 1), 0);
  return {
    length: measured.value,
    atEnd: exports.textIsEnd(cursor.rest),
    wrong,
    ms: { push: pushed.ms, transform: transformed.ms, length: measured.ms, pull: pulled.ms },
  };
});

console.log(JSON.stringify({ count, imports, kinds, ...report }));
