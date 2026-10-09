import { accessSync, closeSync, constants, mkdtempSync, openSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

export const sourceLimit = 65_536;
export const outputLimit = 4 * 1024 * 1024;

// One scratch file per process holds the source. The compiler reads it as a
// file descriptor: the spawnSync `input:` pipe sometimes did not reach EOF.
let scratch;
function sourceFile() {
  if (scratch === undefined) {
    scratch = mkdtempSync(join(tmpdir(), 'ledgerc-bridge-'));
    process.once('exit', () => rmSync(scratch, { recursive: true, force: true }));
  }
  return join(scratch, 'source');
}

// The bridge only transfers bytes. All language work runs in build/ledgerc.
export async function createCompiler(path = new URL('../build/ledgerc', import.meta.url)) {
  const binary = path instanceof URL ? fileURLToPath(path) : path;
  accessSync(binary, constants.X_OK);
  return source => {
    if (!(source instanceof Uint8Array)) throw new TypeError('source must be UTF-8 bytes');
    if (source.length > sourceLimit) throw new Error(`source exceeds ${sourceLimit} bytes`);
    const file = sourceFile();
    writeFileSync(file, source);
    const input = openSync(file, 'r');
    const run = spawnSync(binary, ['--stdin'], { stdio: [input, 'pipe', 'pipe'], maxBuffer: 2 * outputLimit, timeout: 60_000 });
    closeSync(input);
    if (run.error) throw run.error;
    if (run.status !== 0) {
      throw new Error(run.stderr.toString('utf8').trim() || `compiler exited with ${run.status ?? run.signal}`);
    }
    return new TextDecoder('utf-8', { fatal: true }).decode(run.stdout);
  };
}
