#!/usr/bin/env python3
"""Run the host capability probe and print one line for each step.

Usage: probe.py [FILTER]

Each step runs under guard.py (4 GB resident limit, wall-clock limit). A
FILTER keeps only the steps whose label contains it. MECH selects the
mechanism-lang driver. The probe writes only below a new temporary directory.
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MECH = os.environ.get("MECH", "/Users/oobi/Documents/mechanism-lang/_bend2/bin/mech.exe")
GUARD = HERE / "guard.py"
WORK = Path(tempfile.mkdtemp(prefix="ledger-probe-"))
SCHEMA = ROOT / "core" / "schema.mech"
OPS = ROOT / "core" / "ops.mech"
NAT_EXPORTS = (
    "natSum", "natDiff", "natDiffFloor", "natProduct", "natWide",
    "ltTrue", "ltFalse", "eqTrue", "quot", "lastDigit",
)
REC_EXPORTS = ("recTextLength", "recListLength", "recListFold", "recValueSize")
OUT_EXPORTS = (
    "emptyText", "consText", "textIsEnd", "textHead", "textTail", "textLength", "transform",
)
HOSTS = ("kernel", "node", "wasmtime")
COUNTS = (1000, 10000, 100000)


def joined(name, parts):
    target = WORK / name
    target.write_text("\n".join(Path(part).read_text() for part in parts))
    return target


def guarded(command, timeout):
    words = [sys.executable, str(GUARD), "--timeout", str(timeout), "--", *map(str, command)]
    done = subprocess.run(words, capture_output=True, text=True)
    lines = done.stderr.strip().splitlines()
    return json.loads(lines[-1]), done.stdout.strip(), " | ".join(lines[:-1])


def show(label, command, timeout):
    report, out, err = guarded(command, timeout)
    print(
        f"{label}: {report['verdict']} exit={report['exit']} wall={report['wall_s']}s "
        f"rss={report['peak_child_mb']}MB out={out[:400]!r} err={err[:300]!r}",
        flush=True,
    )


def runs(label, source, names):
    return [
        (f"run {label} {name} {host}", [MECH, "run", source, "--export", name, "--host", host], 120)
        for name in names
        for host in HOSTS
    ]


def steps():
    core = joined("core.mech", [SCHEMA, OPS])
    rec = joined("rec.mech", [SCHEMA, HERE / "rec.mech"])
    same = joined("rec-neg-same.mech", [SCHEMA, HERE / "rec-neg-same.mech"])
    grow = joined("rec-neg-grow.mech", [SCHEMA, HERE / "rec-neg-grow.mech"])
    wasm = WORK / "out.wasm"
    exports = [word for name in OUT_EXPORTS for word in ("--export", name)]
    checks = [
        ("check schema", [MECH, "check", SCHEMA], 120),
        ("check core (schema + ops)", [MECH, "check", core], 120),
        ("check rec", [MECH, "check", rec], 120),
        ("check rec-neg-same (must fail)", [MECH, "check", same], 120),
        ("check rec-neg-grow (must fail)", [MECH, "check", grow], 120),
        ("check nat", [MECH, "check", HERE / "nat.mech"], 120),
        ("check dep", [MECH, "check", HERE / "dep.mech"], 120),
    ]
    build = [("build out", [MECH, "build", SCHEMA, HERE / "out.mech", "-o", wasm, *exports], 120)]
    drives = [(f"drive {count}", ["node", HERE / "drive.mjs", wasm, count], 300) for count in COUNTS]
    return (
        checks
        + runs("nat", HERE / "nat.mech", NAT_EXPORTS)
        + runs("rec", rec, REC_EXPORTS)
        + runs("dep", HERE / "dep.mech", ("depLength",))
        + build
        + drives
    )


def main():
    wanted = sys.argv[1:] or [""]
    chosen = [entry for entry in steps() if any(word in entry[0] for word in wanted)]
    print(f"work={WORK} mech={MECH} steps={len(chosen)}", flush=True)
    return [show(*entry) for entry in chosen] and 0


if __name__ == "__main__":
    sys.exit(main())
