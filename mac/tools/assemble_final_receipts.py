#!/usr/bin/env python3
"""Copy the compact final-build receipts into verification/final/ of the release tree.

usage: assemble_final_receipts.py REPORTS_FINAL RELEASE_TREE [--regression]
Large files are gzip-compressed deterministically (mtime 0). The complete report
directory is published separately as a release asset.
"""
import gzip, hashlib, json, shutil, sys
from pathlib import Path

R = Path(sys.argv[1]); T = Path(sys.argv[2]) / 'verification/final'
with_regression = '--regression' in sys.argv

def put(src, dst, gz=False):
    src = R / src; dst = T / dst
    dst.parent.mkdir(parents=True, exist_ok=True)
    if gz:
        dst = dst.with_name(dst.name + '.gz')
        with open(dst, 'wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0, filename='') as out:
            out.write(src.read_bytes())
    else:
        shutil.copyfile(src, dst)

def put_json(obj, dst):
    dst = T / dst; dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(json.dumps(obj, indent=2) + '\n')

if T.exists():
    shutil.rmtree(T)

# Driver status files and the hand-written build logs.
put('logs/final-h3.status', 'status/handwritten-and-H3.status')
put('logs/final-h1.status', 'status/H1.status')
put('close/status', 'status/closing.status')
put('logs/handwritten-build.log', 'handwritten/cold-build.log', gz=True)
put('logs/handwritten-build-b.log', 'handwritten/rebuild-after-comment-edits.log', gz=True)

# H3.
for name in ['summary.json', 'production-run.json', 'closing-run.json', 'environment.json', 'input-pins.json', 'runs.jsonl']:
    put('H3/' + name, 'H3/' + name)
for name in ['axioms.json', 'declarations.json', 'sources.json']:
    put('H3/' + name, 'H3/' + name, gz=True)
put('logs/h3-verify.log', 'H3/verify.log')
put('recheck/h3-verify-newtools.log', 'H3/verify-release-tools.log')

# H1.
v = json.loads((R / 'H1/verified-production.json').read_text())
put_json({k: x for k, x in v.items() if k not in ('records', 'stages', 'input_receipts')}, 'H1/verified-summary.json')
put_json(v['stages'], 'H1/per-kind.json')
for name in ['run-data-only-production.json', 'data-input-receipt.json']:
    put('H1/' + name, 'H1/' + name)
put('H1/SOURCES.sha256', 'H1/SOURCES.sha256', gz=True)
for name in ['receipt.json', 'Main.stdout', 'Audit.stdout', 'SOURCES.sha256', 'COMPILED.sha256']:
    put('H1/closing/' + name, 'H1/closing/' + name)
put('logs/h1-verify.log', 'H1/verify.log')
put('recheck/h1-verify-newtools.log', 'H1/verify-release-tools.log')
put('recheck/h1-reexport-compare.log', 'H1/reexport-compare-release-tools.log')

# Closing checks.
put('close/input-pins.json', 'closing/input-pins.json')
put('close/source-checks.json', 'closing/source-checks.json', gz=True)
h = json.loads((R / 'close/headers.json').read_text())
put_json({k: x for k, x in h.items() if k != 'parser_output'}, 'closing/headers-summary.json')
for stage in ['close-CertData.Close.All', 'close-Solution', 'close-Audit', 'strict-full-audit', 'full-axiom-transcript',
              'handwritten-axiom-transcript', 'statement-generation-check', 'input-pins', 'module-headers',
              'source-configuration', 'physical-statement-comparison-and-negative-control']:
    put(f'close/stages/{stage}/stdout.log', f'closing/stages/{stage}.stdout.log')
    put(f'close/stages/{stage}/time.log', f'closing/stages/{stage}.time.log')
put('close/stages/strict-handwritten-audit/stdout.log', 'closing/stages/strict-handwritten-audit.stdout.log', gz=True)
put('close/stages/strict-handwritten-audit/time.log', 'closing/stages/strict-handwritten-audit.time.log')
for case in ['positive', 'negative-spin']:
    put(f'close/statement/{case}/receipt.json', f'closing/statement/{case}/receipt.json')
    for stream in ['stdout', 'stderr']:
        put(f'close/statement/{case}/stages/comparator/{stream}.log', f'closing/statement/{case}/comparator.{stream}.log')

put('archives/archive-match.json', 'archives/archive-match.json')
put('archives/release-assets.sha256', 'archives/release-assets.sha256')

(T / 'README.md').write_text("""# Receipts of the final build

These files are the compact receipts behind the root `VERIFICATION.md`. They were
produced on sources with Lean source digest
`c875dff024d396b0b78f1fa955ea5d38e8f577e1d8bd69e970fd02bea906bee9`. `SHA256SUMS`
pins every file here except this note. Files ending in `.gz` are gzip-compressed
copies of the original logs. The complete report directory, including per-module
logs and axiom transcripts, is the release asset `verification-receipts.tar.zst`.

| Directory | Contents |
|---|---|
| `status/` | Time-stamped status lines of the three build drivers |
| `handwritten/` | Lake logs of the cold hand-written build and of the rebuild after comment-only edits |
| `H1/` | Input receipt, run record, verifier summary, per-kind totals, generated-source hashes, closing receipt, verifier logs |
| `H3/` | Summary, run records, environment, input pins, axiom and declaration lists, generated-source hashes, verifier logs |
| `closing/` | Input pins, closing-module and Audit transcripts, source and header checks, both statement comparisons |
| `regression/` | Independent-kernel replay of the two-input reduction: receipt and stage results |
| `archives/` | Comparison of the released source archives with the final build's generated sources; hashes of the release assets |

Absolute paths in these files are those of the build machine. Commit hashes in the
status files are development commits; they resolve on the `development` branch.
The status files also show two restarts: the H3 driver was restarted from an empty
state after comment-only edits to the Lean sources, and the H1 driver was restarted
without a preliminary step that named two modules that do not exist. The closing
driver first stopped at the input-pin check because the input directory had not
been prepared, and later at the source check because of the two author-metadata
findings; the remaining checks were then run and passed.
""")

if with_regression:
    put('regression/receipt.json', 'regression/receipt.json')
    for stage in sorted(p.name for p in (R / 'regression/stages').iterdir()):
        d = R / 'regression/stages' / stage
        if (d / 'result.json').exists():
            put(f'regression/stages/{stage}/result.json', f'regression/stages/{stage}.result.json')
        for stream in ['stdout', 'stderr']:
            f = d / f'{stream}.log'
            if f.exists() and 0 < f.stat().st_size < 200_000:
                put(f'regression/stages/{stage}/{stream}.log', f'regression/stages/{stage}.{stream}.log')
    put('logs/regression-attempt1.log', 'regression/first-attempt.log')

lines = []
for p in sorted(x for x in T.rglob('*') if x.is_file() and x.name != 'README.md'):
    lines.append(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(T).as_posix()}\n')
(T / 'SHA256SUMS').write_text(''.join(lines))
print(len(lines), 'files', sum(p.stat().st_size for p in T.rglob('*') if p.is_file()), 'bytes')
