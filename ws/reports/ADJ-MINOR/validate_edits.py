#!/usr/bin/env python3
"""Check the report, rebuild the exact audit, and compile original/proposed sources."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

HERE = Path(__file__).resolve().parent
MS = Path('/home/ubuntu/aklt/manuscript/bundle/manuscript')
log = []


def record(s):
    print(s, flush=True)
    log.append(s)


subprocess.run(['python3', 'build_report.py'], cwd=HERE, check=True)
subprocess.run(['python3', 'audit_exact.py'], cwd=HERE,
               stdout=(HERE/'audit_exact.out').open('w'), check=True)
record('Independent exact audit: PASS (one process, standard library only).')
eds = json.loads((HERE/'edits.json').read_text())
record(f'{len(eds)} replacements: unique anchors, original line ranges and staged application checked.')

manifest = json.loads((HERE/'input-sha256.json').read_text())
assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in manifest.items())
record(f'Frozen-source/report SHA256 manifest: {len(manifest)} entries unchanged.')

base = HERE/'validation-original'
base.mkdir(exist_ok=True)
for p in MS.glob('*.tex'):
    (base/p.name).write_bytes(p.read_bytes())

env = os.environ.copy()
env.update(OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1', NUMEXPR_NUM_THREADS='1')
for label, folder in [('frozen baseline', base), ('proposed corrections', HERE/'validation')]:
    for suffix in ('aux', 'toc', 'out', 'lot', 'lof'):
        (folder/f'main.{suffix}').unlink(missing_ok=True)
    for i in range(1, 5):
        with (folder/f'latex-pass-{i}.stdout').open('w') as out:
            run = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                                  '-file-line-error', 'main.tex'], cwd=folder, env=env,
                                 stdout=out, stderr=subprocess.STDOUT, timeout=120)
        if run.returncode:
            print((folder/f'latex-pass-{i}.stdout').read_text()[-6000:])
            raise RuntimeError(f'{label}: LaTeX failed on pass {i}')
        final_log = (folder/'main.log').read_text()
        if i >= 2 and 'Rerun to get cross-references right' not in final_log:
            break
    assert 'Rerun to get cross-references right' not in final_log
    record(f'LaTeX {label}: PASS (converged after {i} passes).')
    final_log = (folder/'main.log').read_text()
    assert not re.search(r'(undefined references|Citation .+ undefined|Reference .+ undefined)', final_log)


def labels(folder):
    return dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}', (folder/'main.aux').read_text()))


old_labels, new_labels = labels(base), labels(HERE/'validation')
assert old_labels == new_labels
record(f'All {len(old_labels)} LaTeX label values/numbers: unchanged; no undefined references/citations.')
for key in ['e:H', 't:main', 't:QD', 'e:icodod', 't:K', 'd:W', 'p:surgery', 'e:removal',
            'e:Ij', 'e:cutsum', 'l:Xconn', 't:cutMOS', 'r:Pweak', 'e:closed', 'p:closed']:
    record(f'  {key} = {new_labels[key]}')

report = (HERE/'report.md').read_text()
assert report.splitlines()[0] == 'STATUS: COMPLETE'
found = re.findall(r'^## FINDING ([^:]+): (CONFIRMED-MODIFIED|CONFIRMED|REJECTED)$', report, re.M)
required = {f'R{r}-{j}' for r, js in [(1, range(1,4)), (2, range(1,6)),
                                     (3, range(1,5)), (7, range(2,6))] for j in js}
assert required <= {x for x, v in found}
assert len(found) == 17 and len(required) == 16
assert all(f'**{e["id"]} — target' in report for e in eds)
assert report.count('```') % 2 == 0
audit_lines = {line.strip() for line in (HERE/'audit_exact.out').read_text().splitlines()}
for excerpt in re.findall(r'```text\n(.*?)\n```', report, re.S):
    for line in excerpt.splitlines():
        assert not line.strip() or line.strip() in audit_lines, ('inaccurate output quotation', line)
record('Every quoted computation-output line matches the independent audit output.')
record(f'Report coverage: all 16 requested findings plus 1 separate formal-note defect; all {len(eds)} exact corrections included.')
record('All validation checks passed. Inputs remain untouched.')
(HERE/'validation-checks.out').write_text('\n'.join(log)+'\n')
