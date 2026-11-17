"""Contract tests for the final generator; no campaign statement is proved here."""

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import time

sys.dont_write_bytecode = True
ROOT = Path('/home/ubuntu/aklt/wt/ARCH_FINAL')
REPORT = Path('/home/ubuntu/aklt/reports/ARCH_FINAL')
spec = importlib.util.spec_from_file_location('gen_final', ROOT / 'AKLT/Final/gen_final.py')
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)


def rejects(function, *args):
    try:
        function(*args)
    except (ValueError, RuntimeError):
        return
    raise AssertionError('Expected rejection')


start = time.monotonic()
rows, metadata = gen.read_contract(ROOT, gen.DEFAULT_LEAVES)
assert len(rows) == 420
assert len({row['lean_name'] for row in rows}) == 420
assert sum(row['kind'] == 'leaf' for row in rows) == 416
assert sum(row['kind'] == 'certificate' for row in rows) == 4
assert not any(row['kind'] == 'bridge' for row in rows)
gen.discover(ROOT, rows, {})
canonical_sources = {
    row['key'] for row in rows
    if row['key'] and (ROOT / f"AKLT/W/{row['key']}/Main.lean").is_file()
}
discovered = {row['key'] for row in rows if row['proof_exists']}
assert canonical_sources == discovered
assert len(discovered) == 184
assert sum(not row['proof_exists'] for row in rows) == 236
assert not (ROOT / 'AKLT/Final/Main.lean').exists()
print('PASS: exact active checklist, 184 source proofs, 236 missing, no Main.lean')

with tempfile.TemporaryDirectory(prefix='generator-map-', dir=REPORT) as directory:
    path = Path(directory) / 'leaves.json'
    leaves = json.loads(gen.DEFAULT_LEAVES.read_text())
    leaves['Q999'] = dict(leaves['Q001'], node='AKLT.Blueprint.Q.FutureLeafStatement')
    path.write_text(json.dumps(leaves))
    rejects(gen.read_contract, ROOT, path)
    leaves = json.loads(gen.DEFAULT_LEAVES.read_text())
    del leaves['Q001']
    path.write_text(json.dumps(leaves))
    rejects(gen.read_contract, ROOT, path)
print('PASS: added or removed active leaf invalidates the frozen signature')

override = {'Q001': {'module': 'AKLT.W.Q001.Main', 'term': 'AKLT.W.Q001.main'}}
gen.discover(ROOT, rows, override)
assert rows[0]['proof']['term'] == 'AKLT.W.Q001.main'
rejects(gen.discover, ROOT, rows, {'UNKNOWN': override['Q001']})
rejects(gen.discover, ROOT, rows, {'Q001': dict(override['Q001'], term='by trivial')})
print('PASS: explicit declaration override and rejection of unknown or non-declaration terms')

gen.check_dependencies("'t' depends on axioms: [propext, Classical.choice, Quot.sound]")
rejects(gen.check_dependencies, "'t' depends on axioms: [propext, sorryAx]")
print('PASS: dependency allowlist rejects an unproved dependency')

# Render all 420 argument positions with named test tokens, without sending
# these unproved tokens to Lean or writing a candidate Main.lean.
for position, row in enumerate(rows):
    row['proof'] = {'module': 'AKLT.Final.Skeleton', 'term': f'TestProof.p{position}'}
source = gen.render(rows)
tokens = [line.strip() for line in source.splitlines() if line.startswith('    (')]
assert tokens == [f'(TestProof.p{i})' for i in range(420)]
assert source.count('import AKLT.Final.Skeleton') == 1
assert 'theorem main : AKLT.Challenge.MainStatementV2 :=' in source
print('PASS: complete application rendering preserves all 420 positions')

# Real Lean smoke test of compilation, import discovery, exact proof typing and
# dependency checks. The transient main is True, not a campaign leaf or headline.
sample = [{
    'proof': {'module': 'AKLT.W.Q001.Main', 'term': 'AKLT.W.Q001.main'}
}]
smoke = '''import AKLT.Final.Skeleton
import AKLT.W.Q001.Main
example : AKLT.Blueprint.Q.OrthogonalFamilyStatement := AKLT.W.Q001.main
namespace AKLT.Final
theorem main : True := True.intro
#print axioms main
end AKLT.Final
'''
capture = io.StringIO()
with contextlib.redirect_stdout(capture):
    output = gen.validate(ROOT, sample, smoke)
assert "'AKLT.W.Q001.main' depends on axioms:" in output
assert "'AKLT.Final.main' does not depend on any axioms" in output
assert not (ROOT / 'AKLT/Final/Main.lean').exists()
print(capture.getvalue(), end='')
print(output, end='')
print('PASS: real Lean compilation and dependency validation; Main.lean remains absent')

# A mismatched proof must fail Lean elaboration. This uses the already built
# skeleton and leaf artifact, so no dependency compilation needs repeating.
bad = smoke.replace(':= AKLT.W.Q001.main', ':= True.intro')
with tempfile.NamedTemporaryFile(mode='w', prefix='CheckWrongType', suffix='.lean',
                                 dir=ROOT / 'AKLT/Final', delete=False) as stream:
    stream.write(bad)
    filename = Path(stream.name)
try:
    rejects(gen.command, ROOT, ['lake', 'env', 'lean', str(filename)])
finally:
    filename.unlink()
assert not (ROOT / 'AKLT/Final/Main.lean').exists()
print('PASS: Lean rejects a proof of the wrong statement')
print(f'All generator tests passed in {time.monotonic() - start:.3f}s')
