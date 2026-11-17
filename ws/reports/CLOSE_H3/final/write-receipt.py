#!/usr/bin/env python3
"""Collect the successful final closing build and immutable dependency manifests."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path('/home/ubuntu/aklt/wt/CLOSE_H3')
REPORT = Path('/home/ubuntu/aklt/reports/CLOSE_H3')
FINAL = REPORT / 'final'


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    output = (FINAL / 'build.log').read_text()
    timing = (FINAL / 'build.time').read_text()
    assert 'error:' not in output and 'warning:' not in output
    assert re.search(r'Exit status: 0\s*$', timing)
    expected = {
        'CertData.Close.h1': 'AKLT.Blueprint.Top.H1Statement',
        'CertData.Close.h2': 'AKLT.Blueprint.Top.H2Statement',
        'CertData.Close.h3': 'AKLT.Blueprint.Top.H3Statement',
        'CertData.Close.main': 'AKLT.Challenge.MainStatementV2',
    }
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    proofs = []
    source = (ROOT / 'CertData/Close/All.lean').read_text()
    for name, statement in expected.items():
        header = next(line for line in output.splitlines() if line.startswith(f'theorem {name} '))
        assert header == f'theorem {name} : {statement} :=', header
        assert f'example : {statement} := {name.rsplit(".", 1)[1]}' in source
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", output)
        assert match, name
        axioms = [item.strip() for item in match[1].split(',')]
        assert set(axioms) <= allowed
        proofs.append({'name': name, 'module': 'CertData.Close.All', 'type': statement,
                       'printed_declaration': header, 'hypothesis_free': True, 'axioms': axioms})
    duration = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)', timing)[1]
    parts = [float(item) for item in duration.split(':')]
    wall = sum(value * 60 ** i for i, value in enumerate(reversed(parts)))
    peak = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', timing)[1])
    h1 = json.loads((FINAL / 'h1-manifest.json').read_text())
    h3 = json.loads((FINAL / 'h3-manifest.json').read_text())
    scan = json.loads((FINAL / 'source-closure-audit.json').read_text())
    assert scan['success']
    for item in scan['new_or_changed_handwritten']:
        assert digest(ROOT / item['path']) == item['sha256']
    assert h1['summary']['generated_module_count'] == 7964
    assert h3['summary']['generated_module_count'] == 5032
    merge_set = ['CertData/H3/Close/Leaves.lean', 'CertData/H3/Close/Main.lean',
                 'CertData/H1/Close/Main.lean', 'CertData/H1/Close/Audit.lean',
                 'CertData/Close/All.lean', 'lakefile.toml']
    files = [{'path': name, 'sha256': digest(ROOT / name)} for name in merge_set]
    (FINAL / 'merge-set.txt').write_text('\n'.join(merge_set) + '\n')
    source_olean = ROOT / '.lake/build/lib/lean/CertData/Close/All.olean'
    disk = []
    for path in [ROOT, REPORT]:
        disk.append({'path': str(path),
                     'apparent_bytes': int(subprocess.check_output(['du', '-sb', str(path)], text=True).split()[0]),
                     'allocated_bytes': int(subprocess.check_output(['du', '-s', '-B1', str(path)], text=True).split()[0])})
    assert sum(item['allocated_bytes'] for item in disk) < 60_000_000_000
    base = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    mathlib = subprocess.check_output(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert base == h1['summary']['base'] == scan['base']
    assert mathlib == '065356127b1dc0016f66b7283ce0ce2c4055aa55'
    receipt = {
        'format': 'aklt-final-closing-v1', 'status': 'COMPLETE',
        'created_utc': datetime.now(timezone.utc).isoformat(), 'base_commit': base,
        'worktree': str(ROOT), 'module': 'CertData.Close.All', 'theorems': proofs,
        'exact_type_examples': 4, 'allowed_axioms': sorted(allowed),
        'lean_version': '4.35.0-rc2', 'lean_commit': '11acb17ec6b07a8f9e9173e6845197929540936b',
        'lean_version_output': 'Lean (version 4.35.0-rc2, x86_64-unknown-linux-gnu, commit 11acb17ec6b07a8f9e9173e6845197929540936b, Release)',
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'mathlib_commit': mathlib, 'mathlib_prebuilt': True,
        'build': {
            'command': ['bash', str(FINAL / 'build.sh')],
            'lean_command': ['lake', 'env', 'lean', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                             '-DElab.async=false', '-o', '.lake/build/lib/lean/CertData/Close/All.olean',
                             'CertData/Close/All.lean'],
            'cwd': str(ROOT), 'path_prefix': '$HOME/.elan/bin', 'exit': 0,
            'wall_seconds': wall, 'peak_rss_kib': peak, 'peak_rss_bytes': peak * 1024,
            'user_cpu_seconds': float(re.search(r'User time \(seconds\): ([\d.]+)', timing)[1]),
            'system_cpu_seconds': float(re.search(r'System time \(seconds\): ([\d.]+)', timing)[1]),
            'maximum_concurrent_lean_processes': 1,
            'log': str(FINAL / 'build.log'), 'log_sha256': digest(FINAL / 'build.log'),
            'time_receipt': str(FINAL / 'build.time'), 'time_receipt_sha256': digest(FINAL / 'build.time'),
        },
        'generated_libraries': {
            'H1': {'library': 'CertDataH1', 'module_count': 7964,
                   'manifest': str(FINAL / 'h1-manifest.json'),
                   'manifest_sha256': digest(FINAL / 'h1-manifest.json'),
                   'summary': h1['summary'], 'modules': h1['modules']},
            'H3': {'library': 'CertData', 'module_count': 5032,
                   'production_manifest_count_including_handwritten': 5035,
                   'manifest': str(FINAL / 'h3-manifest.json'),
                   'manifest_sha256': digest(FINAL / 'h3-manifest.json'),
                   'summary': h3['summary'], 'modules': h3['modules'],
                   'preserved_handwritten_manifest_entries': h3['preserved_handwritten']},
        },
        'total_attached_generated_modules': 12996,
        'handwritten_import_closure_audit': {
            'path': str(FINAL / 'source-closure-audit.json'),
            'sha256': digest(FINAL / 'source-closure-audit.json'), 'success': True,
            'unchanged_handwritten_on_main': scan['handwritten_on_main_count'],
            'scanned_new_or_changed_count': scan['new_or_changed_handwritten_count'],
            'scanned_new_or_changed_sources': scan['new_or_changed_handwritten'],
            'extra_scan': scan['extra_handwritten_scan'],
        },
        'source_merge_set': files,
        'output_olean': {'path': str(source_olean), 'sha256': digest(source_olean),
                         'bytes': source_olean.stat().st_size},
        'disk': disk, 'lakefile_default_targets': ['AKLT'],
        'lakefile_change': 'Add CertData.H1.Close.+ only to the existing CertDataH1 opt-in globs.',
        'numerical_production_rerun': False, 'interface_repairs': [], 'open_issues': [],
    }
    (REPORT / 'final-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'proofs': proofs,
                      'wall_seconds': wall, 'peak_rss_bytes': peak * 1024,
                      'generated_module_count': 12996}, indent=2))


if __name__ == '__main__':
    main()
