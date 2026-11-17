#!/usr/bin/env python3
"""Replay regression: a transitive Boolean change must invalidate the proof."""
import json, shutil, subprocess, sys
from pathlib import Path
from production_export import ROOT, REPORT, write
from production_build import artifact_path


def main():
    namespace = 'CertData.H1.Validation.RegenCache'
    parent, data, check = [namespace + '.' + name for name in ['Parent', 'Data', 'Check']]
    report = REPORT / 'cache-validation'
    report.mkdir(parents=True, exist_ok=True)
    plan = dict(jobs=[dict(module=parent, kind='cache_validation', deps=[]),
                      dict(module=data, kind='cache_validation', deps=[parent]),
                      dict(module=check, kind='cache_validation', deps=[data])])
    manifest = report / 'cache.json'
    manifest.write_text(json.dumps(plan, indent=2) + '\n')
    command = [sys.executable, str(ROOT / 'AKLT/Cert/H1/tools/production_build.py'),
               str(manifest), '--jobs', '1', '--cap-gib', '2', '--report-dir', str(report)]
    def run(label):
        with (report / (label + '.log')).open('w') as log:
            return subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT).returncode
    def gate(value):
        write(parent, f'import Init\nnamespace {parent}\ndef gate : Bool := {value}\nend {parent}\n')
    try:
        write(data, f'import {parent}\nnamespace {data}\ndef payload : Nat := 7\nend {data}\n')
        write(check, f'import {data}\nnamespace {check}\ntheorem checked : {parent}.gate = true := by decide +kernel\n#print axioms checked\nend {check}\n')
        gate('true')
        assert run('initial') == 0
        assert run('unchanged-replay') == 0
        replay = json.loads((report / 'run-cache.json').read_text())
        assert replay['replayed'] == 3
        gate('false')
        assert run('expected-rejection') != 0
        failure = [json.loads(line) for line in (report / 'failures.jsonl').read_text().splitlines()][-1]
        assert failure['module'] == check and failure['exit'] != 0
        gate('true')
        assert run('restored') == 0
        result = dict(status='PASS', key_version=3, unchanged_replayed_modules=3,
                      transitive_change_rejected=True, restored_source_checked=True)
        (REPORT / 'cache-test.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result))
    finally:
        shutil.rmtree(ROOT / 'CertData/H1/Validation/RegenCache', ignore_errors=True)
        shutil.rmtree(artifact_path(parent).parent, ignore_errors=True)


if __name__ == '__main__':
    main()
