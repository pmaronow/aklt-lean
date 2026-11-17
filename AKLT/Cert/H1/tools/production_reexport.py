#!/usr/bin/env python3
"""Regenerate every H1 owner directly from pinned integer inputs, then compare.

The scratch directory is separate from accepted production sources. This checks
all owners, rather than only the sample required for mechanical transformation.
"""
import argparse, hashlib, json, os, subprocess, sys, time
from pathlib import Path
from production_build import ROOT, REPORT, source_bytes, guard


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--scratch', type=Path, required=True)
    ap.add_argument('--report-dir', type=Path, default=REPORT)
    ap.add_argument('--install', action='store_true', help='install the fresh owners when no production source exists')
    args = ap.parse_args()
    args.scratch.mkdir(parents=True, exist_ok=True)
    report = args.scratch / 'reports'
    report.mkdir(exist_ok=True)
    env = dict(os.environ, H1_REGEN_ROOT=str(args.scratch.resolve()), H1_REGEN_REPORT=str(report.resolve()))
    tools = Path(__file__).resolve().parent
    steps = [
        ['production_export.py', '--all', '--manifest', str(report / 'production-manifest.json')],
        ['production_bridge_export.py', str(report / 'production-manifest.json'), '--output', str(report / 'production-complete.json')],
        ['production_coverage.py', '--manifest', str(report / 'coverage-manifest.json')],
        ['production_index.py', str(report / 'production-complete.json'), '--representatives', str(report / 'representatives.json'), '--coverage', str(report / 'coverage-manifest.json'), '--output', str(report / 'production-final.json')],
        ['production_bundle.py', str(report / 'production-manifest.json'), '--label', 'Batch', '--output', str(report / 'production-batched.json')],
        ['production_bundle.py', str(report / 'production-final.json'), '--base', str(report / 'production-batched.json'), '--label', 'Bridge', '--output', str(report / 'production.json')],
    ]
    begin = time.monotonic()
    for step in steps:
        guard()
        subprocess.run([sys.executable, str(tools / step[0]), *step[1:]], cwd=ROOT, env=env, check=True)
    plan = json.loads((report / 'production.json').read_text())
    expected = set(json.loads((ROOT / 'verification/generated-modules.json').read_text())['H1'])
    assert {j['module'] for j in plan['jobs']} == expected, 'owner map differs from release inventory'
    matches = []
    for job in plan['jobs']:
        rel = job['module'].replace('.', '/') + '.lean'
        fresh = (args.scratch / rel).read_bytes()
        destination = ROOT / rel
        if args.install:
            if destination.exists() or Path(str(destination) + '.gz').exists():
                raise RuntimeError('refusing to overwrite production source: ' + rel)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(fresh)
        else:
            accepted = source_bytes(destination)
            if accepted != fresh:
                raise RuntimeError('byte comparison failed: ' + rel)
        matches.append(dict(module=job['module'], sha256=hashlib.sha256(fresh).hexdigest()))
    args.report_dir.mkdir(parents=True, exist_ok=True)
    receipt = dict(format='h1-data-only-reexport-v1', success=True, mode='install' if args.install else 'compare',
                   modules=len(matches), patterns=len(plan['patterns']),
                   logical_components=len(plan['unbundled_jobs']),
                   wall_seconds=time.monotonic() - begin, sources=matches)
    (args.report_dir / 'data-only-reexport.json').write_text(json.dumps(receipt, indent=2) + '\n')
    plan['data_root'] = str(ROOT / 'CertData/H1/Generated')
    for job in plan['jobs']:
        if job['kind'] in ['case_data', 'case_assembly', 'index_witness_assembly']:
            job['cap_gib'] = 16
        elif job['kind'] in ['all_witness_assembly', 'target_assembly']:
            job['cap_gib'] = 64
    (args.report_dir / 'data-only-production.json').write_text(json.dumps(plan, separators=(',', ':')) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'sources'}), flush=True)


if __name__ == '__main__':
    main()
