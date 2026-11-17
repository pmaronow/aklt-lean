#!/usr/bin/env python3
"""Verify the complete formalization from sources in a fresh checkout.

The certificate families use memory-guarded direct Lean compilations. No
unconditional monolithic independent-kernel replay is implied by this driver.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'scripts'))
from source_digest import source_digest


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=12, help='Maximum Lean compiler processes / Lake worker setting')
    parser.add_argument('--memory-gb', type=float, default=160, help='Sampled process-tree RSS limit in decimal GB')
    parser.add_argument('--input-dir', type=Path, default=ROOT / 'data', help='Parent of H1/ and H3/ numeric inputs')
    parser.add_argument('--report-dir', type=Path, default=ROOT.parent / (ROOT.name + '-verification'))
    parser.add_argument('--verifier', type=Path, default=os.environ.get('PALOMAR_VERIFIER'),
                        help='Official PalomarSubmission checkout; or PALOMAR_VERIFIER')
    parser.add_argument('--verifier-commit', default='14aa8d6b3c2f14a8540605e37144560b9a00e7e7')
    parser.add_argument('--bwrap', type=Path, help='Bubblewrap 0.12.0; otherwise use PATH')
    parser.add_argument('--h1-stage', type=Path,
        help='Final H1 adapter: Python script accepting --project, --input-dir, --report-dir, --jobs, --memory-gb')
    parser.add_argument('--dry-run', action='store_true', help='Print the complete plan; run no command and create no files')
    args = parser.parse_args()
    if not 1 <= args.jobs <= 48 or args.memory_gb <= 0:
        parser.error('Use 1..48 jobs and a positive memory limit')
    for name in ['input_dir', 'report_dir', 'verifier', 'bwrap', 'h1_stage']:
        value = getattr(args, name)
        if value is not None:
            setattr(args, name, Path(value).resolve())
    if args.report_dir.is_relative_to(ROOT):
        parser.error('--report-dir must be outside the checkout (diagnostic Lean files are not sources)')
    if not args.verifier:
        parser.error('Set --verifier or PALOMAR_VERIFIER')
    return args


def main():
    args = arguments()
    work = args.report_dir
    python = sys.executable
    h1 = work / 'H1'
    h3 = work / 'H3'
    guard = [python, str(ROOT / 'scripts/measure_stage.py')]
    stages = []

    def add(name, command, cwd=ROOT, env=None, allow_failure=False):
        stages.append({'stage': name, 'command': list(map(str, command)), 'cwd': str(cwd),
                       'env': env or {}, 'allow_failure': allow_failure})

    # Every dependency is fetched at the exact lake-manifest revision. This
    # materializes sources and downloads the cache; it never invokes lake update.
    setup = '''import os,sys\nfrom pathlib import Path\nsys.dont_write_bytecode=True\nsys.path.insert(0,sys.argv[1])\nfrom scripts.verify_submission import materialize_packages\np=Path(sys.argv[2]);materialize_packages(p,checkout=p,base_env=os.environ.copy())\n'''
    add('pinned-dependency-fetch', [python, '-c', setup, args.verifier, ROOT])
    nested = "from pathlib import Path;import sys;p=Path(sys.argv[1]);n=p/'mathlib/.lake/packages';n.parent.mkdir(exist_ok=True);n.symlink_to(p,target_is_directory=True) if not n.exists() else None"
    add('mathlib-package-links', [python, '-c', nested, ROOT / '.lake/packages'])
    # Use lake env from the root so all pinned sibling dependencies are visible.
    add('pinned-mathlib-cache', ['lake', 'exe', 'cache', 'get'])
    add('cache-no-build-preflight', ['lake', '--no-build', 'build', 'Mathlib'])
    add('handwritten-build', ['lake', 'build', 'Handwritten', 'Challenge', 'Regression.Solution',
        'Regression.Audit', 'AuditHandwritten', 'RegenSamples.H1Consumer', 'RegenSamples.H3Consumer'])
    add('strict-handwritten-audit', ['lake', 'env', 'lean', '-j1', '-DElab.async=false',
        '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-DwarningAsError=true', 'AuditHandwritten.lean'])
    add('handwritten-axiom-transcript', [python, ROOT / 'scripts/check_axioms.py',
        work / 'stages/strict-handwritten-audit/stdout.log', '--mode', 'handwritten'])
    add('input-pins', [python, ROOT / 'scripts/verify_inputs.py', '--input-dir', args.input_dir,
        '--report', work / 'input-pins.json'])
    h3env = {'H3_INPUT_DIR': str(args.input_dir / 'H3'), 'H3_REPORT_DIR': str(h3)}
    h3command = [python, ROOT / 'AKLT/Cert/H3/regen.py']
    add('H3-generate', [*h3command, 'generate'], env=h3env)
    add('H3-build', [*h3command, 'build', '--jobs', min(args.jobs, 16),
        '--ram-gb', min(170, max(1, int(args.memory_gb))), '--process-gib', '64'], env=h3env)
    add('H3-close', [*h3command, 'close', '--stage', 'closing', '--jobs', '1',
        '--ram-gb', min(170, max(1, int(args.memory_gb))), '--process-gib', '64'], env=h3env)
    add('H3-verify', [*h3command, 'verify'], env=h3env)
    if args.h1_stage:
        h1command = [python, args.h1_stage, '--project', ROOT, '--input-dir', args.input_dir / 'H1',
            '--report-dir', h1, '--jobs', min(args.jobs, 36), '--memory-gb', args.memory_gb]
    else:
        # TBD-H1-PORTABLE-ENTRYPOINT: complete this call after the H1 hand-back.
        # AKLT/Cert/H1/tools/production_regen.py is the hand-back reference;
        # its retained-source arguments are not a numeric-input-only interface.
        # The numeric route is production_reexport.py --install followed by
        # production_build.py, production_receipts.py verify, production_close.py.
        # The current exporters still hard-code the campaign input directory.
        h1command = [python, ROOT / 'AKLT/Cert/H1/tools/production_regen.py',
            'TBD-H1-PORTABLE-ENTRYPOINT']
    add('H1-generate-build-close-verify', h1command,
        env={'H1_INPUT_DIR': str(args.input_dir / 'H1'), 'H1_REGEN_REPORT': str(h1)})
    for module in ['CertData.H1.Close.Main', 'CertData.H1.Close.Audit', 'CertData.H3.Close.Main',
                   'CertData.Close.All', 'Solution', 'Audit']:
        source = Path(module.replace('.', '/') + '.lean')
        obj = ROOT / '.lake/build/lib/lean' / source.with_suffix('.olean')
        add('close-' + module, ['lake', 'env', 'lean', '-j1', '-DElab.async=false',
            '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-DwarningAsError=true', '-o', obj, source])
    add('strict-full-audit', ['lake', 'env', 'lean', '-j1', '-DElab.async=false',
        '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-DwarningAsError=true', 'Audit.lean'])
    add('full-axiom-transcript', [python, ROOT / 'scripts/check_axioms.py',
        work / 'stages/strict-full-audit/stdout.log', '--mode', 'full'])
    add('statement-generation-check', [python, ROOT / 'scripts/make_challenge.py', '--check'])
    add('source-configuration', [python, ROOT / 'scripts/verify_sources.py', '--verifier', args.verifier,
        '--report', work / 'source-checks.json'], allow_failure=True)
    add('module-headers', [python, ROOT / 'scripts/verify_headers.py', '--verifier', args.verifier,
        '--report', work / 'headers.json'])
    comparison = [python, ROOT / 'scripts/compare_statement.py', '--verifier', args.verifier,
                  '--report-dir', work / 'statement', '--memory-gb', args.memory_gb]
    if args.bwrap:
        comparison += ['--bwrap', args.bwrap]
    add('physical-statement-comparison-and-negative-control', comparison)
    plan = {'scope': 'complete source build, strict axiom audits, and physical statement comparison',
        'independent_full_unconditional_replay': False, 'jobs': args.jobs, 'memory_gb': args.memory_gb,
        'input_dir': str(args.input_dir), 'report_dir': str(work), 'stages': stages,
        'H1_integration': 'configured adapter' if args.h1_stage else 'TBD-H1-PORTABLE-ENTRYPOINT; fails before any build'}
    if args.dry_run:
        print(json.dumps(plan, indent=2))
        return 0
    if not args.h1_stage:
        raise SystemExit('TBD-H1-PORTABLE-ENTRYPOINT: supply --h1-stage after the H1 hand-back; see docs/regeneration/H1-INTEGRATION.md. No command was run.')
    if not args.h1_stage.is_file():
        raise SystemExit('The --h1-stage adapter does not exist')
    if (ROOT / '.lake/build').exists():
        raise SystemExit('Use a fresh checkout without .lake/build; no build objects are deleted by this script')
    if (ROOT / '.lake/packages').exists():
        raise SystemExit('Cold verification fetches its own pinned packages; start without .lake/packages')
    if work.exists():
        raise SystemExit('Use a new report directory')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        raise SystemExit('Commit all source/documentation changes before a cold verification')
    pin = subprocess.check_output(['git', '-C', str(args.verifier), 'rev-parse', 'HEAD'], text=True).strip()
    if pin != args.verifier_commit:
        raise SystemExit('Official verifier commit differs from --verifier-commit')
    work.mkdir(parents=True)
    (work / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
    before, listing = source_digest(ROOT)
    (work / 'lean-source-digest.txt').write_text(before + '\n')
    (work / 'lean-sources.sha256').write_bytes(listing)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', GIT_TERMINAL_PROMPT='0',
               LEAN_NUM_THREADS=str(args.jobs), MATHLIB_CACHE_DIR=str(work / 'mathlib-cache'))
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env.get('PATH', '')
    env['ELAN_TOOLCHAIN'] = (ROOT / 'lean-toolchain').read_text().strip()
    for key in ['LAKE_PKG_URL_MAP', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
        env.pop(key, None)
    receipt = {'status': 'running', 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'source_digest': before, 'verifier_commit': pin, 'stages': [],
        'independent_full_unconditional_replay': False}
    started = time.monotonic()

    def save():
        receipt['wall_seconds'] = time.monotonic() - started
        (work / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    save()
    try:
        for stage in stages:
            name = stage['stage']
            out = work / 'stages' / name
            if name.startswith('close-'):
                Path(stage['command'][-2]).parent.mkdir(parents=True, exist_ok=True)
            command = [*guard, '--stage', name, '--out', str(out), '--cwd', stage['cwd'],
                '--rss-cap-gb', str(args.memory_gb), '--address-space-gib', '0',
                '--max-lean', str(args.jobs), '--', *stage['command']]
            receipt['current_stage'] = name
            save()
            print('+ ' + shlex.join(stage['command']), flush=True)
            result = subprocess.run(command, cwd=ROOT, env={**env, **stage['env']}, check=False)
            measurement = json.loads((out / 'result.json').read_text())
            receipt['stages'].append(measurement)
            save()
            if measurement['limit'] or (result.returncode and not stage['allow_failure']):
                raise RuntimeError(name + ' failed; see ' + str(out))
            if name == 'source-configuration':
                checks = json.loads((work / 'source-checks.json').read_text())
                author_owned = {'package.metadata_todo', 'package.license_missing'}
                failures = [x for x in checks['issues'] if x['code'] not in author_owned]
                if failures or checks['generated_missing']:
                    raise RuntimeError('Source/configuration or generated inventory check failed')
                receipt['author_metadata_findings'] = checks['issues']
        after, _ = source_digest(ROOT)
        if after != before:
            raise RuntimeError('Tracked Lean sources/build pins changed during verification')
        receipt['status'] = 'complete'
        receipt['audit_transcript'] = 'stages/strict-full-audit/stdout.log'
        receipt['full_unconditional_lean_kernel_build'] = True
        save()
    except BaseException as error:
        receipt.update(status='incomplete', error=str(error))
        save()
        raise
    print(str(work / 'receipt.json'))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
