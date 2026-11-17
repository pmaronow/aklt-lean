#!/usr/bin/env python3
"""Compare the physical statement in separate environments, with a negative control.

This compares reflexive attachment theorems, not the unconditional proof export.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True


def compare(args, negative):
    work = args.report_dir.resolve() / ('negative-spin' if negative else 'positive')
    work.mkdir(parents=True)
    lib = work / 'lib'
    lib.mkdir()
    env = dict(os.environ, LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env.get('PATH', '')
    tc = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=ROOT, env=env, text=True).strip())
    paths = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, env=env, text=True).strip().split(os.pathsep)
    env['LEAN_PATH'] = os.pathsep.join([str(lib)] + [str((ROOT / p).resolve()) for p in paths if p])
    challenge = (ROOT / 'Challenge.lean').read_text()
    if negative:
        needle = 'then (2 : ℂ) - (i.val : ℂ)'
        if challenge.count(needle) != 1:
            raise RuntimeError('Negative-control spinZ location is ambiguous')
        challenge = challenge.replace(needle, 'then (3 : ℂ) - (i.val : ℂ)')
    placeholder = 'theorem aklt_gap : Main := by\n  sorry'
    if challenge.count(placeholder) != 1:
        raise RuntimeError('Expected exactly one conventional Challenge placeholder')
    challenge = challenge.replace(placeholder,
        'theorem main_iff : Main ↔ AKLT.Challenge.MainStatementV2 := Iff.rfl')
    solution = '''module
public import AKLT.Challenge.MainV2
@[expose] public section
namespace AKLTPalomar
def Main : Prop := AKLT.Challenge.MainStatementV2
theorem main_iff : Main ↔ AKLT.Challenge.MainStatementV2 := Iff.rfl
end AKLTPalomar
'''
    modules = [('challenge', 'PhysicalChallenge', challenge), ('solution', 'PhysicalSolution', solution)]
    receipt = {'scope': 'physical statement identity only; no unconditional proof replay',
               'negative_control': negative, 'stages': []}

    def run(name, command, cwd=ROOT, command_env=env, allow_failure=False):
        out = work / 'stages' / name
        subprocess.run([sys.executable, ROOT / 'scripts/measure_stage.py', '--stage', name,
            '--out', out, '--cwd', cwd, '--rss-cap-gb', str(args.memory_gb),
            '--address-space-gib', '0', '--max-lean', '1', '--', *map(str, command)],
            cwd=ROOT, env=command_env, check=False, stdout=subprocess.DEVNULL)
        result = json.loads((out / 'result.json').read_text())
        receipt['stages'].append(result)
        if (result['exit_code'] or result['limit']) and not allow_failure:
            raise RuntimeError(name + ' failed: ' + str(out))
        return result, out

    sys.path.insert(0, str(args.verifier.resolve()))
    from scripts import verify_submission as official
    targets = ['AKLTPalomar.main_iff', *official.primitive_targets(tc)]
    exports = work / 'exports'
    exports.mkdir()
    for side, module, text in modules:
        source = work / (module + '.lean')
        source.write_text(text)
        run('build-' + side, [tc / 'bin/lean', '-j1', '-DautoImplicit=false',
            '-DrelaxedAutoImplicit=false', '--root=' + str(work), source, '-o', lib / (module + '.olean')])
        _, out = run('export-' + side, [tc / 'bin/leanexport', module, '--', *targets])
        target = exports / (side + '.ndjson')
        os.link(out / 'stdout.log', target)
        official.verify_export(target)
        with target.open('rb') as stream:
            export_hash = hashlib.file_digest(stream, 'sha256').hexdigest()
        receipt[side + '_export'] = {'bytes': target.stat().st_size, 'sha256': export_hash}
    bwrap = args.bwrap.resolve() if args.bwrap else Path(shutil.which('bwrap') or '/nonexistent')
    if not bwrap.is_file():
        raise RuntimeError('Provide bubblewrap with --bwrap or PATH')
    if subprocess.check_output([bwrap, '--version'], text=True).strip() != 'bubblewrap 0.12.0':
        raise RuntimeError('The recorded Comparator requires bubblewrap 0.12.0')
    config = work / 'comparator.json'
    official.protected_comparator_config(ROOT / 'comparator.json', config,
        kernels={'nanoda': [str(tc / 'bin/nanoda_bin')]})
    cfg = json.loads(config.read_text())
    cfg['theorem_names'] = ['AKLTPalomar.main_iff']
    cfg['definition_names'] = []
    config.write_text(json.dumps(cfg, indent=2) + '\n')
    judge = work / 'judge'
    for directory in ['project', 'home', 'tmp']:
        (judge / directory).mkdir(parents=True)
    judge_env = {'PATH': str(tc / 'bin') + ':/usr/bin:/bin', 'HOME': str(judge / 'home'),
        'TMPDIR': str(judge / 'tmp'), 'LEAN_ABORT_ON_PANIC': '1', 'COMPARATOR_BWRAP': str(bwrap)}
    command = official.bwrap_command([str(tc / 'bin/lake'), 'comparator', '--config', str(config),
        '--challenge-from-export', str(exports / 'challenge.ndjson'),
        '--solution-from-export', str(exports / 'solution.ndjson')], bwrap=bwrap,
        writable_directories=[judge], readable_paths=[config, exports / 'challenge.ndjson',
            exports / 'solution.ndjson', *official.system_readable_paths()],
        executable_paths=sorted({tc, bwrap, *(p.resolve() for p in map(Path, ['/usr', '/bin', '/lib', '/lib64']) if p.exists())}),
        environment=judge_env, readable_directories=[judge / 'project'], nested_sandbox=True)
    result, out = run('comparator', command, judge / 'project', env, allow_failure=negative)
    transcript = (out / 'stdout.log').read_text() + (out / 'stderr.log').read_text()
    if negative:
        passed = (result['exit_code'] != 0 and not result['limit'] and
                  "Const does not match between challenge and target 'AKLT.Challenge.bondCasimir'" in transcript)
    else:
        passed = (result['exit_code'] == 0 and not result['limit'] and
            'nanoda kernel accepts the solution' in transcript and
            'Lean default kernel accepts the solution' in transcript)
    receipt['passed'] = passed
    (work / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if not passed:
        raise RuntimeError('Unexpected Comparator outcome: ' + str(out))
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verifier', type=Path, required=True)
    parser.add_argument('--report-dir', type=Path, required=True)
    parser.add_argument('--bwrap', type=Path)
    parser.add_argument('--memory-gb', type=float, default=160)
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    if args.report_dir.resolve().is_relative_to(ROOT):
        parser.error('Reports must be outside the source tree; diagnostic Lean files are not repository sources')
    if args.dry_run:
        print(json.dumps({'cases': ['physical identity: Lean and NanoDa', 'spinZ 2 to 3: required mismatch at bondCasimir'],
            'report_dir': str(args.report_dir.resolve()), 'executes_commands': False}, indent=2))
        return
    compare(args, False)
    compare(args, True)
    print('PASS: physical statement identity and expected negative-control rejection')


if __name__ == '__main__':
    main()
