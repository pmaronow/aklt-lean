#!/usr/bin/env python3
"""Exercise portable paths, cold plans, and source checks without Lean or Lake."""
import argparse
import ast
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import types
from unittest.mock import patch

from refresh_manifests import check
from source_digest import source_digest
from verify_inputs import family_input_dir, verify

ROOT = Path(__file__).resolve().parents[1]


def run_checks(root):
    checks = {}
    for directory in ['scripts', 'AKLT/Cert/H1/tools', 'AKLT/Cert/H3']:
        for source in (root / directory).glob('*.py'):
            ast.parse(source.read_text(), filename=str(source))
    checks['python_syntax'] = True
    subprocess.run(['bash', '-n', root / 'scripts/cold-verify.sh', root / 'scripts/verify.sh'], check=True)
    checks['shell_syntax'] = True
    original_digest, _ = source_digest(root)
    build_existed = (root / '.lake/build').exists()
    with tempfile.TemporaryDirectory(prefix='aklt-pure-check-') as tmp:
        folder = Path(tmp)
        base_command = [sys.executable, str(root / 'scripts/cold_verify.py'),
                        '--verifier', str(folder / 'verifier'), '--report-dir', str(folder / 'unused report')]

        def plan(*extra):
            result = subprocess.run([*base_command, '--dry-run', *map(str, extra)],
                                    check=True, capture_output=True, text=True)
            return json.loads(result.stdout)

        default = plan('--input-dir', folder / 'numeric inputs')
        names = [s['stage'] for s in default['stages']]
        h1_names = ['H1-inputs', 'H1-reexport', 'H1-build', 'H1-verify', 'H1-close']
        assert [name for name in names if name.startswith('H1-')] == h1_names
        assert len(names) == 29 and default['H1_mode'] == 'numeric inputs'
        assert names.index('handwritten-build') < names.index('H3-generate') < names.index('H3-build') < names.index('H3-close') < names.index('H3-verify') < names.index('H1-inputs')
        assert names.index('H1-close') < names.index('close-CertData.Close.All') < names.index('close-Solution') < names.index('strict-full-audit') < names.index('statement-generation-check') < names.index('source-configuration') < names.index('module-headers') < names.index('physical-statement-comparison-and-negative-control')
        h1 = {s['stage']: s for s in default['stages'] if s['stage'].startswith('H1-')}
        assert h1['H1-build']['command'][h1['H1-build']['command'].index('--cap-gib') + 1] == '7'
        assert h1['H1-reexport']['command'][h1['H1-reexport']['command'].index('--scratch') + 1].endswith('/H1/export-scratch')
        assert '--install' in h1['H1-reexport']['command']
        assert h1['H1-inputs']['env']['H1_INPUT_DIR'].endswith('/numeric inputs/h1')
        for stage in h1.values():
            assert stage['env'] == h1['H1-inputs']['env']
        assert 'TBD-' not in json.dumps(default)
        assert not default['independent_full_unconditional_replay']
        high = plan('--jobs', 48, '--memory-gb', 300)
        by_name = {s['stage']: s for s in high['stages']}
        for family, jobs, memory in [('H1', '36', '270'), ('H3', '16', '170')]:
            command = by_name[family + '-build']['command']
            assert command[command.index('--jobs') + 1] == jobs
            assert float(command[command.index('--ram-gb') + 1]) == float(memory)
        override = plan('--h1-stage', folder / 'custom.py', '--memory-gb', 32)
        assert [s['stage'] for s in override['stages'] if s['stage'].startswith('H1-')] == ['H1-custom-stage']
        for extra in [('--jobs', '0'), ('--jobs', '49'), ('--memory-gb', '0'),
                      ('--memory-gb', 'nan'), ('--memory-gb', '32'),
                      ('--report-dir', str(root / 'verification/runs/test'))]:
            result = subprocess.run([*base_command, '--dry-run', *extra], capture_output=True, text=True)
            assert result.returncode == 2, (extra, result.returncode)
        assert not (folder / 'unused report').exists()
        checks['cold_plan'] = {'stages': len(names), 'default_H1_sequence': h1_names,
            'numeric_route_without_adapter': True, 'job_memory_caps': True,
            'spaces_in_paths': True, 'invalid_arguments_rejected': True,
            'existing_custom_stage_option_preserved': True, 'dry_run_creates_no_files': True}

        # Shared input defaults must not follow a scratch output root.
        variables = ['H1_INPUT_DIR', 'H1_REGEN_ROOT', 'H1_REGEN_REPORT']
        with patch.dict(os.environ):
            for name in variables:
                os.environ.pop(name, None)
            os.environ['H1_REGEN_ROOT'] = str(folder / 'scratch-output')
            values = runpy.run_path(str(root / 'AKLT/Cert/H1/tools/locations.py'))
            assert values['INPUT_DIR'] == root / 'data/h1'
            assert values['REPORT_DIR'] == root / 'verification/runs/H1'
            os.environ['H1_INPUT_DIR'] = str(folder / 'explicit input')
            os.environ['H1_REGEN_REPORT'] = str(folder / 'explicit report')
            values = runpy.run_path(str(root / 'AKLT/Cert/H1/tools/locations.py'))
            assert values['INPUT_DIR'] == folder / 'explicit input'
            assert values['REPORT_DIR'] == folder / 'explicit report'
        checks['H1_locations'] = {'one_input_setting': True, 'scratch_output_independent': True,
                                  'existing_report_override_preserved': True}
        with patch.dict(os.environ):
            for explicit in [False, True]:
                for variable in ['H3_INPUT_DIR', 'H3_REPORT_DIR']:
                    os.environ.pop(variable, None)
                if explicit:
                    os.environ.update(H3_INPUT_DIR=str(folder / 'H3 input'), H3_REPORT_DIR=str(folder / 'H3 report'))
                for name in ['production.py', 'export.py', 'generate_prefix.py']:
                    path = root / 'AKLT/Cert/H3' / name
                    wanted = {'ROOT', 'ARCHIVE', 'REPORT', 'report'}
                    nodes = [n for n in ast.walk(ast.parse(path.read_text())) if isinstance(n, ast.Assign) and
                             any(isinstance(t, ast.Name) and t.id in wanted for t in n.targets)]
                    ns = {'__file__': str(path), 'pathlib': __import__('pathlib'), 'os': os,
                          'ex': types.SimpleNamespace(ROOT=root)}
                    exec(compile(ast.Module(body=nodes, type_ignores=[]), '<location expressions>', 'exec'), ns)
                    if 'ARCHIVE' in ns:
                        assert ns['ARCHIVE'] == (folder / 'H3 input' if explicit else root / 'data/h3')
                    assert ns.get('REPORT', ns.get('report')) == (folder / 'H3 report' if explicit else root / 'verification/runs/H3')
        checks['H3_locations'] = {'all_three_entry_points': True, 'existing_overrides_preserved': True}

        # Evaluate only the H1 argument parser prefix. No signal handler, file
        # creation, scheduler, compiler query, or subprocess from the tool runs.
        path = root / 'AKLT/Cert/H1/tools/production_build.py'
        function = next(n for n in ast.parse(path.read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'main')
        prefix = []
        for node in function.body:
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and isinstance(node.value.func.value, ast.Name) and node.value.func.value.id == 'signal':
                break
            prefix.append(node)
        function.body = prefix + [ast.Return(value=ast.Name(id='args', ctx=ast.Load()))]
        ast.fix_missing_locations(function)
        for memory in [None, 160]:
            ns = {'argparse': argparse, 'Path': Path, 'MAX_JOBS': 36, 'MEMORY_LIMIT': 270_000_000_000,
                  'REPORT': folder, '__doc__': 'Resource argument parser fixture'}
            exec(compile(ast.Module(body=[function], type_ignores=[]), '<resource argument parser>', 'exec'), ns)
            argv = ['production_build.py', 'plan.json'] + (['--ram-gb', str(memory)] if memory else [])
            with patch.object(sys, 'argv', argv):
                args = ns['main']()
            assert ns['MEMORY_LIMIT'] == (memory or 270) * 1_000_000_000
            assert args.cap_gib == 8 and args.jobs == 32
        checks['H1_resource_option'] = {'default_270_GB_unchanged': True, 'explicit_limit_applied': True,
                                        'existing_default_jobs_and_process_cap_unchanged': True}

        # Tiny numeric-file fixtures exercise hash, size, and folder checks.
        input_root = folder / 'inputs'
        manifests = []
        for family in ['H1', 'H3']:
            directory = input_root / family.lower()
            directory.mkdir(parents=True)
            content = ('fixture-' + family).encode()
            (directory / 'witness.bin').write_bytes(content)
            pin = folder / (family + '.json')
            pin.write_text(json.dumps([{'name': 'witness.bin', 'bytes': len(content),
                                       'sha256': __import__('hashlib').sha256(content).hexdigest()}]))
            manifests.append((family, pin))
        assert len(verify(input_root, manifests)) == 2
        (input_root / 'h1').rename(input_root / 'H1')
        assert family_input_dir(input_root, 'H1') == input_root / 'H1'
        assert len(verify(input_root, manifests)) == 2
        (input_root / 'h1').mkdir()
        try:
            family_input_dir(input_root, 'H1')
        except ValueError:
            pass
        else:
            raise AssertionError('Ambiguous input directories accepted')
        (input_root / 'h1').rmdir()
        (input_root / 'H1/witness.bin').write_bytes(b'changed-H1')
        try:
            verify(input_root, manifests)
        except ValueError:
            pass
        else:
            raise AssertionError('Modified input accepted')
        checks['input_pins'] = {'small_positive_fixture': True, 'modified_input_rejected': True,
                                'uppercase_compatibility': True, 'ambiguous_case_rejected': True}

        # Check rendered statement bytes in memory. A one-byte read perturbation
        # exercises rejection without writing any Lean file.
        from make_challenge import render
        challenge, metadata = render(root)
        assert challenge == (root / 'Challenge.lean').read_bytes()
        assert metadata == (root / 'verification/statement-sources.json').read_bytes()
        checks['statement_bytes'] = True
        original_read = Path.read_bytes

        def altered_read(path):
            raw = original_read(path)
            return raw + b'\n' if path == root / 'Challenge.lean' else raw

        with patch.object(Path, 'read_bytes', altered_read):
            rejected = check(root)
        assert not rejected['passed'] and any(issue['file'] == 'Challenge.lean' for issue in rejected['issues'])
        checks['altered_statement_bytes_rejected_without_source_write'] = True

    manifests = check(root)
    assert manifests['passed'], manifests['issues']
    checks['current_manifests'] = manifests
    current_digest, _ = source_digest(root)
    assert current_digest == original_digest
    assert (root / '.lake/build').exists() == build_existed
    checks['no_compiler_runner_or_build_directory_created'] = True
    return {'passed': True, 'checks': checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=ROOT)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    result = run_checks(args.project.resolve())
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
