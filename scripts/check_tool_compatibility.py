#!/usr/bin/env python3
"""Check tool compatibility with a source revision using only Python and Git.

Synthetic hash/key/receipt probes do not invoke a compiler or verify a proof.
"""
import argparse
import ast
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import types
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


def strip_docs(tree):
    class Docs(ast.NodeTransformer):
        def visit_Module(self, node):
            return self.body(node)

        def visit_FunctionDef(self, node):
            return self.body(node)

        def visit_ClassDef(self, node):
            return self.body(node)

        def body(self, node):
            self.generic_visit(node)
            if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
                node.body = node.body[1:]
            return node
    return Docs().visit(tree)


def functions(source):
    result = {}

    def walk(body, parent=''):
        for node in body:
            if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
                name = parent + node.name
                copy = strip_docs(ast.parse(ast.unparse(node)))
                result[name] = hashlib.sha256(ast.dump(copy, include_attributes=False).encode()).hexdigest()
                walk(node.body, name + '.')
    walk(ast.parse(source).body)
    return result


def select(source, names, namespace):
    nodes = [n for n in ast.parse(source).body if isinstance(n, (ast.FunctionDef, ast.ClassDef)) and n.name in names]
    exec(compile(ast.Module(body=nodes, type_ignores=[]), '<compatibility probe>', 'exec'), namespace)
    return namespace


def run_checks(root, baseline):
    old = lambda name: subprocess.check_output(['git', '-C', str(root), 'show', baseline + ':' + name], text=True)
    tracked = subprocess.check_output(['git', '-C', str(root), 'ls-tree', '-r', '--name-only', baseline], text=True).splitlines()
    old_tools = [n for n in tracked if n.startswith(('AKLT/Cert/H1/tools/', 'AKLT/Cert/H3/')) and n.endswith('.py')]
    deleted = sorted(n for n in old_tools if not (root / n).exists())
    changed = {}
    for name in old_tools:
        if not (root / name).exists():
            continue
        before, after = functions(old(name)), functions((root / name).read_text())
        differences = sorted(n for n in set(before) | set(after) if before.get(n) != after.get(n))
        if differences:
            changed[name] = differences
    expected = {
        'AKLT/Cert/H1/tools/packed.py': ['main'],
        'AKLT/Cert/H1/tools/production_bridge_export.py': ['main'],
        'AKLT/Cert/H1/tools/production_coverage.py': ['main'],
        'AKLT/Cert/H1/tools/production_export.py': ['main'],
        'AKLT/Cert/H1/tools/production_receipts.py': ['inputs'],
        'AKLT/Cert/H1/tools/production_build.py': ['main'],
        'AKLT/Cert/H3/export.py': ['main'],
    }
    if changed != expected:
        raise AssertionError('Unexpected function changes: ' + json.dumps(changed, indent=2))
    # Every other retained function, including emitters, bundle builders, full
    # verifiers, dependency hashing, and the H1 compiler/receipt body, is exact.
    important = {
        'AKLT/Cert/H1/tools/production_build.py': ['build_key', 'library_fingerprint', 'artifact_hashes', 'axiom_audit', 'main.run'],
        'AKLT/Cert/H1/tools/production_receipts.py': ['verify'],
        'AKLT/Cert/H1/tools/production_reexport.py': ['main'],
        'AKLT/Cert/H1/tools/production_bundle.py': ['main'],
        'AKLT/Cert/H3/regen.py': ['context', 'source_info', 'dep_hashes', 'run_one', 'verify', 'current'],
        'AKLT/Cert/H3/production.py': ['source', 'generate_graph', 'generate_case', 'generate_assemblies'],
    }
    for name, required in important.items():
        before, after = functions(old(name)), functions((root / name).read_text())
        for function in required:
            if function not in before or before[function] != after.get(function):
                raise AssertionError(name + ': changed ' + function)

    # Normalize only the approved input/report selection expressions and compare
    # the complete ASTs, not just function names. This also protects numeric data
    # and string templates in module-level code.
    class Locations(ast.NodeTransformer):
        def visit_Call(self, node):
            self.generic_visit(node)
            if isinstance(node.func, ast.Name) and node.func.id == 'Path' and len(node.args) == 1 and isinstance(node.args[0], ast.Constant):
                if isinstance(node.args[0].value, str) and node.args[0].value.endswith('/data/h1'):
                    return ast.copy_location(ast.Name(id='INPUT_DIR', ctx=ast.Load()), node)
            if isinstance(node.func, ast.Attribute) and node.func.attr == 'get' and len(node.args) == 2 and isinstance(node.args[0], ast.Constant) and node.args[0].value in {'H1_REGEN_REPORT', 'H3_REPORT_DIR', 'H3_INPUT_DIR'}:
                node.args[1] = ast.Constant(value='<repository-relative default>')
            return node

        def visit_Assign(self, node):
            self.generic_visit(node)
            if any(isinstance(t, ast.Name) and t.id == 'REPORT' for t in node.targets):
                node.value = ast.Constant(value='<report setting>')
            return node

        def visit_ImportFrom(self, node):
            return None if node.module == 'locations' else node
    for name in old_tools:
        if not (root / name).exists() or name == 'AKLT/Cert/H1/tools/production_build.py':
            continue
        a = Locations().visit(strip_docs(ast.parse(old(name))))
        b = Locations().visit(strip_docs(ast.parse((root / name).read_text())))
        if ast.dump(a, include_attributes=False) != ast.dump(b, include_attributes=False):
            raise AssertionError('Non-location/template AST difference: ' + name)

    class ResourceOption(Locations):
        def visit_Global(self, node):
            return None if set(node.names) <= {'REPORT', 'MEMORY_LIMIT'} else node

        def visit_Expr(self, node):
            if isinstance(node.value, ast.Call) and node.value.args and isinstance(node.value.args[0], ast.Constant) and node.value.args[0].value == '--ram-gb':
                return None
            return self.generic_visit(node)

        def visit_If(self, node):
            # The two new conditions validate the optional aggregate resource
            # limit. Neither condition writes a receipt or modifies proof data.
            if any(isinstance(x, ast.Attribute) and x.attr == 'ram_gb' for x in ast.walk(node.test)):
                return None
            return self.generic_visit(node)

        def visit_Assign(self, node):
            if any(isinstance(t, ast.Name) and t.id == 'MEMORY_LIMIT' for t in node.targets) and any(isinstance(x, ast.Attribute) and x.attr == 'ram_gb' for x in ast.walk(node.value)):
                return None
            return super().visit_Assign(node)

    builder = 'AKLT/Cert/H1/tools/production_build.py'
    before = ResourceOption().visit(strip_docs(ast.parse(old(builder))))
    after = ResourceOption().visit(strip_docs(ast.parse((root / builder).read_text())))
    if ast.dump(before, include_attributes=False) != ast.dump(after, include_attributes=False):
        raise AssertionError('H1 builder differs beyond locations and the new resource option')

    probes = {}
    with tempfile.TemporaryDirectory(prefix='aklt-tool-probe-') as tmp:
        folder = Path(tmp)
        payload = folder / 'source.txt'
        payload.write_text('module\npublic import AKLT.Cert.H1.Production.Basic\npublic import CertData.H1.Generated.Sample\n')
        for n in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']:
            (folder / n).write_text('synthetic pin ' + n + '\n')
        h1 = 'AKLT/Cert/H1/tools/production_build.py'
        keys = []
        for source in [old(h1), (root / h1).read_text()]:
            ns = {'Path': Path, 'ROOT': folder, 'hashlib': hashlib, 'json': json,
                're': __import__('re'), 'gzip': __import__('gzip'), '_files': {}, '_pins': None,
                'library_fingerprint': lambda name: 'fixed-library-fingerprint:' + name}
            select(source, {'source_bytes', 'sha', 'file_digest', 'imports', 'build_key'}, ns)
            dependencies = [{'module': 'CertData.H1.Generated.Sample', 'key': 'fixed-generated-key',
                             'artifact_hashes': {'Sample.olean': 'fixed-artifact-digest'}}]
            keys.append(ns['build_key'](payload, dependencies))
        assert keys[0] == keys[1]
        probes['H1_build_key_identical'] = True
        audit_source = 'namespace Example\ntheorem checked : True := True.intro\n#print axioms checked\nend Example\n'
        audit_log = "'Example.checked' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        audits = []
        for source in [old(h1), (root / h1).read_text()]:
            ns = {'re': __import__('re'), 'ALLOWED': {'propext', 'Classical.choice', 'Quot.sound'}}
            select(source, {'axiom_audit'}, ns)
            audits.append(ns['axiom_audit'](audit_log, audit_source))
            try:
                ns['axiom_audit'](audit_log.replace('propext', 'Forbidden'), audit_source)
            except RuntimeError:
                pass
            else:
                raise AssertionError('Axiom negative control was accepted')
        assert audits[0] == audits[1]
        probes['H1_axiom_format_and_rejection_identical'] = True
        # The input receipt record remains identical at an explicitly selected
        # location. Redirect only the old literal for this synthetic fixture.
        data = folder / 'data'
        data.mkdir()
        (data / 'chunk.bin').write_bytes(b'integer witness fixture')
        (data / 'index.json').write_text(json.dumps({'chunks': [{'file': 'chunk.bin'}]}))
        receipt_source = 'AKLT/Cert/H1/tools/production_receipts.py'
        receipts = []
        for i, source in enumerate([old(receipt_source), (root / receipt_source).read_text()]):
            ns = {'Path': (lambda value: data) if i == 0 else Path, 'INPUT_DIR': data,
                  'json': json, 'sha': lambda path: hashlib.sha256(path.read_bytes()).hexdigest()}
            select(source, {'inputs'}, ns)
            output = folder / ('inputs-' + str(i) + '.json')
            with contextlib.redirect_stdout(io.StringIO()):
                ns['inputs'](types.SimpleNamespace(output=output))
            receipts.append(output.read_bytes())
        assert receipts[0] == receipts[1]
        probes['H1_input_receipt_bytes_identical'] = True
        # H3 context uses a mocked version query and synthetic tracked bytes.
        # No executable is started and no compiled object is accepted as proof.
        h3 = 'AKLT/Cert/H3/regen.py'
        binary = folder / 'compiler-fixture'
        binary.write_bytes(b'fixed compiler bytes')
        artifact = folder / 'artifact-fixture'
        artifact.write_bytes(b'fixed artifact bytes')
        results = []
        for source in [old(h3), (root / h3).read_text()]:
            saved = {}
            calls = []
            def query(command, **kwargs):
                calls.append(command)
                if command[0] == 'git':
                    return 'source.txt\n'
                if command == ['lean', '--version']:
                    return 'synthetic Lean version\n'
                raise AssertionError(command)
            ns = {'ROOT': folder, 'REPORT': folder, 'Path': Path, 'json': json, 'hashlib': hashlib,
                  'subprocess': types.SimpleNamespace(check_output=query),
                  'shutil': types.SimpleNamespace(which=lambda *a, **k: str(binary)),
                  'save': lambda path, value: saved.update({str(path.name): value}),
                  'artifacts': lambda module: [artifact]}
            select(source, {'sha', 'digest', 'context', 'dep_hashes'}, ns)
            value = ns['context']({'PATH': 'synthetic-bin', 'LEAN_PATH': 'fixed-import-path'})
            deps = ns['dep_hashes']({'deps': ['AKLT.Sample', 'CertData.Sample', 'Mathlib']})
            results.append((value, saved, deps))
        assert results[0] == results[1]
        probes['H3_context_and_dependency_hashes_identical'] = True

    # Compare complete module envelopes and emitted templates in memory.
    module = 'AKLT/Cert/H1/tools/module_source.py'
    templates = []
    for source in [old(module), (root / module).read_text()]:
        ns = {'__name__': 'compatibility_module', '__file__': str(root / module)}
        exec(compile(source, '<H1 source envelope>', 'exec'), ns)
        raw = 'import Init\nnamespace Example\ndef datum : Nat := 7\ntheorem checked : datum = 7 := rfl\n#print axioms checked\nend Example\n'
        templates.append(ns['module_source'](raw))
    assert templates[0] == templates[1]
    probes['H1_module_envelope_bytes_identical'] = True
    production = 'AKLT/Cert/H3/production.py'
    templates = []
    for source in [old(production), (root / production).read_text()]:
        ns = {'__name__': 'compatibility_module', '__file__': str(root / production)}
        exec(compile(source, '<H3 source envelope>', 'exec'), ns)
        sample = root / 'CertData/H3/Example/Check.lean'
        body = 'def datum : Nat := h3_hex% "7"\ntheorem checked : datum = 7 := by decide +kernel\n'
        templates.append(ns['source'](sample, ['CertData.H3.Kernel.Literal'], body))
    assert templates[0] == templates[1]
    probes['H3_module_template_bytes_identical'] = True

    return {'passed': True, 'baseline': baseline, 'deleted_tools': deleted,
        'unchanged_key_verifier_emitter_functions': important,
        'function_changes_limited_to': expected, 'all_other_retained_function_ASTs_identical': True,
        'all_nonresource_tool_AST_changes_are_only_paths_imports_or_docstrings': True,
        'synthetic_probes': probes, 'compiler_or_runner_started': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', default='42b16c3')
    parser.add_argument('--project', type=Path, default=ROOT)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    result = run_checks(args.project.resolve(), args.baseline)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
