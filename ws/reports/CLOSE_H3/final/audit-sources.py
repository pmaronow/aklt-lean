#!/usr/bin/env python3
"""Audit new handwritten sources over the complete project import closure."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path('/home/ubuntu/aklt/wt/CLOSE_H3')
REPORT = Path('/home/ubuntu/aklt/reports/CLOSE_H3/final')


def strip_comments(text):
    out = []
    i, depth = 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append('\n' if text[i] == '\n' else ' ' if depth else text[i])
            i += 1
    assert depth == 0
    return ''.join(out)


def main():
    h1 = json.loads((REPORT / 'h1-manifest.json').read_text())
    h3 = json.loads((REPORT.parent / 'attachment.json').read_text())
    generated = {item['module'] for item in h1['modules'] + h3['modules']}
    base = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    tree = subprocess.check_output(['git', 'ls-tree', '-r', base], cwd=ROOT, text=True)
    tracked = {}
    for line in tree.splitlines():
        metadata, name = line.split('\t', 1)
        tracked[name] = metadata.split()[2]
    patterns = [r'\bsorry\b', r'\badmit\b', r'\baxiom\b', r'\bnative_decide\b',
                r'\bimplemented_by\b', r'\bextern\b', r'\bunsafe\b', r'\bopaque\b',
                r'\bmacro_rules\b', r'debug\.skipKernelTC', r'#eval', r'\bIO\b',
                r'\brun_cmd\b', r'maxHeartbeats\s+0\b']
    visited, pending, missing, audited, on_main = set(), ['CertData.Close.All'], [], [], []
    edges = {}
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        if not module.startswith(('AKLT.', 'CertData.')):
            continue
        rel = Path(*module.split('.')).with_suffix('.lean')
        path = ROOT / rel
        if not path.exists():
            assert module in generated, f'Missing hand-written source: {module}'
            missing.append(module)
            continue
        raw = path.read_bytes()
        code = strip_comments(raw.decode())
        imports = []
        for match in re.finditer(r'^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)', code, re.M):
            imports.extend(match[1].split())
        edges[module] = imports
        pending.extend(imports)
        if module in generated:
            continue
        blob = hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest()
        sha = hashlib.sha256(raw).hexdigest()
        if tracked.get(str(rel)) == blob:
            on_main.append({'module': module, 'path': str(rel), 'sha256': sha})
        else:
            hits = [pattern for pattern in patterns if re.search(pattern, code)]
            assert not hits, (module, hits)
            audited.append({'module': module, 'path': str(rel), 'sha256': sha,
                            'forbidden_hits': hits, 'lines': len(raw.splitlines())})
    expected = {'CertData.Close.All', 'CertData.H1.Close.Main',
                'CertData.H3.Close.Main', 'CertData.H3.Close.Leaves'}
    assert {item['module'] for item in audited} == expected
    # The copied H1 audit is outside All's import closure; scan it too.
    extra = ROOT / 'CertData/H1/Close/Audit.lean'
    extra_hits = [pattern for pattern in patterns if re.search(pattern, strip_comments(extra.read_text()))]
    assert not extra_hits
    result = {
        'base': base, 'root': 'CertData.Close.All', 'success': True,
        'visited_modules_including_external_roots': len(visited),
        'project_source_modules': len(edges), 'handwritten_on_main_count': len(on_main),
        'new_or_changed_handwritten_count': len(audited), 'new_or_changed_handwritten': audited,
        'unchanged_handwritten_on_main': sorted(on_main, key=lambda row: row['module']),
        'generated_modules_in_closure': len(generated & visited),
        'generated_h1_modules_in_closure': sum(item['module'] in visited for item in h1['modules']),
        'generated_h3_modules_in_closure': sum(item['module'] in visited for item in h3['modules']),
        'compacted_generated_sources': sorted(missing),
        'external_modules': sorted(m for m in visited if not m.startswith(('AKLT.', 'CertData.'))),
        'extra_handwritten_scan': {'path': str(extra.relative_to(ROOT)), 'forbidden_hits': extra_hits},
        'patterns': patterns,
    }
    (REPORT / 'source-closure-audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k.endswith('count') or k in
                     ['success', 'project_source_modules', 'generated_modules_in_closure',
                      'generated_h1_modules_in_closure', 'generated_h3_modules_in_closure']}))


if __name__ == '__main__':
    main()
