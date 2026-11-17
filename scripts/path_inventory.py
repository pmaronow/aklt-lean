#!/usr/bin/env python3
"""List retained absolute path literals without rewriting historical evidence."""
import argparse
import csv
import gzip
import io
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PREFIXES = {'bin', 'dev', 'etc', 'home', 'lib', 'lib64', 'nonexistent', 'path',
            'proc', 'root', 'run', 'sys', 'tmp', 'usr', 'var'}
TOKEN = re.compile(r'''(?<![\w.:/])(/[A-Za-z_][^\s\x00"'`<>|,;\)\]]*)''')


def reason(name, value):
    if value.startswith('/home/'):
        if name.startswith(('AKLT/Cert/H1/tools/', 'AKLT/Cert/H3/')):
            return 'Unexpected user-specific tool path; replace it with a repository-relative default or an explicit input.'
        if name.endswith('.lean'):
            return 'Unchanged Lean comment containing a historical diagnostic reference; no import or runtime requirement.'
        return 'Verbatim historical receipt, review, or feasibility report; identifies measured environment and is not a required release path.'
    return 'Standard Linux/tool/sandbox path, user-selected example, scanner pattern, or historical diagnostic; not a fixed user checkout requirement.'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path, default=ROOT / 'verification/layout')
    args = parser.parse_args()
    root = args.project.resolve()
    tracked = subprocess.check_output(['git', '-C', str(root), 'ls-files', '-z']).decode().split('\0')
    rows = []
    for name in tracked:
        if not name or name.startswith('verification/layout/') or name.endswith('.pdf') or name == 'scripts/path_inventory.py':
            continue
        path = root / name
        try:
            text = gzip.decompress(path.read_bytes()).decode() if name.endswith('.gz') else path.read_text()
        except (UnicodeError, OSError):
            continue
        for line_number, line in enumerate(text.splitlines(), 1):
            values = set(TOKEN.findall(line))
            if re.search(r'''['"]/['"]''', line):
                values.add('/')
            for value in sorted(values):
                # An anchored .gitignore pattern is relative to the repository,
                # and a slash in a mathematical expression is not a path.
                if name == '.gitignore' or (value != '/' and value.split('/')[1] not in PREFIXES):
                    continue
                rows.append({'file': name, 'line': line_number, 'path': value,
                             'reason': reason(name, value)})
    data = io.StringIO()
    table = csv.DictWriter(data, fieldnames=['file', 'line', 'path', 'reason'],
                            delimiter='\t', lineterminator='\n')
    table.writeheader()
    table.writerows(rows)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'absolute-paths.tsv.gz').write_bytes(gzip.compress(data.getvalue().encode(), mtime=0))
    home = [r for r in rows if r['path'].startswith('/home/')]
    summary = {'inventory': 'absolute-paths.tsv.gz',
        'scope': 'Tracked text and decompressed historical reports; one distinct literal per file/line. Excludes this inventory, its producer, binary paper PDF, Git ignore anchors, and mathematical division.',
        'rows': len(rows), 'home_path_rows': len(home), 'files': len({r['file'] for r in rows}),
        'home_path_files': sorted({r['file'] for r in home})}
    (args.output / 'absolute-paths.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
