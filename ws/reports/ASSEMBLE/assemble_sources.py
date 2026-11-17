#!/usr/bin/env python3
"""Copy the twelve sources and remove TeX comments, preserving source lines."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/ubuntu/aklt')
DEST = ROOT / 'manuscript-v2'
REPORT = ROOT / 'reports/ASSEMBLE'
SOURCES = {
    'sec1-result.tex': 'REV_A1',
    'sec2-moments.tex': 'REV_C1a',
    'sec3-quantum-frames.tex': 'REV_A1',
    'sec4-periodic-gap.tex': 'REV_A2',
    'sec5-window.tex': 'REV_B',
    'sec6-walks.tex': 'REV_C1a',
    'sec7-recursion.tex': 'REV_C1b',
    'sec8-inputs.tex': 'REV_C2',
    'app-finite.tex': 'REV_A2',
    'app-topology.tex': 'REV_B',
    'app-input-contracts.tex': 'REV_C2',
    'app-local-operator.tex': 'REV_C3',
}


def strip_comments(s):
    out = []
    for line in s.splitlines(keepends=True):
        for i, ch in enumerate(line):
            if ch != '%':
                continue
            n = 0
            j = i - 1
            while j >= 0 and line[j] == '\\':
                n += 1
                j -= 1
            if n % 2 == 0:
                # Preserve TeX's end-of-line suppression for inline comments.
                # Source comment-only lines become empty lines.
                prefix = line[:i]
                if prefix.strip():
                    if line.endswith('\n'):
                        raise ValueError('Inline comment needs explicit review: ' + line)
                    line = prefix
                else:
                    line = '\n' if line.endswith('\n') else ''
                break
        out.append(line)
    return ''.join(out)


if __name__ == '__main__':
    records = []
    for filename, lane in SOURCES.items():
        source = ROOT / 'reports' / lane / filename
        original = source.read_text()
        target = DEST / filename
        if target.exists():
            raise SystemExit(f'Refusing to overwrite assembled file: {target}')
        target.write_text(strip_comments(original))
        records.append({'file': filename, 'source': str(source),
                        'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
    (REPORT / 'sources.json').write_text(json.dumps(records, indent=2) + '\n')
    print(f'Copied {len(records)} section files; source hashes recorded.')
