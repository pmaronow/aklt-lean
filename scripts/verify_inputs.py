#!/usr/bin/env python3
"""Check both families' release numeric files against their pinned bytes."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir', type=Path, default=ROOT / 'data')
parser.add_argument('--report', type=Path, required=True)
args = parser.parse_args()
rows = []
for family, manifest in [('H1', ROOT / 'verification/inputs/H1.json'),
                         ('H3', ROOT / 'AKLT/Cert/H3/inputs.json')]:
    for pin in json.loads(manifest.read_text()):
        path = args.input_dir.resolve() / family / pin['name']
        if path.stat().st_size != pin['bytes']:
            raise SystemExit('Input size mismatch: ' + str(path))
        with path.open('rb') as stream:
            digest = hashlib.file_digest(stream, 'sha256').hexdigest()
        if digest != pin['sha256']:
            raise SystemExit('Input hash mismatch: ' + str(path))
        rows.append(dict(family=family, path=str(path), **pin))
args.report.parent.mkdir(parents=True, exist_ok=True)
args.report.write_text(json.dumps(rows, indent=2) + '\n')
print(f'PASS: {len(rows)} pinned numeric inputs')
