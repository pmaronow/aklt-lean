#!/usr/bin/env python3
"""Check both families' release numeric files against their pinned bytes."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def family_input_dir(parent, family):
    """Use lowercase family directories; accept existing uppercase layouts."""
    parent = Path(parent).resolve()
    current = parent / family.lower()
    previous = parent / family.upper()
    if current.is_dir() and previous.is_dir():
        raise ValueError('Ambiguous input directories: ' + str(current) + ' and ' + str(previous))
    return previous if previous.is_dir() else current


def verify(input_dir, manifests):
    rows = []
    for family, manifest in manifests:
        directory = family_input_dir(input_dir, family)
        for pin in json.loads(Path(manifest).read_text()):
            path = directory / pin['name']
            if path.stat().st_size != pin['bytes']:
                raise ValueError('Input size mismatch: ' + str(path))
            with path.open('rb') as stream:
                digest = hashlib.file_digest(stream, 'sha256').hexdigest()
            if digest != pin['sha256']:
                raise ValueError('Input hash mismatch: ' + str(path))
            rows.append(dict(family=family, path=str(path), **pin))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT / 'data')
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    try:
        rows = verify(args.input_dir, [('H1', ROOT / 'verification/inputs/H1.json'),
                                      ('H3', ROOT / 'AKLT/Cert/H3/inputs.json')])
    except ValueError as error:
        raise SystemExit(str(error))
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(rows, indent=2) + '\n')
    print(f'PASS: {len(rows)} pinned numeric inputs')


if __name__ == '__main__':
    main()
