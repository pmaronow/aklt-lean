#!/usr/bin/env python3
"""Identify tracked Lean sources and build pins independently of documentation."""
import argparse
import hashlib
from pathlib import Path
import re
import subprocess


def source_digest(project):
    project = Path(project).resolve()
    tracked = subprocess.check_output(
        ['git', '-C', str(project), 'ls-files', '-z']).decode().split('\0')
    pins = {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}
    names = sorted({p for p in tracked if p and (p.endswith('.lean') or p in pins)})
    if not pins <= set(names):
        raise ValueError('The tracked build pins are incomplete')
    lines = []
    for name in names:
        if '\n' in name or '\r' in name:
            raise ValueError('Source paths must not contain line breaks')
        digest = hashlib.sha256((project / name).read_bytes()).hexdigest()
        lines.append(f'{name} {digest}\n')
    listing = ''.join(lines).encode('utf-8')
    return hashlib.sha256(listing).hexdigest(), listing


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--manifest', type=Path, help='Also write the exact hashed path/digest listing')
    parser.add_argument('--check', metavar='SHA256_OR_FILE',
                        help='Compare with a lowercase SHA-256 or a file containing that value')
    args = parser.parse_args()
    actual, listing = source_digest(args.project)
    if args.check:
        expected = args.check
        if not re.fullmatch(r'[0-9a-f]{64}', expected):
            expected = Path(expected).read_text().strip()
        if not re.fullmatch(r'[0-9a-f]{64}', expected):
            parser.error('--check needs a SHA-256 or a file containing only that value')
        if actual != expected:
            raise SystemExit(f'Source digest mismatch: expected {expected}, found {actual}')
    if args.manifest:
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_bytes(listing)
    print(actual)


if __name__ == '__main__':
    main()
