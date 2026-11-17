#!/usr/bin/env python3
"""Attach accepted H1 artifacts and materialize their archived source text."""
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path('/home/ubuntu/aklt/wt/CLOSE_H3')
PRODUCER = Path('/home/ubuntu/aklt/wt/CERT_H1')
CLOSER = PRODUCER / '_close_main'
HANDOFF = Path('/home/ubuntu/aklt/reports/CERT_H1')
REPORT = Path('/home/ubuntu/aklt/reports/CLOSE_H3/final')


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def copy_checked(src, dst, expected):
    dst.parent.mkdir(parents=True, exist_ok=True)
    if not dst.exists():
        shutil.copyfile(src, dst)
    assert digest(dst) == expected, f'Artifact mismatch: {dst}'


def main():
    start = time.monotonic()
    REPORT.mkdir(parents=True, exist_ok=True)
    base = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    closing = json.loads((HANDOFF / 'closing/receipt.json').read_text())
    assert base == closing['main']
    compatibility = json.loads((HANDOFF / 'closing/compatibility.json').read_text())
    merge = json.loads((HANDOFF / 'phase3/merge-verification.json').read_text())
    source_pins = merge['merge_files'] | merge['dependency_sources']
    rows = []
    for item in compatibility['rows']:
        rel = item['source']
        assert item['source_matches_production']
        assert (ROOT / rel).read_bytes() == (CLOSER / rel).read_bytes(), rel
        assert digest(ROOT / rel) == source_pins[rel], rel
        if rel.startswith('AKLT/Cert/H1/'):
            assert digest(PRODUCER / rel) == source_pins[rel], rel
        rows.append({'source': rel, 'sha256': digest(ROOT / rel)})
    assert (ROOT / 'lakefile.toml').read_bytes() == (CLOSER / 'lakefile.toml').read_bytes()
    (REPORT / 'h1-compatibility.json').write_text(json.dumps(
        {'base': base, 'source_rows': rows, 'mismatches': []}, indent=2) + '\n')

    verified_path = HANDOFF / 'phase3/verified-production.json'
    verified = json.loads(verified_path.read_text())
    assert verified['success'] and verified['modules'] == 7964
    assert digest(Path(verified['manifest'])) == verified['manifest_sha256']
    modules = []
    for item in verified['records']:
        assert item['exit'] == 0
        rel = Path(*item['module'].split('.'))
        source = rel.with_suffix('.lean')
        archive = PRODUCER / item['source_archive']
        raw = gzip.decompress(archive.read_bytes())
        assert hashlib.sha256(raw).hexdigest() == item['source_sha256'], str(archive)
        dst_s = ROOT / source
        dst_s.parent.mkdir(parents=True, exist_ok=True)
        if dst_s.exists():
            assert dst_s.read_bytes() == raw, str(dst_s)
        else:
            dst_s.write_bytes(raw)
        olean = rel.with_suffix('.olean')
        dst_o = ROOT / '.lake/build/lib/lean' / olean
        copy_checked(PRODUCER / olean, dst_o, item['artifact_sha256'])
        modules.append({
            'module': item['module'], 'source': str(source),
            'source_sha256': item['source_sha256'], 'source_bytes': len(raw),
            'olean': str(dst_o.relative_to(ROOT)), 'olean_sha256': item['artifact_sha256'],
            'olean_bytes': dst_o.stat().st_size,
        })
        if len(modules) % 500 == 0:
            print(f'Attached and verified {len(modules)} H1 owner modules', flush=True)

    hand_written = []
    for item in closing['files']:
        rel = Path(item['path'])
        if rel.suffix == '.lean':
            copy_checked(CLOSER / rel, ROOT / rel, item['sha256'])
            hand_written.append(item)
    for item in closing['oleans']:
        src = Path(item['path'])
        rel = Path(*item['module'].split('.')).with_suffix('.olean')
        copy_checked(src, ROOT / '.lake/build/lib/lean' / rel, item['sha256'])
    summary = {
        'base': base, 'generated_module_count': len(modules),
        'source_bytes': sum(item['source_bytes'] for item in modules),
        'olean_bytes': sum(item['olean_bytes'] for item in modules),
        'source_method': 'read and decompress verified producer archives into own worktree',
        'artifact_method': 'copy retained oleans and verify destination SHA-256',
        'wall_seconds': time.monotonic() - start, 'numerical_production_rerun': False,
        'production_manifest_sha256': verified['manifest_sha256'],
        'verified_receipt_sha256': digest(verified_path),
        'closing_receipt_sha256': digest(HANDOFF / 'closing/receipt.json'),
    }
    (REPORT / 'h1-manifest.json').write_text(json.dumps(
        {'summary': summary, 'hand_written_sources': hand_written, 'modules': modules}, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
