#!/usr/bin/env python3
"""Verify the current H3 attachment against its accepted production hashes."""
import hashlib
import json
from pathlib import Path
import time

ROOT = Path('/home/ubuntu/aklt/wt/CLOSE_H3')
REPORT = Path('/home/ubuntu/aklt/reports/CLOSE_H3')
PRODUCTION = Path('/home/ubuntu/aklt/reports/CERT_H3/phase3/production-modules.json')


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    start = time.monotonic()
    prior = json.loads((REPORT / 'attachment.json').read_text())
    production = json.loads(PRODUCTION.read_text())
    accepted = {item['module']: item for item in production}
    modules = []
    for item in prior['modules']:
        expected = accepted[item['module']]
        assert item['olean_sha256'] == expected['olean_sha256']
        assert item['source_sha256'] == expected['source_sha256']
        olean = ROOT / item['artifact']
        assert olean.stat().st_size == item['olean_bytes']
        assert digest(olean) == expected['olean_sha256'], str(olean)
        source = Path(*item['module'].split('.')).with_suffix('.lean')
        if (ROOT / source).exists():
            assert digest(ROOT / source) == expected['source_sha256'], str(source)
        else:
            assert item['source_compacted']
        modules.append({
            'module': item['module'], 'source': str(source),
            'source_sha256': expected['source_sha256'],
            'source_compacted': item['source_compacted'],
            'olean': item['artifact'], 'olean_sha256': expected['olean_sha256'],
            'olean_bytes': item['olean_bytes'],
        })
        if len(modules) % 500 == 0:
            print(f'Verified {len(modules)} current H3 artifacts', flush=True)
    for item in prior['preserved_handwritten']:
        olean = ROOT / '.lake/build/lib/lean' / Path(*item['module'].split('.')).with_suffix('.olean')
        assert digest(olean) == item['local_olean_sha256'], str(olean)
    summary = {
        'generated_module_count': len(modules), 'production_manifest_count': len(production),
        'preserved_handwritten_manifest_count': len(prior['preserved_handwritten']),
        'olean_bytes': sum(item['olean_bytes'] for item in modules),
        'production_manifest_sha256': digest(PRODUCTION),
        'wall_seconds': time.monotonic() - start, 'numerical_production_rerun': False,
    }
    (REPORT / 'final/h3-manifest.json').write_text(json.dumps(
        {'summary': summary, 'modules': modules,
         'preserved_handwritten': prior['preserved_handwritten']}, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
