#!/usr/bin/env python3
"""Attach only the accepted phase-3 generated modules; never run production."""
import hashlib
import errno
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path('/home/ubuntu/aklt/wt/CLOSE_H3')
LANE = Path('/home/ubuntu/aklt/wt/CERT_H3')
HANDOFF = Path('/home/ubuntu/aklt/reports/CERT_H3')
REPORT = Path('/home/ubuntu/aklt/reports/CLOSE_H3')


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    started = time.monotonic()
    audit = {'head': subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()}
    handwritten = []
    for item in json.loads((HANDOFF / 'phase3/merge-set-hashes.json').read_text()):
        rel = Path(item['path'])
        if rel.suffix != '.lean' or not str(rel).startswith('CertData/H3/'):
            continue
        current, lane = digest(ROOT / rel), digest(LANE / rel)
        assert current == lane == item['sha256'], f'Hand-written drift: {rel}'
        handwritten.append({'path': str(rel), 'sha256': current})
    audit['handwritten_sources_identical'] = handwritten
    handwritten_paths = {item['path'] for item in handwritten}

    closure = []
    clean = json.loads((HANDOFF / 'phase3/clean-merge-receipt.json').read_text())
    for item in clean['modules']:
        if item['module'] == 'CertData.H3.MergeAudit':
            continue  # The temporary audit was never an imported dependency.
        rel = Path(*item['module'].split('.')).with_suffix('.lean')
        current = digest(ROOT / rel)
        assert current == item['source_sha256'], f'Dependency drift: {rel}'
        closure.append({'path': str(rel), 'sha256': current})
    audit['phase3_dependency_sources_identical'] = closure
    REPORT.mkdir(parents=True, exist_ok=True)
    (REPORT / 'compatibility.json').write_text(json.dumps(audit, indent=2) + '\n')

    supplemental = []
    for name in ['CertData/H3/Kernel/Literal', 'CertData/H3/Bridge/FamilyAssembly']:
        rel = Path(name).with_suffix('.olean')
        src, dst = LANE / rel, ROOT / '.lake/build/lib/lean' / rel
        expected = digest(src)
        if not dst.exists():
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dst)
            assert digest(dst) == expected, str(dst)
        supplemental.append({'module': name.replace('/', '.'),
                             'lane_olean_sha256': expected, 'local_olean_sha256': digest(dst)})
    (REPORT / 'supplemental-handwritten.json').write_text(json.dumps(supplemental, indent=2) + '\n')

    manifest = json.loads((HANDOFF / 'phase3/production-modules.json').read_text())
    attached, source_bytes, olean_bytes, compacted = [], 0, 0, 0
    copied_olean_bytes, linked_modules, preserved_handwritten = 0, 0, []
    for item in manifest:
        rel = Path(*item['module'].split('.'))
        src_o = (LANE / rel).with_suffix('.olean')
        dst_o = (ROOT / '.lake/build/lib/lean' / rel).with_suffix('.olean')
        if str(rel.with_suffix('.lean')) in handwritten_paths:
            assert digest(ROOT / rel.with_suffix('.lean')) == item['source_sha256']
            preserved_handwritten.append({
                'module': item['module'], 'source_sha256': item['source_sha256'],
                'local_olean_sha256': digest(dst_o),
                'lane_olean_sha256': item['olean_sha256'],
            })
            continue
        assert src_o.stat().st_size == item['olean_bytes'], str(src_o)
        dst_o.parent.mkdir(parents=True, exist_ok=True)
        if dst_o.exists():
            assert digest(dst_o) == item['olean_sha256'], f'Existing foreign artifact: {dst_o}'
        else:
            assert digest(src_o) == item['olean_sha256'], f'Olean hash: {src_o}'
            try:
                os.link(src_o, dst_o)
            except OSError as error:
                if error.errno != errno.EXDEV:
                    raise
                shutil.copyfile(src_o, dst_o)
                assert digest(dst_o) == item['olean_sha256'], f'Copied artifact: {dst_o}'
        linked = os.path.samefile(src_o, dst_o)
        if linked:
            linked_modules += 1
        else:
            copied_olean_bytes += item['olean_bytes']
        olean_bytes += item['olean_bytes']

        src_s = (LANE / rel).with_suffix('.lean')
        dst_s = (ROOT / rel).with_suffix('.lean')
        if src_s.exists():
            assert digest(src_s) == item['source_sha256'], f'Source hash: {src_s}'
            dst_s.parent.mkdir(parents=True, exist_ok=True)
            if dst_s.exists():
                assert digest(dst_s) == item['source_sha256'], f'Existing foreign source: {dst_s}'
            else:
                shutil.copyfile(src_s, dst_s)
            source_bytes += dst_s.stat().st_size
        else:
            assert item['source_compacted'], f'Unexpected missing source: {src_s}'
            compacted += 1
        attached.append({
            'module': item['module'], 'source_compacted': item['source_compacted'],
            'source_sha256': item['source_sha256'], 'olean_sha256': item['olean_sha256'],
            'olean_bytes': item['olean_bytes'], 'artifact': str(dst_o.relative_to(ROOT)),
            'method': 'hard-link' if linked else 'copy',
            'device': dst_o.stat().st_dev, 'inode': dst_o.stat().st_ino,
        })
        if len(attached) % 500 == 0:
            print(f'Verified {len(attached)} generated modules', flush=True)
    summary = {
        'manifest_modules': len(manifest), 'generated_modules': len(attached),
        'preserved_handwritten_modules': len(preserved_handwritten),
        'source_files': len(attached) - compacted,
        'compacted_sources_not_regenerated': compacted,
        'olean_logical_bytes': olean_bytes, 'copied_source_bytes': source_bytes,
        'new_olean_payload_bytes': copied_olean_bytes, 'hardlinked_modules': linked_modules,
        'wall_seconds': time.monotonic() - started,
        'method': 'copy sources; hard-link oleans when possible, copy across mounts',
        'production_commands_run': [],
    }
    (REPORT / 'attachment.json').write_text(json.dumps(
        {'summary': summary, 'preserved_handwritten': preserved_handwritten,
         'modules': attached}, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
