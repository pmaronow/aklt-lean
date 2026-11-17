#!/usr/bin/env python3
"""Create a deterministic, inventory-only H1 module source archive."""
import argparse, gzip, hashlib, io, json, tarfile
from pathlib import Path
from production_build import ROOT, REPORT, sha, source_bytes


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--report-dir', type=Path, default=REPORT)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    output = args.output or args.report_dir / 'H1-module-sources.tar.gz'
    inventory = sorted(json.loads((ROOT / 'verification/generated-modules.json').read_text())['H1'])
    records = []
    with output.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, compresslevel=9, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.PAX_FORMAT) as archive:
                for module in inventory:
                    rel = module.replace('.', '/') + '.lean'
                    payload = source_bytes(ROOT / rel)
                    if not payload.startswith(b'module\n') or len(payload.splitlines()) > 10000:
                        raise RuntimeError('invalid generated source: ' + rel)
                    info = tarfile.TarInfo(rel)
                    info.size = len(payload)
                    info.mode = 0o644
                    info.mtime = 0
                    info.uid = info.gid = 0
                    archive.addfile(info, io.BytesIO(payload))
                    records.append(dict(path=rel, sha256=hashlib.sha256(payload).hexdigest()))
    result = dict(archive=str(output), sha256=sha(output), bytes=output.stat().st_size,
                  source_files=len(records), files=records, compiled_artifacts_included=False)
    (args.report_dir / 'source-archive.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'files'}))


if __name__ == '__main__':
    main()
