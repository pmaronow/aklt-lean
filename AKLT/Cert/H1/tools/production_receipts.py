#!/usr/bin/env python3
"""Independently verify the module-system H1 receipt DAG and source inventory."""
from __future__ import annotations
import argparse, collections, gzip, hashlib, json, re, time
from pathlib import Path
from production_build import (ROOT, REPORT, ALLOWED, artifact_hashes, artifact_path,
                              axiom_audit, build_key, compact_source, guard,
                              imports, sha, source_bytes)


def verify(args):
    begin = time.monotonic()
    plan = json.loads(args.manifest.read_text())
    jobs = {j['module']: j for j in plan['jobs']}
    inventory = set(json.loads((ROOT / 'verification/generated-modules.json').read_text())['H1'])
    if not args.partial and set(jobs) != inventory:
        raise RuntimeError('production plan differs from the release inventory')
    latest = {}
    for line in (args.report_dir / 'events.jsonl').read_text().splitlines():
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue  # A concurrent frontier may be appending its final line.
        if record.get('exit') == 0:
            latest[record['module']] = record
    source_manifest = {r['module']: r for r in json.loads((args.report_dir / 'source-manifest.json').read_text())} if (args.report_dir / 'source-manifest.json').exists() else None
    pending = set(jobs)
    verified = {}
    records = []
    stages = collections.defaultdict(lambda: dict(modules=0, user_seconds=0., system_seconds=0., max_rss_kib=0., artifact_bytes=0, theorems=0))
    source_hashes = {}
    object_hashes = {}
    theorem_count = 0
    source_total = 0
    while pending:
        ready = sorted(m for m in pending if all(d in verified for d in jobs[m]['deps']))
        if not ready:
            raise RuntimeError('cycle or missing dependency')
        for module in ready:
            if len(verified) % 100 == 0:
                guard()
            job = jobs[module]
            record = latest.get(module)
            if not record:
                raise RuntimeError('missing successful receipt: ' + module)
            source = ROOT / (module.replace('.', '/') + '.lean')
            payload = source_bytes(source)
            text = payload.decode()
            digest = hashlib.sha256(payload).hexdigest()
            if digest != record['source_sha256'] or source_manifest and digest != source_manifest[module]['source_sha256']:
                raise RuntimeError('source mismatch: ' + module)
            if not text.startswith('module\n') or len(text.splitlines()) > 10000:
                raise RuntimeError('invalid header or line cap: ' + module)
            code = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
            forbidden = re.findall(r'(?<![\w.])(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)(?![\w\'])', code)
            if forbidden or 'debug.skipKernelTC' in code:
                raise RuntimeError('forbidden source construct: ' + module + ': ' + repr(forbidden))
            actual = {m for m in imports(text) if m.startswith('CertData.H1.Generated.')}
            if not actual <= set(job['deps']):
                raise RuntimeError('untracked generated imports: ' + module)
            objects = artifact_hashes(module)
            if objects != record['artifact_hashes']:
                raise RuntimeError('compiled module mismatch: ' + module)
            key, closure = build_key(source, [verified[d] for d in job['deps']])
            if key != record['key'] or closure != record['library_closure']:
                raise RuntimeError('dependency closure mismatch: ' + module)
            timing = Path(record['timing']).read_text()
            if not re.search(r'^\s*Exit status: 0\s*$', timing, re.M):
                raise RuntimeError('missing GNU-time exit zero: ' + module)
            audits = axiom_audit(Path(record['log']).read_text(), text)
            auditpath = Path(record['axiom_audit'])
            if sha(auditpath) != record['axiom_audit_sha256'] or json.loads(auditpath.read_text()) != audits:
                raise RuntimeError('axiom receipt mismatch: ' + module)
            if len(audits) != record['theorem_count']:
                raise RuntimeError('theorem count mismatch: ' + module)
            theorem_count += len(audits)
            source_total += len(payload)
            stage = stages[job['kind']]
            stage['modules'] += 1
            stage['user_seconds'] += record['user_seconds']
            stage['system_seconds'] += record['system_seconds']
            stage['max_rss_kib'] = max(stage['max_rss_kib'], record['max_rss_kib'])
            stage['artifact_bytes'] += sum((ROOT / p).stat().st_size for p in objects)
            stage['theorems'] += len(audits)
            source_hashes[str(source.relative_to(ROOT))] = digest
            object_hashes.update(objects)
            records.append(record)
            verified[module] = record
            pending.remove(module)
    inputs = json.loads((args.report_dir / 'data-input-receipt.json').read_text())
    for row in inputs:
        path = Path(row['path'])
        if path.stat().st_size != row['bytes'] or sha(path) != row['sha256']:
            raise RuntimeError('numeric input changed: ' + str(path))
    result = dict(format='h1-module-production-verified-v3', success=True,
                  scope='selected pilot owner DAG' if args.partial else 'complete H1 owner DAG',
                  manifest=str(args.manifest), manifest_sha256=sha(args.manifest),
                  modules=len(verified), patterns=len(plan['patterns']),
                  blocks=sum(len(p['blocks']) for p in plan['patterns']),
                  logical_components=sum(len(j.get('components', [j['module']])) for j in jobs.values()),
                  generated_theorems=theorem_count, axiom_audits=theorem_count,
                  cpu_hours=sum(s['user_seconds'] + s['system_seconds'] for s in stages.values()) / 3600,
                  source_bytes=source_total, compiled_files=len(object_hashes),
                  stages=dict(stages), records=records, input_receipts=inputs,
                  verification_wall_seconds=time.monotonic() - begin)
    name = 'verified-pilot.json' if args.partial else 'verified-production.json'
    (args.report_dir / name).write_text(json.dumps(result, indent=2) + '\n')
    for name, data in [('SOURCES.sha256', source_hashes), ('COMPILED.sha256', object_hashes)]:
        if args.partial:
            name = 'PILOT-' + name
        (args.report_dir / name).write_text(''.join(data[path] + '  ' + path + '\n' for path in sorted(data)))
    print(json.dumps({k: v for k, v in result.items() if k not in ['stages', 'records', 'input_receipts']}))


def inputs(args):
    base = Path('/home/ubuntu/aklt/data/h1')
    index = json.loads((base / 'index.json').read_text())
    files = [base / 'index.json'] + [base / chunk['file'] for chunk in index['chunks']]
    records = [dict(path=str(p), bytes=p.stat().st_size, sha256=sha(p)) for p in files]
    if args.output.exists() and json.loads(args.output.read_text()) != records:
        raise RuntimeError('numeric input receipt changed')
    args.output.write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps(dict(input_files=len(records), bytes=sum(r['bytes'] for r in records))))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='command', required=True)
    parser = sub.add_parser('verify')
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--report-dir', type=Path, default=REPORT)
    parser.add_argument('--partial', action='store_true')
    parser = sub.add_parser('inputs')
    parser.add_argument('--output', type=Path, required=True)
    sub.add_parser('restore-sources')
    parser = sub.add_parser('compact-templates')
    parser.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.command == 'verify':
        verify(args)
    elif args.command == 'inputs':
        inputs(args)
    elif args.command == 'restore-sources':
        count = 0
        for archive in (ROOT / 'CertData/H1/Generated').rglob('*.lean.gz'):
            source = Path(str(archive)[:-3])
            payload = gzip.decompress(archive.read_bytes())
            if source.exists() and source.read_bytes() != payload:
                raise RuntimeError('source differs from archive: ' + str(source))
            if not source.exists():
                source.write_bytes(payload)
                count += 1
        print(json.dumps(dict(restored_sources=count)))
    else:
        # This command only compacts disposable unbundled generator templates.
        records = []
        for directory in ['Data', 'Check']:
            for source in (ROOT / 'CertData/H1/Generated' / directory).rglob('*.lean'):
                digest = sha(source)
                compact_source(source)
                records.append(dict(source=str(source.relative_to(ROOT)), sha256=digest))
        args.output.write_text(json.dumps(records, indent=2) + '\n')
        print(json.dumps(dict(compacted_templates=len(records))))


if __name__ == '__main__':
    main()
