#!/usr/bin/env python3
"""Transform retained H1 sources without opening or copying any legacy object.

The complete data-only regeneration commands are documented in REGEN-H1.md.
This faster route uses the same reversible envelope and frozen owner map.
"""
import argparse, collections, gzip, hashlib, json, time
from pathlib import Path
from module_source import module_source, rename_legacy
from production_build import ROOT, REPORT, guard


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--legacy-root', type=Path, required=True)
    ap.add_argument('--legacy-manifest', type=Path, required=True)
    ap.add_argument('--legacy-receipt', type=Path, required=True)
    ap.add_argument('--report-dir', type=Path, default=REPORT)
    args = ap.parse_args()
    args.report_dir.mkdir(parents=True, exist_ok=True)
    legacy = json.loads(args.legacy_manifest.read_text())
    inventory = set(json.loads((ROOT / 'verification/generated-modules.json').read_text())['H1'])
    jobs = legacy['jobs']
    assert {j['module'] for j in jobs} == inventory
    receipts = {r['module']: r for r in json.loads(args.legacy_receipt.read_text())['records']}
    records = []
    begin = time.monotonic()
    bykind = collections.defaultdict(list)
    for i, job in enumerate(jobs):
        if i % 100 == 0:
            guard()
        rel = job['module'].replace('.', '/') + '.lean'
        source = args.legacy_root / rel
        payload = source.read_bytes() if source.exists() else gzip.decompress(Path(str(source) + '.gz').read_bytes())
        old_hash = hashlib.sha256(payload).hexdigest()
        assert old_hash == receipts[job['module']]['source_sha256'], rel
        text = module_source(rename_legacy(payload.decode()))
        target = ROOT / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_text() != text:
            raise RuntimeError('refusing to overwrite different generated source: ' + rel)
        target.write_text(text)
        record = dict(module=job['module'], kind=job['kind'], source=rel,
                      source_sha256=hashlib.sha256(text.encode()).hexdigest(),
                      legacy_source_sha256=old_hash, bytes=len(text.encode()),
                      physical_lines=len(text.splitlines()),
                      legacy_cpu_seconds=receipts[job['module']]['user_seconds'] + receipts[job['module']]['system_seconds'],
                      legacy_max_rss_kib=receipts[job['module']]['max_rss_kib'])
        records.append(record)
        bykind[job['kind']].append(record)
    plan = {k: v for k, v in legacy.items() if k not in ['unbundled_jobs', 'resource_policy']}
    plan['data_root'] = str(ROOT / 'CertData/H1/Generated')
    plan['visibility'] = 'module; public imports; exposed public section; backward.proofsInPublic'
    plan['resource_policy'] = dict(max_processes=36, max_memory_bytes=270_000_000_000)
    (args.report_dir / 'production.json').write_text(json.dumps(plan, separators=(',', ':')) + '\n')
    (args.report_dir / 'source-manifest.json').write_text(json.dumps(records, indent=2) + '\n')
    (args.report_dir / 'SOURCES.sha256').write_text(''.join(r['source_sha256'] + '  ' + r['source'] + '\n' for r in sorted(records, key=lambda r: r['source'])))
    # Global witness/target singleton pilots necessarily need the entire DAG;
    # they are measured when their prerequisites have been freshly rebuilt.
    terminal = {'all_witness_assembly', 'target_assembly'}
    targets = []
    for kind, group in sorted(bykind.items()):
        metric = 'legacy_cpu_seconds' if any('theorem ' in (ROOT / r['source']).read_text() for r in group[:1]) else 'bytes'
        ordered = sorted(group, key=lambda r: (r[metric], r['module']))
        for role, row in [('small', ordered[0]), ('large', ordered[-1])]:
            targets.append(dict(row, role=role, selection_metric=metric, terminal=kind in terminal))
    (args.report_dir / 'pilot-targets.json').write_text(json.dumps(targets, indent=2) + '\n')
    bymodule = {j['module']: j for j in jobs}
    wanted = set()
    def add(module):
        if module in wanted:
            return
        wanted.add(module)
        for dep in bymodule[module]['deps']:
            add(dep)
    for target in targets:
        if not target['terminal']:
            add(target['module'])
    pilot = dict(plan, jobs=[j for j in jobs if j['module'] in wanted], pilot_targets=[t for t in targets if not t['terminal']])
    (args.report_dir / 'pilot.json').write_text(json.dumps(pilot, separators=(',', ':')) + '\n')
    summary = dict(modules=len(jobs), pilot_modules=len(wanted), kinds=len(bykind),
                   source_bytes=sum(r['bytes'] for r in records),
                   maximum_lines=max(r['physical_lines'] for r in records),
                   wall_seconds=time.monotonic()-begin,
                   legacy_manifest_sha256=hashlib.sha256(args.legacy_manifest.read_bytes()).hexdigest())
    (args.report_dir / 'regeneration.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
