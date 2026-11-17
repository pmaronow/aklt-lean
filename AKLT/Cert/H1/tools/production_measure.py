#!/usr/bin/env python3
"""Summarize accepted module-system runs without relying on legacy pilot files."""
import argparse, collections, json
from pathlib import Path
from production_build import ROOT, REPORT, artifact_hashes


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--verified-production', type=Path)
    ap.add_argument('--report-dir', type=Path, default=REPORT)
    args = ap.parse_args()
    verified = args.verified_production or args.report_dir / 'verified-production.json'
    if verified.exists():
        receipt = json.loads(verified.read_text())
        rows = receipt['records']
    else:
        latest = {}
        for line in (args.report_dir / 'events.jsonl').read_text().splitlines():
            row = json.loads(line)
            if row.get('exit') == 0:
                latest[row['module']] = row
        rows = list(latest.values())
    stages = collections.defaultdict(lambda: dict(modules=0, cpu_seconds=0., max_rss_gib=0., compiled_bytes=0))
    for row in rows:
        stage = stages[row['kind']]
        stage['modules'] += 1
        stage['cpu_seconds'] += row['user_seconds'] + row['system_seconds']
        stage['max_rss_gib'] = max(stage['max_rss_gib'], row['max_rss_kib'] / 2**20)
        stage['compiled_bytes'] += sum((ROOT / path).stat().st_size for path in row['artifact_hashes'])
    result = dict(modules=len(rows), generated_theorems=sum(row['theorem_count'] for row in rows),
                  cpu_hours=sum(s['cpu_seconds'] for s in stages.values()) / 3600,
                  peak_module_rss_gib=max(s['max_rss_gib'] for s in stages.values()),
                  compiled_bytes=sum(s['compiled_bytes'] for s in stages.values()),
                  stages=dict(stages))
    (args.report_dir / 'measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'stages'}))


if __name__ == '__main__':
    main()
