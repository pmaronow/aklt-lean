#!/usr/bin/env python3
"""Refresh the live report without touching accepted certificates or receipts."""
import argparse, collections, datetime, json, re, time
from pathlib import Path
from production_build import REPORT


def update(directory):
    path = directory / 'events.jsonl'
    latest = {}
    if path.exists():
        for line in path.read_text().splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            if row.get('exit') == 0:
                latest[row['module']] = row
    targets = json.loads((directory / 'pilot-targets.json').read_text())
    matches = []
    for target in targets:
        row = latest.get(target['module'])
        if row:
            matches.append(dict(target, cpu_seconds=row['user_seconds'] + row['system_seconds'],
                                wall_seconds=row['wall_seconds'], max_rss_kib=row['max_rss_kib'],
                                theorem_count=row['theorem_count']))
    accepted_logs = {row['log'] for row in latest.values()}
    running_logs = [path for path in (directory / 'logs').glob('*.stdout') if str(path) not in accepted_logs]
    running_audits = sum(len(re.findall(r'depends on axioms:|does not depend on any axioms', path.read_text())) for path in running_logs)
    (directory / 'pilot-results.json').write_text(json.dumps(matches, indent=2) + '\n')
    lines = [f"Updated UTC: {datetime.datetime.now(datetime.timezone.utc).isoformat()}", '',
             f"Accepted fresh owners: **{len(latest):,} / 7,964**. Exported theorem audits: "
             f"**{sum(r['theorem_count'] for r in latest.values()):,}**. "
             f"Accepted CPU time: **{sum(r['user_seconds'] + r['system_seconds'] for r in latest.values()) / 3600:.3f} hours**.", '',
             f"Another **{running_audits:,}** theorem audit prints are present in {len(running_logs)} unfinished module logs; these are not counted as accepted owners.", '',
             '| Kind | Accepted owners |', '|---|---:|']
    for kind, count in sorted(collections.Counter(r['kind'] for r in latest.values()).items()):
        lines.append(f'| `{kind}` | {count} |')
    lines += ['', 'Pilot comparisons (CPU seconds and peak GiB; fresh processes):', '',
              '| Kind / sample | Owner | Legacy CPU | New CPU | Legacy GiB | New GiB |',
              '|---|---|---:|---:|---:|---:|']
    for row in matches:
        lines.append(f"| {row['kind']} / {row['role']} | `{row['module'].split('.')[-1]}` | "
                     f"{row['legacy_cpu_seconds']:.2f} | {row['cpu_seconds']:.2f} | "
                     f"{row['legacy_max_rss_kib'] / 2**20:.3f} | {row['max_rss_kib'] / 2**20:.3f} |")
    lines += ['', 'The two final singleton assembly kinds require every prerequisite, so their',
              'fresh pilot measurements are recorded at the end of the same clean campaign.',
              'For every singleton kind the small and large samples are the same owner.',
              'All other paired pilot targets are selected by legacy CPU cost for checks or',
              'source bytes for data. Their shared prerequisite closure has 5,092 owners.', '']
    report = directory / 'report.md'
    content = report.read_text()
    start = '<!-- LIVE-PROGRESS -->'
    end = '<!-- /LIVE-PROGRESS -->'
    block = start + '\n' + '\n'.join(lines) + '\n' + end
    if start in content:
        content = content[:content.index(start)] + block + content[content.index(end) + len(end):]
    else:
        content = content.replace('## ORCH-SUMMARY', block + '\n\n## ORCH-SUMMARY')
    report.write_text(content)
    print(json.dumps(dict(accepted=len(latest), accepted_theorem_audits=sum(row['theorem_count'] for row in latest.values()),
                          running_audit_prints=running_audits, unfinished_logs=len(running_logs),
                          pilot_samples=len(matches), total_samples=len(targets))), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--report-dir', type=Path, default=REPORT)
    ap.add_argument('--watch', action='store_true')
    args = ap.parse_args()
    while True:
        update(args.report_dir)
        if not args.watch or (args.report_dir / 'report-finalized').exists():
            break
        time.sleep(30)


if __name__ == '__main__':
    main()
