#!/usr/bin/env python3
"""Write the final H1 report only after independent production and closing audits."""
import argparse, collections, datetime, json, re
from pathlib import Path
from production_build import ROOT, REPORT


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--report-dir', type=Path, default=REPORT)
    args = ap.parse_args()
    report = args.report_dir
    load = lambda name: json.loads((report / name).read_text())
    verified = load('verified-production.json')
    closing = load('closing/receipt.json')
    reexport = load('data-only-reexport.json')
    archive = load('source-archive.json')
    installer = load('archive-installer-test.json')
    pilots = load('pilot-results.json')
    assert verified['success'] and verified['modules'] == 7964 and verified['generated_theorems'] == 414638
    assert closing['success'] and closing['closed'] and reexport['success'] and installer['success']
    assert len(pilots) == 50, 'some paired pilot measurements are missing'
    archived = {r['path']: r['sha256'] for r in archive['files']}
    accepted = {r['module'].replace('.', '/') + '.lean': r['source_sha256'] for r in verified['records']}
    assert archived == accepted, 'source archive and checked sources differ'
    summaries = [load('run-' + name + '.json') for name in ['smoke', 'pilot', 'production']]
    coverage_summary = load('run-coverage-smoke.json') if (report / 'run-coverage-smoke.json').exists() else None
    numeric_rows = verified['records']
    close_rows = closing['records']
    compiler_events = [json.loads(line) for line in (report / 'events.jsonl').read_text().splitlines()]
    numeric_cpu = sum(r['user_seconds'] + r['system_seconds'] for r in compiler_events if r.get('exit') == 0)
    portfolio_cpu = sum(r['user_seconds'] + r['system_seconds'] for r in numeric_rows)
    close_cpu = sum(r['user_seconds'] + r['system_seconds'] for r in close_rows)
    diagnostic_cpu = 0.
    for directory in ['cache-validation', 'coverage-visibility-test', 'coverage-profile-test', 'coverage-private-proof-test']:
        for journal in ['events.jsonl', 'failures.jsonl']:
            path = report / directory / journal
            if path.exists():
                for line in path.read_text().splitlines():
                    row = json.loads(line)
                    if row['module'].startswith('CertData.H1.Validation.'):
                        diagnostic_cpu += (row.get('user_seconds') or 0) + (row.get('system_seconds') or 0)
    peak_module = max(r['max_rss_kib'] for r in numeric_rows + close_rows) / 2**20
    # The pilot and smoke overlap; production and closing run afterward.
    aggregate_bound = max(summaries[0]['peak_sampled_aggregate_rss_bytes'] + summaries[1]['peak_sampled_aggregate_rss_bytes'],
                          summaries[1]['peak_sampled_aggregate_rss_bytes'] + (coverage_summary['peak_sampled_aggregate_rss_bytes'] if coverage_summary else 0),
                          summaries[2]['peak_sampled_aggregate_rss_bytes'], max(r['max_rss_kib'] * 1024 for r in close_rows))
    all_summaries = summaries + ([coverage_summary] if coverage_summary else [])
    minimum_memory = min(s['minimum_available_bytes'] for s in all_summaries)
    minimum_disk = min(s['minimum_free_disk_bytes'] for s in all_summaries)
    first = min(int(re.search(r'-(\d+)\.stdout$', r['log'])[1]) / 1e9 for r in numeric_rows)
    last = max(r['finished_at'] for r in close_rows)
    totals = dict(modules=7964, theorems=414638, numeric_cpu_hours=numeric_cpu/3600,
                  portfolio_cpu_hours=portfolio_cpu/3600, successful_compiler_events=len(compiler_events),
                  closing_cpu_seconds=close_cpu, total_compiler_cpu_hours=(numeric_cpu+close_cpu)/3600,
                  diagnostic_compiler_cpu_seconds=diagnostic_cpu,
                  all_campaign_compiler_cpu_hours=(numeric_cpu+close_cpu+diagnostic_cpu)/3600,
                  peak_module_rss_gib=peak_module, conservative_sampled_aggregate_bound_bytes=aggregate_bound,
                  minimum_available_bytes=minimum_memory, minimum_free_disk_bytes=minimum_disk,
                  campaign_wall_hours=(last-first)/3600, compiled_files=verified['compiled_files'],
                  source_bytes=verified['source_bytes'], source_archive_sha256=archive['sha256'])
    (report / 'handoff-totals.json').write_text(json.dumps(totals, indent=2) + '\n')
    handoff = ROOT / 'REGEN-H1.md'
    text = handoff.read_text()
    start = text.index('\n\n') + 2
    end = text.index('\n\nAll 7,964', start)
    text = text[:start] + (
        f"All **7,964 owners and 414,638 theorem axiom audits passed**. Both H1 closing\n"
        f"contracts are kernel-checked, exact, and hypothesis-free. Numeric compilation\n"
        f"used **{numeric_cpu/3600:.3f} CPU-hours**; closing added **{close_cpu:.2f} CPU-seconds**.\n"
        f"The largest module used **{peak_module:.3f} GiB** peak RSS. The conservative\n"
        f"aggregate sampled bound is **{aggregate_bound/1e9:.3f} GB**, below 270 GB.\n"
        f"The authoritative report and receipts are `{report}`.\n\n"
        f"The release's `.git` mount is read-only, so committing in this clone is blocked.\n"
        f"A commit patch is prepared separately for the orchestrator to apply."
    ) + text[end:]
    if 'production_close.py --report-dir "$H1_REGEN_REPORT"' not in text:
        text = text.replace('The hand-written closing modules are',
            'Rebuild the closing modules and verify their exact closed types and axioms:\n\n'
            '```sh\npython3 AKLT/Cert/H1/tools/production_close.py --report-dir "$H1_REGEN_REPORT"\n```\n\n'
            'The hand-written closing modules are', 1)
    handoff.write_text(text)
    lines = [
        'STATUS: PARTIAL (kernel rebuild complete; .git is read-only; measured coverage timing regression remains)', '',
        '# H1 module-system regeneration', '',
        f"All **7,964 generated owners**, **414,638 exported theorems**, and both closed H1 contracts passed fresh kernel checking against the ported release. Numeric compilation used **{numeric_cpu/3600:.3f} CPU-hours**; closing used **{close_cpu:.2f} CPU-seconds**. Diagnostic compiles added **{diagnostic_cpu:.2f} CPU-seconds**. Total campaign compiler CPU: **{(numeric_cpu+close_cpu+diagnostic_cpu)/3600:.3f} hours**. Python export/runner overhead is excluded.", '',
        f"The campaign from the first fresh compiler launch through closing took **{(last-first)/3600:.3f} wall-hours**. All 7,964 compiled owners were absent at initial inspection. No legacy compiled artifact was read, copied, linked, or imported. Dependencies were prebuilt; no Lake update or Mathlib build occurred.", '',
        '## Closed exports', '',
        '```lean',
        'CertData.H1.Close.finiteData : AKLT.Blueprint.Top.H1FiniteDataStatementV2',
        'CertData.H1.Close.certificate : AKLT.Blueprint.Top.CertificateStatement',
        '```', '',
        'Both have no hypotheses. The existing Main and Audit modules contain exact-type `example` checks. Main also checks all 33 ported `AKLT.W.H1C001.main` through `AKLT.W.H1C033.main` leaves and all private premise assemblies. Actual axiom output for each closed export is:', '',
        '```text', '[propext, Classical.choice, Quot.sound]', '```', '',
        'See `closing/Main.stdout`, `closing/Audit.stdout`, and `closing/receipt.json` for exact printed types, all axiom output, commands, hashes, and measurements.', '',
        '## Generators and arithmetic preservation', '',
        'The reversible module envelope adds public imports, exposed public definitions, and `backward.proofsInPublic`. No checker, arithmetic expression, proof body, or input number changed. No Lean checker visibility repair was necessary. The only existing Lean edit is a documentation sentence in H1 Close.Main. See `REGEN-CHANGES.md` for every hand-written change.', '',
        f"The full independent data-only re-export took {reexport['wall_seconds']:.2f} seconds and regenerated all 158,230 logical components and 7,964 owners. Every owner matched the transformed retained source byte for byte. The exact owner/dependency/component map also matched. Inputs are the index and 16 witness chunks under `/home/ubuntu/aklt/data/h1`; all 17 hashes match the legacy production input receipt.", '',
        '## Pilot results', '',
        'Small and large targets were selected for every one of the 25 kinds, by legacy CPU cost for checks or source bytes for data. Every build used a fresh Lean process. Singleton kinds use the same owner for both roles. The two final global singleton assemblies require the entire DAG and were measured at the end of the same initially clean campaign. All other targets and their shared prerequisites form the 5,092-owner pilot plan.', '',
        '| Kind / sample | Owner | Legacy CPU s | New CPU s | Legacy GiB | New GiB |',
        '|---|---|---:|---:|---:|---:|',
    ]
    for row in pilots:
        lines.append(f"| {row['kind']} / {row['role']} | `{row['module'].split('.')[-1]}` | {row['legacy_cpu_seconds']:.2f} | {row['cpu_seconds']:.2f} | {row['legacy_max_rss_kib']/2**20:.3f} | {row['max_rss_kib']/2**20:.3f} |")
    lines += ['', 'The coverage frontier samples use 26–28% more CPU than their legacy receipts. The small profiled control spends 77.3 seconds in kernel type checking versus 61.3 seconds in the legacy profile. Loading private definition bodies (92.17 CPU-seconds) and default private-proof elaboration (88.01 seconds) did not improve the 85.11-second profiled required-header control. No missing exposed body was found and no definition-preserving repair was identified. Production data, checker definitions, and required headers remain unchanged. This timing regression on `AKLT.Cert.H1.Production.coverageShard` is passed to the orchestrator; details and hashed diagnostic receipts are in `coverage-performance.json`.', '',
              '## Production totals by kind', '', '| Kind | Owners | CPU hours | Peak GiB |', '|---|---:|---:|---:|']
    for kind, row in sorted(verified['stages'].items()):
        lines.append(f"| `{kind}` | {row['modules']} | {(row['user_seconds']+row['system_seconds'])/3600:.4f} | {row['max_rss_kib']/2**20:.3f} |")
    lines += ['', 'Stage costs use the final accepted receipt for each owner; total compiler CPU includes every successful fresh build event, including any repeated pilot build.', '', '## Resource controls and receipts', '',
        f"Limits were 36 Lean processes and 270 GB RAM, with a 40 GB available-memory floor and 100 GiB free-disk floor. The initial pilot used up to four workers, the shared-prerequisite pilot used 32, and the remaining production used up to 35. A one-worker coverage frontier also ran alongside the 32-worker pilot, for at most 33 Lean processes. The overlap with the initial pilot and small validation/header runs remained below 36. The largest module used {peak_module:.3f} GiB RSS. A conservative sum of the overlapping runners' sampled peaks is {aggregate_bound/1e9:.3f} GB. Minimum recorded available memory was {minimum_memory/1e9:.3f} GB; minimum recorded disk was {minimum_disk/2**30:.3f} GiB.", '',
        'The append-only `events.jsonl`, individual `receipts/`, separate stdout/stderr/GNU-time files in `logs/`, and theorem-by-theorem `.axioms.json` files record source hashes, all modern module artifact parts, exit status, CPU/wall time, peak RSS, and exact theorem names. Independent `production_receipts.py verify` checked all dependency keys, actual import edges, sources, artifacts, and complete axiom sets. Only propext, Classical.choice, and Quot.sound occur. `cache-test.json` records successful unchanged replay, transitive invalidation, expected kernel rejection, and restoration.', '',
        'All 7,964 production sources remain under `CertData/H1/Generated/Batch/` and `Bridge/`. All modern objects remain under `.lake/build/lib/lean/CertData/H1/Generated/`; closing objects are under the adjacent `Close/`. They are untracked. No production owner source was deleted or compacted. The duplicate scratch tree was removed only after recording all 166,194 hashes in `scratch-sources.sha256`. The complete data-only command recreates it.', '',
        f"`SOURCES.sha256` covers every generated source; `COMPILED.sha256` covers all {verified['compiled_files']:,} generated compiled artifact parts. `verified-production.json` and `closing/receipt.json` give their typed receipts and timings. The deterministic source archive is `{archive['archive']}` ({archive['bytes']:,} bytes), SHA-256 `{archive['sha256']}`. The official installer passed in a fresh scratch project and every installed source hash matched.", '',
        '## Commands and hand-off', '',
        'Exact commands to regenerate from inputs, transform retained sources, build/resume the family, verify receipts, and close both contracts are in `REGEN-H1.md`. The final assembly imports `CertData.H1.Close.Main` and the H3 closing module. It needs the H1 source archive and these matching normal artifacts, including `.olean.private` and `.olean.server`. Lake trace files are not synthesized; `lake env lean` consumes the artifacts directly, while `lake build` may repeat reductions.', '',
        'The official source checks found no generated-source issue. The only two existing package issues are the author/provenance TODO and missing root LICENSE. Lean parsed all 9,079 present first-party headers without error. Combined H3/Solution/Audit and the unconditional Comparator/NanoDa/con-ron pipeline remain the orchestrator’s joint-release work.', '',
        '## Git delivery constraint', '',
        'The release mounts `.git` read-only. `git add` failed with `Unable to create .git/index.lock: Read-only file system`; approval escalation is unavailable. A complete hand-written-change commit patch is prepared in a writable scratch clone for application by the orchestrator. No generated source or object belongs in that commit.', '',
        '## ORCH-SUMMARY', '',
        '- H1 kernel rebuild complete: 7,964 owners and 414,638 exported theorem audits.',
        '- Closed exports: CertData.H1.Close.finiteData and CertData.H1.Close.certificate; exact original types.',
        '- Both exports use only propext, Classical.choice, and Quot.sound; no hypotheses remain.',
        f'- Numeric CPU {numeric_cpu/3600:.3f} h; closing CPU {close_cpu:.2f} s; peak module RSS {peak_module:.3f} GiB.',
        '- All 25 kinds have paired same-owner legacy comparisons; final global singleton pilots occur after prerequisites.',
        '- All owners match full data-only regeneration byte for byte; all input hashes match legacy production.',
        '- No arithmetic/checker/proof edit; Close.Main has one documentation-only edit.',
        '- Coverage frontier CPU is 26–28% higher; private-body/proof-scope tests did not repair it; see coverage-performance.json.',
        '- All production sources and all modern artifact parts remain in this release; no legacy object reused.',
        '- SHA-256 source/compiled manifests, source archive, installer test, and per-theorem receipts are delivered.',
        '- Full reproduction commands are in REGEN-H1.md; all scratch-source removals followed hashing.',
        '- No dependency rebuild, Lake update, package write, or sub-agent was used.',
        '- Exact open delivery: committing in this clone is blocked by read-only .git; apply the supplied commit patch.',
        '- Existing author/provenance TODO and root LICENSE remain for the orchestrator.',
        '- Joint release still needs H3, final assembly, strict Audit, Comparator, NanoDa, and con-ron.',
    ]
    (report / 'report.md').write_text('\n'.join(lines) + '\n')
    print(json.dumps(totals))


if __name__ == '__main__':
    main()
