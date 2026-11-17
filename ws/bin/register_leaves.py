#!/usr/bin/env python3
"""register_leaves.py [--dry] PART... : for every open leaf of reports/BP_<PART>/leaves.json whose truth-sweep
verdict is TRUE, write briefs/<KEY>.md + state/leafjson/<KEY>.json and run `aklt-ladder add`. Prints a summary."""
import json, os, sys, glob, subprocess, re
A = os.path.expanduser('~/aklt'); dry = '--dry' in sys.argv; parts = [p for p in sys.argv[1:] if p != '--dry']
verd = {}
for f in glob.glob(f'{A}/reports/TS*_*/verdicts.jsonl'):
    for n, line in enumerate(open(f, errors='replace'), 1):
        line = line.strip()
        if not line: continue
        try: d = json.loads(line)
        except Exception as e: sys.exit(f'BAD JSONL {f}:{n}: {e}')
        verd[d['leaf']] = d
common = open(f'{A}/briefs/LEAF-COMMON.md').read(); os.makedirs(f'{A}/state/leafjson', exist_ok=True)
reg = json.load(open(f'{A}/state/leaf-keys.json')) if os.path.exists(f'{A}/state/leaf-keys.json') else {}
summary = {}
for part in parts:
    L = json.load(open(f'{A}/reports/BP_{part}/leaves.json')); L = L if isinstance(L, list) else L.get('leaves', [])
    c = {'added': 0, 'skipped_verdict': 0, 'no_verdict': 0, 'already': 0, 'failed': 0}
    for i, x in enumerate(L, 1):
        name = x['lean_name']; v = verd.get(name)
        if 'superseded' in json.dumps([x.get('status'), x.get('adaptation_status')]).lower(): c['superseded'] = c.get('superseded', 0) + 1; continue
        if v is None: c['no_verdict'] += 1; continue
        if v['verdict'] != 'TRUE': c['skipped_verdict'] += 1; continue
        if name in reg: c['already'] += 1; continue
        key = f'{part}{i:03d}'
        route = v.get('route') or x.get('suggested_proof_route') or ''
        brief = (f"# {key} — prove one blueprint leaf\n\n**Statement:** `{name}` (module `{x['module']}`). **Paper:** label "
                 f"{x.get('paper_label','?')} {x.get('paper_locator', x.get('paper_lines',''))}. **Difficulty (estimate):** {v.get('difficulty', x.get('difficulty','?'))}.\n"
                 f"**Suggested route:** {route}\n**Trap notes:** {x.get('trap_note','')}\n" + common)
        open(f'{A}/briefs/{key}.md', 'w').write(brief)
        lj = {'key': key, 'node': name, 'module': x['module'], 'brief': f'{A}/briefs/{key}.md', 'deps': []}
        json.dump(lj, open(f'{A}/state/leafjson/{key}.json', 'w'))
        if dry: c['added'] += 1; continue
        r = subprocess.run([f'{A}/bin/aklt-ladder', 'add', f'{A}/state/leafjson/{key}.json'], capture_output=True, text=True)
        if r.returncode == 0: c['added'] += 1; reg[name] = key
        else: c['failed'] += 1; print('FAILED', key, name, (r.stdout + r.stderr)[-300:].replace('\n', ' '))
    summary[part] = c
json.dump(reg, open(f'{A}/state/leaf-keys.json', 'w'), indent=1); print(json.dumps(summary))
