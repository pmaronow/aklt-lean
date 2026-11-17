#!/usr/bin/env python3
"""truth_groups2.py PART...: truth-sweep briefs for leaves of reports/BP_<PART>/leaves.json that have no verdict yet
and are not superseded (groups of <= 8). Keys TS2_<PART>_NN."""
import json, os, sys, glob
A = os.path.expanduser('~/aklt'); common = open(f'{A}/briefs/TRUTH-COMMON.md').read(); keys = []
seen = set()
for f in glob.glob(f'{A}/reports/TS*_*/verdicts.jsonl'):
    for line in open(f, errors='replace'):
        try: seen.add(json.loads(line)['leaf'])
        except Exception: pass
for part in sys.argv[1:]:
    L = json.load(open(f'{A}/reports/BP_{part}/leaves.json')); L = L if isinstance(L, list) else L.get('leaves', [])
    L = [x for x in L if x['lean_name'] not in seen and 'superseded' not in json.dumps([x.get('status'), x.get('adaptation_status')]).lower()]
    for i in range(0, len(L), 8):
        g = L[i:i+8]; key = f'TS2_{part}_{i//8+1:02d}'; os.makedirs(f'{A}/reports/{key}', exist_ok=True)
        lines = '\n'.join(f"- `{x['lean_name']}` (module `{x.get('module','?')}`, paper label {x.get('paper_label','?')})" for x in g)
        open(f'{A}/briefs/{key}.md', 'w').write(f"# {key} — truth sweep of blueprint leaves\n\n**Your leaves:**\n{lines}\n\nYour working directory is `{A}/reports/{key}/`.\n" + common)
        keys.append(key)
print(' '.join(keys))
