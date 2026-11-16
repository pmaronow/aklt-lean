#!/usr/bin/env python3
"""truth_groups.py PART...: one truth-sweep brief per group of <= 8 open leaves from reports/BP_<PART>/leaves.json."""
import json, os, sys
A = os.path.expanduser('~/aklt'); common = open(f'{A}/briefs/TRUTH-COMMON.md').read(); keys = []; table = {}
for part in sys.argv[1:]:
    L = json.load(open(f'{A}/reports/BP_{part}/leaves.json'))
    L = L if isinstance(L, list) else L.get('leaves', [])
    for i in range(0, len(L), 8):
        g = L[i:i+8]; key = f'TS_{part}_{i//8+1:02d}'; os.makedirs(f'{A}/reports/{key}', exist_ok=True)
        lines = '\n'.join(f"- `{x['lean_name']}` (module `{x.get('module','?')}`, paper label {x.get('paper_label','?')})" for x in g)
        open(f'{A}/briefs/{key}.md', 'w').write(f"# {key} — truth sweep of blueprint leaves\n\n**Your leaves:**\n{lines}\n\nYour working directory is `{A}/reports/{key}/`.\n" + common)
        keys.append(key); table[key] = [x['lean_name'] for x in g]
json.dump(table, open(f'{A}/state/truth_groups.json', 'w'), indent=1); print(' '.join(keys))
