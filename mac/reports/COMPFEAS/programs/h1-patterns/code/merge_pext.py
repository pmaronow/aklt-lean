"""Merge P_ext^59 result files (dedupe by key, keep the smaller minimum) and summarise (agent 57).
Usage: merge_pext.py out.json in1.json [...]"""
import sys, json, pickle
SC = '/tmp/claude-0/-home-user-otis-claude/9ebf8585-0840-54e3-b6a3-dc01fea1715b/scratchpad/agents/57'
reps = pickle.load(open(SC + '/pext59_reps.pkl', 'rb'))
allkeys = set(repr(k) for k in reps)
best = {}
for f in sys.argv[2:]:
    for r in json.load(open(f)):
        if r['key'] not in best or r['min'] < best[r['key']]['min']:
            best[r['key']] = r
res = list(best.values())
from patch import bkey, nbrs
D1 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
FULL = set()
for x in D1:
    for y in nbrs(x):
        if y != (0, 0) or x != (0, -1):
            FULL.add(bkey(x, y))
json.dump(res, open(sys.argv[1], 'w'))
print('patterns done', len(res), 'of', len(allkeys), 'missing', len(allkeys - set(best)))
for typ, out in [('straight', [0, 1]), ('turn', [1, 0])]:
    rows = sorted([r for r in res if r['out'] == out], key=lambda r: r['min'])
    print(typ, len(rows), 'worst', [round(r['min'], 5) for r in rows[:6]], 'max spread', f"{max(r['spread'] for r in rows):.1e}")
    for r in rows[:3]:
        pres = set(tuple(map(tuple, b)) for b in r['present'])
        missing = sorted(b for b in FULL if b not in pres)
        print('   ', round(r['min'], 5), 'K', r['K'], 'non-U:', {k: c for k, c in r['kinds'].items() if c != 'u'}, 'missing bonds:', missing)
