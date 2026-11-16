"""Re-minimise the worst patterns (and every pattern whose restarts disagreed) with many restarts (agent 57).
Usage: verify_worst.py nworst restarts out.json in1.json [in2.json ...]"""
import sys, json, ast
from patch import pattern_custom, Ratio
nworst, restarts, outf = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
res = []
for f in sys.argv[4:]:
    res += json.load(open(f))
sel = []
for out in ([0, 1], [1, 0]):
    rows = sorted([r for r in res if r['out'] == out], key=lambda r: r['min'])
    sel += rows[:nworst]
sel += [r for r in res if r['spread'] > 1e-7 and r not in sel]
print('verifying', len(sel), flush=True)
outl = []
for i, r in enumerate(sel):
    kinds = {ast.literal_eval(x): c for x, c in r['kinds'].items()}
    absent = set(tuple(map(tuple, b)) for b in r['absent'])
    R = Ratio(pattern_custom(kinds, absent, tuple(r['out'])))
    (val, m), vals = R.minimize(restarts=restarts, seed=1000 + i)
    outl.append(dict(r, min_old=r['min'], min=min(val, r['min']), spread_new=vals[-1] - vals[0], nrestarts=restarts))
    if val < r['min'] - 1e-9 or i % 25 == 0:
        print(i, tuple(r['out']), 'old', round(r['min'], 6), 'new', round(val, 6), 'spread', f"{vals[-1]-vals[0]:.1e}", flush=True)
    json.dump(outl, open(outf, 'w'))
print('done', flush=True)
