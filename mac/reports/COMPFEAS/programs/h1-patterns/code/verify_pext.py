"""Re-minimise the worst P_ext patterns (and those whose restarts disagreed) with many restarts (agent 57).
Usage: verify_pext.py nworst restarts out.json in1.json [...]"""
import sys, json, ast
from patch import Ratio
from pext_build import build
nworst, restarts, outf = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
res = []
for f in sys.argv[4:]:
    res += json.load(open(f))
sel = []
for out in ([0, 1], [1, 0]):
    sel += sorted([r for r in res if r['out'] == out], key=lambda r: r['min'])[:nworst]
sel += [r for r in res if r['spread'] > 1e-7 and r not in sel]
print('verifying', len(sel), flush=True)
outl = []
for i, r in enumerate(sel):
    kinds = {ast.literal_eval(x): c for x, c in r['kinds'].items()}
    present = frozenset(tuple(map(tuple, b)) for b in r['present'])
    R = Ratio(build(kinds, present, tuple(r['out'])))
    (val, m), vals = R.minimize(restarts=restarts, seed=5000 + i)
    outl.append(dict(r, min_old=r['min'], min=min(val, r['min']), spread_new=vals[-1] - vals[0]))
    if val < r['min'] - 1e-9:
        print('improved', i, r['out'], r['min'], '->', val, flush=True)
    json.dump(outl, open(outf, 'w'))
print('done', flush=True)
