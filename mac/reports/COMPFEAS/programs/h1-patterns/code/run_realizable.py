"""Worst case over all realisable radius-2 patterns (agent 57).  Usage: run_realizable.py chunk nchunks restarts out.json"""
import sys, json, time
import numpy as np
from realizable import enumerate_realizable, canon, CORN, D1, TIPS, V, nbrs, bkey
from patch import pattern_custom, Ratio
chunk, nchunks, restarts, outf = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
TSET = set([V] + D1 + CORN + TIPS)
R = enumerate_realizable()
reps = {}
for kinds, absent in R:
    a = frozenset(b for b in absent if b[0] in TSET and b[1] in TSET)
    k = dict(kinds)
    for c in CORN:
        if k[c] == 'd' and not [y for y in nbrs(c) if y in D1 and bkey(c, y) not in absent]:
            k[c] = 'c'
    for out in [(0, 1), (1, 0)]:
        if k.get((out[0], out[1]), 'u') == 'c':
            continue
        key = canon(k, a, out)
        if key not in reps:
            reps[key] = (k, a, out)
keys = sorted(reps)
mine = keys[chunk::nchunks]
res = []
t0 = time.time()
for i, key in enumerate(mine):
    k, a, out = reps[key]
    pat = pattern_custom(k, a, out)
    Rt = Ratio(pat)
    (val, m), vals = Rt.minimize(restarts=restarts, seed=i)
    res.append(dict(out=out, kinds={str(x): c for x, c in k.items()}, absent=[list(map(list, b)) for b in a], min=val,
                    spread=vals[-1] - vals[0], K=Rt.K))
    if i % 20 == 0:
        json.dump(res, open(outf, 'w'))
        print(i, len(mine), round(time.time() - t0), 'cur min straight', min([r['min'] for r in res if r['out'] == (0, 1)] or [9]),
              'turn', min([r['min'] for r in res if r['out'] == (1, 0)] or [9]), flush=True)
json.dump(res, open(outf, 'w'))
print('done', len(mine), round(time.time() - t0), flush=True)
