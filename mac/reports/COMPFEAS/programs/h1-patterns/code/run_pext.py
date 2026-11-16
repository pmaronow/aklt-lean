"""Minimise the level-1 constant over a pickled pattern class (agent 57).  Usage: run_pext.py reps.pkl chunk nchunks
restarts out.json"""
import sys, json, time, pickle
from patch import Ratio
import patch
from pext import V
pk, chunk, nchunks, restarts, outf = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
reps = pickle.load(open(pk, 'rb'))
T = set((i, j) for i in range(-2, 3) for j in range(-2, 3) if abs(i) + abs(j) <= 2)
def build(kinds, present, out):
    sites = sorted(set(kinds) | set(x for b in present for x in b) | {V})
    kk = {x: kinds.get(x, 'u') for x in sites}; kk[V] = 'u'
    bonds = sorted(present)
    slots = [x for x in sites for y in patch.nbrs(x) if y not in T]
    kn = dict(kk); kn[V] = 'd'
    return dict(v=V, sites=sites, kinds_cur=kk, kinds_next=kn, bonds_cur=bonds,
                bonds_next=[b for b in bonds if b != patch.bkey(V, out)], slots=slots, kind_all=kk)
keys = sorted(reps)[chunk::nchunks]
res = []; t0 = time.time()
import os
done = set()
if len(sys.argv) > 6 and os.path.exists(sys.argv[6]):
    res = json.load(open(sys.argv[6])); done = set(r['key'] for r in res)
for i, key in enumerate(keys):
    if repr(key) in done:
        continue
    kinds, present, out = reps[key]
    R = Ratio(build(kinds, present, out))
    if R.K == 0:
        val = float(R.f(__import__('numpy').zeros((0, 3)))); vals = [val, val]
    else:
        (val, m), vals = R.minimize(restarts=restarts, seed=i)
    val = float(val); vals = [float(x) for x in vals]
    res.append(dict(key=repr(key), out=list(out), kinds={str(x): c for x, c in kinds.items()}, present=[list(map(list, b)) for b in present],
                    min=val, spread=vals[-1] - vals[0], K=R.K))
    if i % 200 == 0:
        json.dump(res, open(outf, 'w'))
        print(i, len(keys), round(time.time() - t0), 'min', round(min(r['min'] for r in res), 5), flush=True)
json.dump(res, open(outf, 'w'))
print('done', len(keys), round(time.time() - t0), flush=True)
