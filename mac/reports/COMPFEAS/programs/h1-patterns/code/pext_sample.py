"""Timing / value sample of P_ext (agent 57).  Usage: pext_sample.py nsample restarts out.json"""
import sys, time, json, random, pickle, os
from pext import enumerate_pext, V, S
from patch import Ratio
import patch
n, restarts, outf = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
cache = '/tmp/claude-0/-home-user-otis-claude/9ebf8585-0840-54e3-b6a3-dc01fea1715b/scratchpad/agents/57/pext_reps.pkl'
if os.path.exists(cache):
    reps = pickle.load(open(cache, 'rb'))
else:
    reps = enumerate_pext(); pickle.dump(reps, open(cache, 'wb'))
keys = sorted(reps)
random.seed(1)
sample = random.sample(keys, n)
def build(kinds, present, out):
    """pattern dict for the engine from kinds/present bonds (tips live when their bond is present)."""
    sites = sorted(set(kinds) | set(x for b in present for x in b))
    kk = {x: kinds.get(x, 'u') for x in sites}
    kk[V] = 'u'
    bonds = sorted(present)
    # slots: legs leaving the template from tips (3 each) and corners (2 each, kept or dropped -> slot)
    T = set((i, j) for i in range(-2, 3) for j in range(-2, 3) if abs(i) + abs(j) <= 2)
    slots = [x for x in sites for y in patch.nbrs(x) if y not in T]
    yout = out
    kn = dict(kk); kn[V] = 'd'
    return dict(v=V, sites=sites, kinds_cur=kk, kinds_next=kn, bonds_cur=bonds,
                bonds_next=[b for b in bonds if b != patch.bkey(V, yout)], slots=slots, kind_all=kk)
res = []; t0 = time.time()
for i, key in enumerate(sample):
    kinds, present, out = reps[key]
    t = time.time()
    R = Ratio(build(kinds, present, out))
    (val, m), vals = R.minimize(restarts=restarts, seed=i)
    res.append(dict(key=repr(key), out=out, min=val, K=R.K, nsites=len(R.pat['sites']), t=time.time() - t))
json.dump(res, open(outf, 'w'))
import numpy as np
print('sample', n, 'mean time', np.mean([r['t'] for r in res]), 'min value', min(r['min'] for r in res),
      'quantiles', np.round(np.quantile([r['min'] for r in res], [0, .01, .1, .5]), 4))
