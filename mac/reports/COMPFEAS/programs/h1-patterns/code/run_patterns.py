import sys, time, json
import numpy as np
from patterns import enumerate_patterns
from patch import pattern_from_trail, Ratio
L = int(sys.argv[1]); restarts = int(sys.argv[2]); outf = sys.argv[3]
pats, first = enumerate_patterns(L)
res = []
t0 = time.time()
for key, cnt in sorted(pats.items(), key=lambda kv: -kv[1]):
    trail, out = first[key]
    pat = pattern_from_trail(trail, out)
    R = Ratio(pat)
    (val, m), vals = R.minimize(restarts=restarts, seed=1)
    turn = 'start' if len(trail) == 1 else ('straight' if (out[0] == -trail[-2][0] and out[1] == -trail[-2][1]) else 'turn')
    nd = sum(1 for x, k in pat['kind_all'].items() if k == 'd'); nc = sum(1 for x, k in pat['kind_all'].items() if k == 'c')
    res.append(dict(key=str(key), count=cnt, trail=trail, out=out, type=turn, min=val, spread=vals[-1] - vals[0], nd=nd, nc=nc, K=R.K))
    print(f"{turn:8s} min={val:.5f} spread={vals[-1]-vals[0]:.1e} K={R.K} dil={nd} const={nc} count={cnt} trail={trail} out={out}  t={time.time()-t0:.0f}", flush=True)
json.dump(res, open(outf, 'w'))
