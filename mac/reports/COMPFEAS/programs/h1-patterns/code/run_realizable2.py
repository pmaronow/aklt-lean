"""Second pass: patterns that appear only once the status 'start site passed twice' is allowed (agent 57).
Usage: run_realizable2.py chunk nchunks restarts out.json"""
import sys, json, time
import realizable as RZ
from realizable import canon, CORN, D1, TIPS, V, nbrs, bkey
from patch import pattern_custom, Ratio
chunk, nchunks, restarts, outf = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
TSET = set([V] + D1 + CORN + TIPS)
def reps_of(R):
    reps = {}
    for kinds, absent in R:
        a = frozenset(b for b in absent if b[0] in TSET and b[1] in TSET)
        k = dict(kinds)
        for c in CORN:
            if k[c] == 'd' and not [y for y in nbrs(c) if y in D1 and bkey(c, y) not in absent]:
                k[c] = 'c'
        for out in [(0, 1), (1, 0)]:
            if k.get(out, 'u') == 'c':
                continue
            key = canon(k, a, out)
            if key not in reps:
                reps[key] = (k, a, out)
    return reps
RZ.EXTRA = False; base = reps_of(RZ.enumerate_realizable())
RZ.EXTRA = True; ext = reps_of(RZ.enumerate_realizable())
new = sorted(k for k in ext if k not in base)
print('base', len(base), 'extended', len(ext), 'new', len(new), flush=True)
mine = new[chunk::nchunks]
res = []; t0 = time.time()
for i, key in enumerate(mine):
    k, a, out = ext[key]
    Rt = Ratio(pattern_custom(k, a, out))
    (val, m), vals = Rt.minimize(restarts=restarts, seed=i)
    res.append(dict(out=out, kinds={str(x): c for x, c in k.items()}, absent=[list(map(list, b)) for b in a], min=val,
                    spread=vals[-1] - vals[0], K=Rt.K))
    if i % 20 == 0:
        json.dump(res, open(outf, 'w'))
        print(i, len(mine), round(time.time() - t0), min(r['min'] for r in res), flush=True)
json.dump(res, open(outf, 'w'))
print('done', round(time.time() - t0), flush=True)
