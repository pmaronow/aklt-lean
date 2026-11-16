"""Greedy discrete descent over the LITERAL P_ext class (any status, no consistency), to see how low it goes
(agent 57).  Moves: change one site's option.  1 restart per evaluation, best re-checked with 12 restarts."""
import itertools, json, sys
from pext import site_options, effective, E, N, W, S, CORN, V, bkey
from pext_build import build
from patch import Ratio
sites = [E, N, W, S] + CORN
opts = {x: site_options(x) for x in sites}
cache = {}
def val(ch, out, restarts=1):
    kinds, present = effective(ch)
    if bkey(V, out) not in present:
        return 9.0
    key = (out, tuple(sorted(kinds.items())), tuple(sorted(present)))
    if key in cache and restarts == 1:
        return cache[key]
    R = Ratio(build(kinds, present, out))
    if R.K == 0:
        v = float(R.f(__import__('numpy').zeros((0, 3))))
    else:
        (v, m), vals = R.minimize(restarts=restarts, seed=7)
    cache[key] = float(v)
    return float(v)
results = []
starts = []
for out in [N, E]:
    allU = {x: opts[x][0] for x in sites}; allU[S] = ('d', frozenset([bkey(S, (1, -1)), bkey(S, (-1, -1))]))
    starts.append((out, allU))
# the 0.9256 literal pattern: N keeps {v, tip}, corners U, s keeps {(0,-2),(1,-1)} -- as found by the sample (out = turn)
ch = {x: opts[x][0] for x in sites}
ch[N] = ('d', frozenset([bkey(N, V), bkey(N, (0, 2))])); ch[S] = ('d', frozenset([bkey(S, (0, -2)), bkey(S, (1, -1))]))
starts.append(((-1, 0), ch))
for out, ch in starts:
    ch = dict(ch); cur = val(ch, out)
    improved = True
    while improved:
        improved = False
        for x in sites:
            for o in opts[x]:
                if o == ch[x]:
                    continue
                c2 = dict(ch); c2[x] = o
                v = val(c2, out)
                if v < cur - 1e-7:
                    cur, ch, improved = v, c2, True
        print('out', out, 'sweep value', round(cur, 5), flush=True)
    vfinal = val(ch, out, restarts=12)
    kinds, present = effective(ch)
    results.append(dict(out=out, value=vfinal, statuses={str(x): [o[0], sorted(map(list, o[1]))] for x, o in ch.items()}))
    print('FINAL out', out, round(vfinal, 5), {str(x): o[0] + str(sorted(o[1])) for x, o in ch.items() if o[0] != 'u'}, flush=True)
json.dump(results, open(sys.argv[1], 'w'))
