import sys
import numpy as np
from patch import pattern_custom, Ratio
v = (0, 0); s = (0, -1)
base_k = {s: 'd', (0, -2): 'd'}
base_ab = {(v, s), (s, (0, -2)), ((0, -2), (0, -3))}
variants = [('generic', {}, set())]
for c in [(1, 1), (-1, 1), (1, -1), (-1, -1)]:
    variants.append((f'corner {c} absent', {c: 'x'}, set()))
    variants.append((f'corner {c} dil', {c: 'd'}, set()))
for c, y in [((1, 1), (1, 0)), ((1, 1), (0, 1)), ((-1, 1), (0, 1)), ((1, -1), (1, 0)), ((1, -1), (0, -1))]:
    variants.append((f'corner {c} bond to {y} cut, corner live-branch', {c: 'u'}, {(c, y)}))
for t in [(2, 0), (0, 2), (-2, 0)]:
    variants.append((f'tip {t} absent', {t: 'x'}, set()))
for e, r in [((1, 0), (2, 0)), ((1, 0), (1, 1)), ((0, 1), (1, 1)), ((0, 1), (0, 2)), ((-1, 0), (-1, 1))]:
    # e passed once, remaining bonds {v, r}: delete e's other two bonds
    others = [y for y in [(e[0] + 1, e[1]), (e[0] - 1, e[1]), (e[0], e[1] + 1), (e[0], e[1] - 1)] if y not in (v, r)]
    variants.append((f'nbr {e} dil keeps {r}', {e: 'd'}, {(e, o) for o in others}))
variants.append(('all four corners absent', {(1, 1): 'x', (-1, 1): 'x', (1, -1): 'x', (-1, -1): 'x'}, set()))
variants.append(('top corners absent', {(1, 1): 'x', (-1, 1): 'x'}, set()))
variants.append(('arrival site const', {s: 'c'}, set()))
for out in [(0, 1), (1, 0), (-1, 0)]:
    typ = 'straight' if out == (0, 1) else 'turn'
    for name, k, ab in variants:
        kk = dict(base_k); kk.update(k)
        pat = pattern_custom(kk, base_ab | ab, out)
        if pat['kind_all'].get((v[0] + out[0], v[1] + out[1])) not in ('u', 'd'):
            continue
        R = Ratio(pat)
        (val, m), vals = R.minimize(restarts=3, seed=2)
        print(f"{typ:8s} out={out} {name:45s} K={R.K:2d} min={val:.5f} spread={vals[-1]-vals[0]:.1e}", flush=True)
