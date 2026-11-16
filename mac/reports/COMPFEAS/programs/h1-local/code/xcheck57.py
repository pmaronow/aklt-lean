"""Cross-check: agent 57's own slot network (patch.Ratio on the stored P_ext^59 keys, 3 slots per tip, 2 per corner)
against the ring engine (ring.py, tips reduced to one vector of radius 3/5) at random unit vectors with the three
slots of each tip tied.  Covers all 7,962 patterns (agent 57's slot model)."""
import sys, json, ast
import numpy as np
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/57-vector-channel/code')
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
import patch
from patch import Ratio
from ring import Pattern, load, TIP

V = (0, 0)
T = set((i, j) for i in range(-2, 3) for j in range(-2, 3) if abs(i) + abs(j) <= 2)
TIPOF = {t: x for x, t in TIP.items()}


def build(kinds, present, out):
    sites = sorted(set(kinds) | set(x for b in present for x in b) | {V})
    kk = {x: kinds.get(x, 'u') for x in sites}; kk[V] = 'u'
    bonds = sorted(present)
    slots = [x for x in sites for y in patch.nbrs(x) if y not in T]
    kn = dict(kk); kn[V] = 'd'
    return dict(v=V, sites=sites, kinds_cur=kk, kinds_next=kn, bonds_cur=bonds,
                bonds_next=[b for b in bonds if b != patch.bkey(V, out)], slots=slots, kind_all=kk)


P = load()
step = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = np.random.default_rng(11)
worst = 0.0; cnt = 0
for r in P[::step]:
    kinds = {ast.literal_eval(k): c for k, c in r['kinds'].items()}
    present = [patch.bkey(tuple(a), tuple(b)) for a, b in r['present']]
    pat = build(kinds, present, tuple(r['out']))
    R = Ratio(pat)
    p = Pattern(r, refined=False)
    U = rng.normal(size=(p.nv, 3)); U /= np.linalg.norm(U, axis=1, keepdims=True)
    if R.K == 0:
        continue
    by = {}
    for i, (x, t) in enumerate(p.vars):
        by.setdefault(x, []).append(U[i])
    pos = {}
    m = np.zeros((R.K, 3))
    for k, x in enumerate(pat['slots']):
        if x in TIPOF and TIPOF[x] in by:
            m[k] = by[TIPOF[x]][0]                    # tied tip slots: field (3/5) u on the d1 site
        elif x in by:
            j = pos.get(x, 0); pos[x] = j + 1
            m[k] = by[x][j]
        else:                                         # site without present bond: its factor cancels in the ratio
            w = rng.normal(size=3); m[k] = w / np.linalg.norm(w)
    d = abs(R.f(m) - p.ratio(U))
    worst = max(worst, d); cnt += 1
print('patterns checked', cnt, 'max |agent-57 network - ring engine| =', worst)
