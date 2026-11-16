"""Level-1 (radius-2 template, independent adversarial unit vectors on all legs leaving it) constants for the
passages of agent 58's closed pair strands (agent 57).  START: strand leaves u = (0,0), whose neighbour c = (0,-1) is
removed (absent), u uniform with three bonds -> diluted without the out bond.  END: strand arrives at v = (0,0)
from s = (0,-1) (passed once), v's neighbour c is removed, v uniform with its two remaining bonds f, g -> diluted with
the same two bonds (the strand pairs with the insertion)."""
import numpy as np
from patch import pattern_custom, Ratio, bkey, add
def end_pattern(kinds, absent, c):
    pat = pattern_custom(kinds, absent, (0, 1) if c != (0, 1) else (1, 0))
    v = (0, 0)
    # undo the out-bond removal: next = cur bonds, v diluted
    pat['bonds_next'] = list(pat['bonds_cur'])
    return pat
res = []
# START, generic: c absent, everything else unvisited (the other insertion site is an ordinary live site)
for out in [(0, 1), (1, 0)]:
    pat = pattern_custom({(0, -1): 'x'}, set(), out)
    R = Ratio(pat); (val, m), vals = R.minimize(restarts=6, seed=1)
    print(f"START (c removed) out={out} {'straight' if out == (0, 1) else 'turn'}: min {val:.5f} spread {vals[-1]-vals[0]:.1e} K={R.K}", flush=True)
# START with c removed AND diluted corners next to c (c was passed once in the trace history) -- a few variants
for extra in [{(1, -1): 'd'}, {(1, 1): 'd'}, {(0, 1): 'd'}]:
    for out in [(0, 1), (1, 0), (-1, 0)]:
        if extra.get(out) is not None:
            continue
        k = {(0, -1): 'x'}; k.update(extra)
        pat = pattern_custom(k, set(), out)
        R = Ratio(pat); (val, m), vals = R.minimize(restarts=3, seed=2)
        print(f"START variant {extra} out={out}: min {val:.5f}", flush=True)
# END: arrival from s=(0,-1) passed once (came straight from (0,-2)); c removed at (0,1) (opposite) or (1,0) (side)
for c in [(0, 1), (1, 0)]:
    kinds = {(0, -1): 'd', (0, -2): 'd', c: 'x'}
    absent = {((0, 0), (0, -1)), ((0, -1), (0, -2)), ((0, -2), (0, -3))}
    pat = end_pattern(kinds, absent, c)
    R = Ratio(pat); (val, m), vals = R.minimize(restarts=6, seed=3)
    print(f"END c={c}: min {val:.5f} spread {vals[-1]-vals[0]:.1e} K={R.K}", flush=True)
    # arrival site passed twice / arrival with a turn
    kinds2 = {(0, -1): 'd', (1, -1): 'd', c: 'x'}
    absent2 = {((0, 0), (0, -1)), ((0, -1), (1, -1)), ((1, -1), (2, -1))}
    if c != (1, 0):
        pat = end_pattern(kinds2, absent2, c)
        R = Ratio(pat); (val, m), vals = R.minimize(restarts=3, seed=4)
        print(f"END c={c}, previous step a turn: min {val:.5f}", flush=True)
