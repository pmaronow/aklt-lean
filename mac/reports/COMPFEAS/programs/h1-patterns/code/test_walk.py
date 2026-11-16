"""Exact test of the stopped walk identity (agent 54 Lemma 1.1) in the diluted-site form (agent 57):
E_G[a.n_x] = sum_{w in T(x,S)} 3^{-|w|} (Z_{G;[w]}/Z_G) E_{G;[w]}[a.n_end],
G;[w] = G minus the bonds of w, visited sites diluted: passed once -> (3/5)unif + (2/5)delta_0, twice -> (3/5)delta_0.
Random unit pins on random boundary legs of small grids; S = pin sites (+ optional extra sites)."""
import sys
import numpy as np
from spins import contract

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)


def unit(v):
    return v / np.linalg.norm(v)


def run(W, H, npins, extraS, x):
    V = [(i, j) for i in range(W) for j in range(H)]
    E = [((i, j), (i + 1, j)) for i in range(W - 1) for j in range(H)] + [((i, j), (i, j + 1)) for i in range(W) for j in range(H - 1)]
    deg = {v: sum(v in e for e in E) for v in V}
    legs = [v for v in V for _ in range(4 - deg[v])]
    rng.shuffle(legs)
    pins = {}
    for v in legs[:npins]:
        if v == x:
            continue
        pins.setdefault(v, []).append(unit(rng.normal(size=3)))
    S = set(pins) | set(extraS)
    S.discard(x)
    ext = {v: [np.concatenate([[1.0], p]) for p in ps] for v, ps in pins.items()}
    a = rng.normal(size=3)
    ZG = contract({v: 'u' for v in V}, [(e[0], e[1], 1.0) for e in E], ext)
    lhs = contract({v: 'u' for v in V}, [(e[0], e[1], 1.0) for e in E], ext, insert=(x, a)) / ZG
    adj = {v: [] for v in V}
    for k, e in enumerate(E):
        adj[e[0]].append((k, e[1])); adj[e[1]].append((k, e[0]))
    total = 0.0; count = [0]
    used = []; passes = {v: 0 for v in V}

    def dfs(v):
        nonlocal total
        if used and v in S:
            kinds = {u: ('u', 'd', 'c')[passes[u]] for u in V}
            bonds = [(E[k][0], E[k][1], 1.0) for k in range(len(E)) if k not in used]
            Zw = contract(kinds, bonds, ext)
            Nw = contract(kinds, bonds, ext, insert=(v, a))
            total += 3.0 ** (-len(used)) * Nw / ZG
            count[0] += 1
            return
        passes[v] += 1
        for k, y in adj[v]:
            if k in used:
                continue
            used.append(k)
            dfs(y)
            used.pop()
        passes[v] -= 1

    dfs(x)
    return lhs, total, count[0], len(pins), sorted(S)


for (W, H, npins, extra, x) in [(2, 2, 3, [], (0, 0)), (3, 2, 4, [], (1, 0)), (3, 3, 5, [], (1, 1)), (3, 3, 8, [(2, 1)], (1, 1)),
                               (4, 3, 6, [], (1, 1)), (3, 3, 12, [], (1, 1)), (4, 3, 4, [(3, 2)], (0, 1))]:
    lhs, rhs, n, npin, S = run(W, H, npins, extra, x)
    print(f"{W}x{H} pins={npin} |S|={len(S)} x={x}: trails={n}  lhs={lhs:+.15f}  rhs={rhs:+.15f}  diff={lhs - rhs:+.2e}", flush=True)

# larger cases with many revisits (few pins, S small)
for (W, H, npins, extra, x, seed) in [(4, 4, 1, [], (1, 1), 5), (5, 3, 2, [], (2, 1), 6), (4, 4, 2, [], (2, 2), 9)]:
    rng = np.random.default_rng(seed)
    lhs, rhs, n, npin, S = run(W, H, npins, extra, x)
    print(f"{W}x{H} pins={npin} S={S} x={x}: trails={n}  lhs={lhs:+.15f}  rhs={rhs:+.15f}  diff={lhs - rhs:+.2e}", flush=True)
