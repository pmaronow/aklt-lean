"""Alm-type transfer-matrix upper bound on the growth rate of the weighted trail sums (agent 57).
States: windows = trails of length m (direction strings, up to translation).  M_k(s, s') = weighted number of
k-step extensions of s (bond-avoiding together with s) whose last m steps are s'.  Step weights computed with the
window as the only history: first visit -> ws (straight) / wt (turn); revisit -> wr = 1/4 (>= 1/5 and 1/4).
Every true weighted trail sum satisfies A_{n+k} <= A_n M_k (componentwise over final windows), so the growth rate
is <= rho(M_k)^(1/k); Collatz-Wielandt: rho <= max_i (M x)_i / x_i for any positive x.
Usage: alm.py m k cs ct"""
import sys, itertools
import numpy as np
from scipy.sparse import csr_matrix
m, k = int(sys.argv[1]), int(sys.argv[2]); cs, ct = float(sys.argv[3]), float(sys.argv[4])
ws, wt, wr = 1 / (3 * cs), 1 / (3 * ct), 0.25
D = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def walk(dirs):
    p = (0, 0); pts = [p]; bonds = set(); dep = {}
    for d in dirs:
        q = (p[0] + D[d][0], p[1] + D[d][1])
        b = (min(p, q), max(p, q))
        if b in bonds:
            return None
        bonds.add(b); dep[p] = dep.get(p, 0) + 1; p = q; pts.append(p)
    return p, bonds, dep


states = []
def gen(prefix):
    if len(prefix) == m:
        states.append(tuple(prefix)); return
    for d in range(4):
        if prefix and d == (prefix[-1] + 2) % 4:
            continue
        if walk(prefix + [d]) is not None:
            gen(prefix + [d])
gen([])
idx = {s: i for i, s in enumerate(states)}
rows, cols, vals = [], [], []
for s in states:
    p, bonds, dep = walk(list(s))
    acc = {}
    def ext(p, last, bonds, dep, seq, w):
        if len(seq) == k:
            t = (tuple(s) + tuple(seq))[-m:]
            acc[t] = acc.get(t, 0.0) + w; return
        for d in range(4):
            q = (p[0] + D[d][0], p[1] + D[d][1])
            b = (min(p, q), max(p, q))
            if b in bonds:
                continue
            ww = wr if dep.get(p, 0) >= 1 else (ws if d == last else wt)
            bonds.add(b); dep[p] = dep.get(p, 0) + 1
            ext(q, d, bonds, dep, seq + [d], w * ww)
            bonds.discard(b); dep[p] -= 1
    ext(p, s[-1], set(bonds), dict(dep), [], 1.0)
    for t, w in acc.items():
        rows.append(idx[s]); cols.append(idx[t]); vals.append(w)
M = csr_matrix((vals, (rows, cols)), shape=(len(states), len(states)))
x = np.ones(len(states))
for it in range(3000):
    y = M @ x
    lam = y.max() / x.max()
    x = y / y.max()
cw = (M @ x / x).max()
print(f"m={m} k={k} cs={cs} ct={ct} states={len(states)} rho(M_k)<= {cw:.6f}  growth<= {cw ** (1 / k):.6f}")
