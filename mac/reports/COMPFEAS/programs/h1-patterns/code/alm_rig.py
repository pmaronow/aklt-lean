"""Rigorous version of alm.py (agent 57): the transfer matrix entries are polynomials in the step weights with
integer coefficients (counted exactly), evaluated in ball arithmetic (python-flint arb); the Collatz-Wielandt
bound max_i (M x)_i / x_i is evaluated in ball arithmetic for a positive vector x (from float power iteration).
Usage: alm_rig.py m k c_s c_t   (constants as decimal strings, taken as exact rationals)."""
import sys
from fractions import Fraction as Fr
import numpy as np
import flint
from flint import arb, fmpq
flint.ctx.prec = 80
m, k = int(sys.argv[1]), int(sys.argv[2]); cs, ct = Fr(sys.argv[3]), Fr(sys.argv[4])
D = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def walk(dirs):
    p = (0, 0); bonds = set(); dep = {}
    for d in dirs:
        q = (p[0] + D[d][0], p[1] + D[d][1]); b = (min(p, q), max(p, q))
        if b in bonds:
            return None
        bonds.add(b); dep[p] = dep.get(p, 0) + 1; p = q
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
# entries as monomial counts: (i, j) -> {(ns, nt, nr): count}
E = {}
for s in states:
    p, bonds, dep = walk(list(s))
    i = idx[s]
    def ext(p, last, seq, a, t, r):
        if len(seq) == k:
            j = idx[(tuple(s) + tuple(seq))[-m:]]
            dd = E.setdefault((i, j), {}); key = (a, t, r); dd[key] = dd.get(key, 0) + 1; return
        for d in range(4):
            q = (p[0] + D[d][0], p[1] + D[d][1]); b = (min(p, q), max(p, q))
            if b in bonds:
                continue
            if dep.get(p, 0) >= 1:
                na, nt_, nr = a, t, r + 1
            elif d == last:
                na, nt_, nr = a + 1, t, r
            else:
                na, nt_, nr = a, t + 1, r
            bonds.add(b); dep[p] = dep.get(p, 0) + 1
            ext(q, d, seq + [d], na, nt_, nr)
            bonds.discard(b); dep[p] -= 1
    ext(p, s[-1], [], 0, 0, 0)
ws, wt, wr = 1 / (3 * cs), 1 / (3 * ct), Fr(1, 4)
def arbq(f):
    return arb(fmpq(f.numerator, f.denominator))
Aws, Awt, Awr = arbq(ws), arbq(wt), arbq(wr)
n = len(states)
# float matrix for the Perron vector
rows, cols, vals = [], [], []
Earb = {}
for (i, j), dd in E.items():
    v = arb(0)
    for (a, t, r), c in dd.items():
        v += c * Aws ** a * Awt ** t * Awr ** r
    Earb[(i, j)] = v
    rows.append(i); cols.append(j); vals.append(float(v.mid()))
from scipy.sparse import csr_matrix
M = csr_matrix((vals, (rows, cols)), shape=(n, n))
x = np.ones(n)
for it in range(5000):
    y = M @ x; x = y / y.max()
x = np.maximum(x, 1e-300)
# rigorous Collatz-Wielandt with x taken exactly
xa = [arb(float(xi)) for xi in x]
num = [arb(0) for _ in range(n)]
for (i, j), v in Earb.items():
    num[i] += v * xa[j]
best = None
for i in range(n):
    r = num[i] / xa[i]
    ub = r.upper() if hasattr(r, 'upper') else r.mid() + r.rad()
    if best is None or ub > best:
        best = ub
rho = float(best)
print(f"m={m} k={k} cs={cs} ct={ct} windows={n}: rho(M_k) <= {rho:.8f}, growth <= {rho ** (1 / k):.8f} (rigorous upper bound)")
