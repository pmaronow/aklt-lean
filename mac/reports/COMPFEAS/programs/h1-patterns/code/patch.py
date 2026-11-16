"""Local step patches (agent 57).  A step at v (first visit, measure unif) leaving along bond (v, v+out):
1/rho = E_next[I/J] >= inf over boundary data of Z_cur(m)/Z_next(m), where Z_cur / Z_next are the patch partition
functions with v uniform with all its remaining bonds / v diluted without the out bond, and the boundary data are
adversarial unit vectors m_k on every leg leaving the patch (slots).  Site kinds: 'u' unvisited, 'd' passed once,
'c' passed twice (decoupled constant), trail bonds deleted."""
import itertools, string
import numpy as np
from scipy.optimize import minimize
from spins import momtensor

DIRS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def nbrs(x):
    return [add(x, d) for d in DIRS]


def bkey(a, b):
    return (a, b) if a <= b else (b, a)


def pattern_from_trail(trail, out, radius=2, template=None):
    """trail = [v_0, ..., v_m = v] lattice sites (consecutive neighbours), v first visited at the end.
    Returns dict with sites, kinds_cur, kinds_next, bonds_cur, bonds_next, slots (list of site names)."""
    v = trail[-1]
    assert v not in trail[:-1], 'v must be a first visit'
    tb = set(bkey(trail[i], trail[i + 1]) for i in range(len(trail) - 1))
    assert len(tb) == len(trail) - 1, 'not a trail'
    passes = {}
    for i, s in enumerate(trail[:-1]):
        passes[s] = passes.get(s, 0) + 1
    if template is None:
        T = [(v[0] + i, v[1] + j) for i in range(-radius, radius + 1) for j in range(-radius, radius + 1) if abs(i) + abs(j) <= radius]
    else:
        T = [add(v, t) for t in template]
    Tset = set(T)
    kind = {x: 'ucc'[min(passes.get(x, 0), 2)] if passes.get(x, 0) != 1 else 'd' for x in T}
    kind = {x: ('u', 'd', 'c')[min(passes.get(x, 0), 2)] for x in T}
    kind[v] = 'u'
    live = [x for x in T if kind[x] != 'c']
    bonds = []
    for x in live:
        for y in nbrs(x):
            if y in Tset and kind[y] != 'c' and x < y and bkey(x, y) not in tb:
                bonds.append((x, y))
    slots = []
    for x in live:
        for y in nbrs(x):
            if y not in Tset and bkey(x, y) not in tb:
                slots.append(x)
    yout = add(v, out)
    assert bkey(v, yout) not in tb and yout in Tset and kind[yout] != 'c'
    kinds_next = dict((x, kind[x]) for x in live); kinds_next[v] = 'd'
    bonds_next = [b for b in bonds if b != bkey(v, yout)]
    return dict(v=v, sites=live, kinds_cur=dict((x, kind[x]) for x in live), kinds_next=kinds_next,
                bonds_cur=bonds, bonds_next=bonds_next, slots=slots, kind_all=kind)


class Network:
    """Z(m) for a patch with slot vectors m (K x 3); value and gradient (environment tensors)."""

    def __init__(self, sites, kinds, bonds, slots):
        self.sites = sites
        letters = iter(string.ascii_letters)
        bl = {b: next(letters) for b in bonds}
        self.legs = {x: [bl[b] for b in bonds if x in b] for x in sites}
        self.slot_of = {x: [k for k, s in enumerate(slots) if s == x] for x in sites}
        self.M = {x: momtensor(len(self.legs[x]) + len(self.slot_of[x]), kinds[x]) for x in sites}
        self.K = len(slots)
        subs = [''.join(self.legs[x]) for x in sites]
        dummy = [np.ones((4,) * len(self.legs[x])) for x in sites]
        self.expr = ','.join(subs) + '->'
        self.path = np.einsum_path(self.expr, *dummy, optimize='greedy')[0]
        self.env = {}
        for i, x in enumerate(sites):
            if self.slot_of[x]:
                e = ','.join(subs[:i] + subs[i + 1:]) + '->' + subs[i]
                ops = dummy[:i] + dummy[i + 1:]
                self.env[x] = (e, np.einsum_path(e, *ops, optimize='greedy')[0] if ops else None)

    def site_tensors(self, m):
        T = {}
        for x in self.sites:
            t = self.M[x]
            for k in self.slot_of[x]:
                t = np.tensordot(t, np.concatenate([[1.0], m[k]]), axes=([t.ndim - 1], [0]))
            T[x] = t
        return T

    def value(self, m):
        T = self.site_tensors(m)
        return float(np.einsum(self.expr, *[T[x] for x in self.sites], optimize=self.path))

    def value_grad(self, m):
        T = self.site_tensors(m)
        Z = float(np.einsum(self.expr, *[T[x] for x in self.sites], optimize=self.path))
        g = np.zeros((self.K, 3))
        for i, x in enumerate(self.sites):
            ks = self.slot_of[x]
            if not ks:
                continue
            e, p = self.env[x]
            ops = [T[y] for y in self.sites if y != x]
            Env = np.einsum(e, *ops, optimize=p) if ops else np.array(1.0)
            r = len(self.legs[x])
            for j, k in enumerate(ks):
                t = self.M[x]
                # contract slot legs in order; slot j gets (0, e_alpha)
                for jj, kk in enumerate(ks):
                    if jj == j:
                        continue
                for alpha in range(3):
                    t = self.M[x]
                    for jj, kk in enumerate(ks):
                        vec = np.zeros(4); 
                        if jj == j:
                            vec[alpha + 1] = 1.0
                        else:
                            vec[0] = 1.0; vec[1:] = m[kk]
                        t = np.tensordot(t, vec, axes=([r], [0])) if t.ndim > r else t
                    g[k, alpha] = float(np.tensordot(t, Env, axes=r)) if r else float(t * Env)
        return Z, g


class Ratio:
    def __init__(self, pat):
        self.pat = pat
        self.cur = Network(pat['sites'], pat['kinds_cur'], pat['bonds_cur'], pat['slots'])
        self.nxt = Network(pat['sites'], pat['kinds_next'], pat['bonds_next'], pat['slots'])
        self.K = len(pat['slots'])

    def f(self, m):
        return self.cur.value(m) / self.nxt.value(m)

    def fg_unconstrained(self, y):
        Y = y.reshape(-1, 3)
        nr = np.linalg.norm(Y, axis=1, keepdims=True)
        m = Y / nr
        a, ga = self.cur.value_grad(m)
        b, gb = self.nxt.value_grad(m)
        f = a / b
        gm = (ga * b - a * gb) / b ** 2
        gy = (gm - np.sum(gm * m, axis=1, keepdims=True) * m) / nr
        return f, gy.ravel()

    def minimize(self, restarts=10, seed=0, tol=1e-12):
        rng = np.random.default_rng(seed)
        best = (np.inf, None)
        vals = []
        for t in range(restarts):
            y0 = rng.normal(size=3 * self.K)
            r = minimize(self.fg_unconstrained, y0, jac=True, method='L-BFGS-B', options={'maxiter': 5000, 'ftol': tol, 'gtol': 1e-10})
            vals.append(r.fun)
            if r.fun < best[0]:
                Y = r.x.reshape(-1, 3)
                best = (r.fun, Y / np.linalg.norm(Y, axis=1, keepdims=True))
        return best, sorted(vals)


def pattern_custom(kinds, absent_bonds, out, v=(0, 0), radius=2, slot_legs=True):
    """kinds: dict site -> 'u'/'d'/'c'/'x' (x = site absent: all its bonds give factor 1) for template sites
    (default 'u'); absent_bonds: set of bonds (pairs) that are deleted (trail bonds).  Legs leaving the template
    are slots unless their bond is in absent_bonds."""
    T = [(v[0] + i, v[1] + j) for i in range(-radius, radius + 1) for j in range(-radius, radius + 1) if abs(i) + abs(j) <= radius]
    Tset = set(T)
    ab = set(bkey(*b) for b in absent_bonds)
    kind = {x: kinds.get(x, 'u') for x in T}
    kind[v] = 'u'
    live = [x for x in T if kind[x] in 'ud']
    bonds = [(x, y) for x in live for y in nbrs(x) if y in Tset and kind[y] in 'ud' and x < y and bkey(x, y) not in ab]
    slots = [x for x in live for y in nbrs(x) if y not in Tset and bkey(x, y) not in ab]
    yout = add(v, out)
    kinds_next = dict((x, kind[x]) for x in live); kinds_next[v] = 'd'
    return dict(v=v, sites=live, kinds_cur=dict((x, kind[x]) for x in live), kinds_next=kinds_next,
                bonds_cur=bonds, bonds_next=[b for b in bonds if b != bkey(v, yout)], slots=slots, kind_all=kind)
