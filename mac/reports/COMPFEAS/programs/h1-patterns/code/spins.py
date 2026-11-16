"""Core exact machinery (agent 57).  Spin systems on graphs with site measures
   'u' = uniform on S^2, 'd' = diluted (3/5) uniform + (2/5) delta_0, 'c' = (3/5) delta_0,
bond factors (1 + s n.n'), pins (1 + p.n), slots (1 + m.n).  Exact evaluation by contraction in the
colour basis: 1 + s n.n' = sum_c kap_c M_c(n) M_c(n'), M = (1, n), kap = (1, s, s, s); a site tensor is
lambda[prod_i M_{c_i}(n)] (moments of the site measure).  All integrands have degree <= 5 per site."""
import itertools, string
import numpy as np


def dfact(n):
    r = 1
    while n > 1:
        r *= n; n -= 2
    return r


def mom_unif(cols):
    e = [0, 0, 0]
    for c in cols:
        if c:
            e[c - 1] += 1
    if any(k % 2 for k in e):
        return 0.0
    return dfact(e[0] - 1) * dfact(e[1] - 1) * dfact(e[2] - 1) / dfact(sum(e) + 1)


_MT = {}
def momtensor(k, kind='u'):
    key = (k, kind)
    if key not in _MT:
        T = np.zeros((4,) * k)
        for c in itertools.product(range(4), repeat=k):
            z = 1.0 if all(x == 0 for x in c) else 0.0
            if kind == 'u':
                T[c] = mom_unif(c)
            elif kind == 'd':
                T[c] = 0.6 * mom_unif(c) + 0.4 * z
            elif kind == 'c':
                T[c] = 0.6 * z
            else:
                raise ValueError(kind)
        _MT[key] = T
    return _MT[key]


def contract(sites, bonds, ext, insert=None):
    """sites: dict name -> kind; bonds: list of (x, y, s); ext: dict name -> list of 4-vectors (1, m) (slots/pins,
    already including strength); insert: optional (name, a) -> insert a.n at that site.  Returns the integral."""
    letters = iter(string.ascii_letters)
    bl = [next(letters) for _ in bonds]
    ops, subs = [], []
    for x, kind in sites.items():
        legs = [bl[i] for i, b in enumerate(bonds) if x in b[:2]]
        vecs = list(ext.get(x, []))
        if insert is not None and insert[0] == x:
            vecs.append(np.concatenate([[0.0], insert[1]]))
        T = momtensor(len(legs) + len(vecs), kind)
        for vv in vecs:
            T = np.tensordot(T, vv, axes=([T.ndim - 1], [0]))
        ops.append(T); subs.append(''.join(legs))
    for i, (x, y, s) in enumerate(bonds):
        ops.append(np.array([1.0, s, s, s])); subs.append(bl[i])
    return float(np.einsum(','.join(subs) + '->', *ops, optimize='greedy'))
