"""Cross-check patch.Network against spins.contract and against the 12-point icosahedral design (agent 57)."""
import numpy as np, itertools
from patch import pattern_custom, Network
from spins import contract
v = (0, 0); s = (0, -1)
pat = pattern_custom({s: 'd', (0, -2): 'd', (1, 1): 'd'}, {(v, s), (s, (0, -2)), ((0, -2), (0, -3)), ((1, 1), (1, 2))}, (1, 0))
rng = np.random.default_rng(1)
m = rng.normal(size=(len(pat['slots']), 3)); m /= np.linalg.norm(m, axis=1, keepdims=True)
for which in ['cur', 'next']:
    kinds = pat['kinds_' + which]; bonds = pat['bonds_' + which]
    N = Network(pat['sites'], kinds, bonds, pat['slots'])
    ext = {}
    for k, x in enumerate(pat['slots']):
        ext.setdefault(x, []).append(np.concatenate([[1.0], m[k]]))
    a = N.value(m); b = contract(kinds, [(x, y, 1.0) for x, y in bonds], ext)
    print(which, a, b, a - b)
# icosahedral design check of a single-site moment: E[prod (1+n.u_i)] for 4 random u's
phi = (1 + 5 ** 0.5) / 2
ico = np.array([[0, 1, phi], [0, 1, -phi], [0, -1, phi], [0, -1, -phi], [1, phi, 0], [1, -phi, 0], [-1, phi, 0], [-1, -phi, 0],
                [phi, 0, 1], [phi, 0, -1], [-phi, 0, 1], [-phi, 0, -1]], float); ico /= np.linalg.norm(ico, axis=1, keepdims=True)
u = rng.normal(size=(4, 3))
design = np.mean([np.prod([1 + p @ ui for ui in u]) for p in ico])
from spins import momtensor
T = momtensor(4, 'u')
for ui in u:
    T = np.tensordot(T, np.concatenate([[1.0], ui]), axes=([T.ndim - 1], [0]))
print('degree-4 single site: design', design, 'moments', float(T), 'diff', design - float(T))
