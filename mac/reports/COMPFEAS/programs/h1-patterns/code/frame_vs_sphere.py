"""Is the adversarial infimum attained at frame points? (agent 57).  Generic turning pattern: continuous minimum vs
the best value found by exhaustive coordinate descent with every slot restricted to the 12 icosahedron vertices
(and to the 12 + 20 icosahedron + dodecahedron directions), many random starts, each frame rotated randomly."""
import numpy as np
from patch import pattern_custom, Ratio
v = (0, 0); s = (0, -1)
pat = pattern_custom({s: 'd', (0, -2): 'd'}, {(v, s), (s, (0, -2)), ((0, -2), (0, -3))}, (1, 0))
R = Ratio(pat)
(val, mstar), _ = R.minimize(restarts=3, seed=0)
print('continuous min', val)
phi = (1 + 5 ** 0.5) / 2
ico = np.array([[0, 1, phi], [0, 1, -phi], [0, -1, phi], [0, -1, -phi], [1, phi, 0], [1, -phi, 0], [-1, phi, 0], [-1, -phi, 0],
                [phi, 0, 1], [phi, 0, -1], [-phi, 0, 1], [-phi, 0, -1]], float)
ico /= np.linalg.norm(ico, axis=1, keepdims=True)
dod = np.array([[a, b, c] for a in (1, -1) for b in (1, -1) for c in (1, -1)] +
               [[0, a / phi, b * phi] for a in (1, -1) for b in (1, -1)] + [[a / phi, b * phi, 0] for a in (1, -1) for b in (1, -1)] +
               [[a * phi, 0, b / phi] for a in (1, -1) for b in (1, -1)], float)
dod /= np.linalg.norm(dod, axis=1, keepdims=True)
rng = np.random.default_rng(3)
def rot():
    q = rng.normal(size=4); q /= np.linalg.norm(q); a, b, c, d = q
    return np.array([[a*a+b*b-c*c-d*d, 2*(b*c-a*d), 2*(b*d+a*c)], [2*(b*c+a*d), a*a-b*b+c*c-d*d, 2*(c*d-a*b)], [2*(b*d-a*c), 2*(c*d+a*b), a*a-b*b-c*c+d*d]])
for name, F0 in [('icosahedron (12)', ico), ('ico+dodeca (32)', np.vstack([ico, dod]))]:
    best = 9
    for t in range(6):
        F = F0 @ rot().T
        m = F[rng.integers(len(F), size=R.K)]
        cur = R.f(m)
        improved = True
        while improved:
            improved = False
            for k in range(R.K):
                vals = []
                for p in F:
                    mm = m.copy(); mm[k] = p; vals.append(R.f(mm))
                j = int(np.argmin(vals))
                if vals[j] < cur - 1e-12:
                    cur = vals[j]; m[k] = F[j]; improved = True
        best = min(best, cur)
    print(name, 'best frame-restricted value (coordinate descent, 6 random frames/starts):', round(best, 6))
