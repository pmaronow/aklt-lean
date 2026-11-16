import numpy as np
from patch import pattern_custom, Ratio
v = (0, 0); s = (0, -1)
base_k = {s: 'd', (0, -2): 'd'}
base_ab = {(v, s), (s, (0, -2)), ((0, -2), (0, -3))}
for out in [(0, 1), (1, 0)]:
    pat = pattern_custom(base_k, base_ab, out)
    R = Ratio(pat)
    (val, m), vals = R.minimize(restarts=3, seed=5)
    rel = [k for k, x in enumerate(pat['slots']) if x != (0, -2)]
    M = m[rel]
    sv = np.linalg.svd(M, compute_uv=False)
    print(out, round(val, 6), 'singular values of slot matrix', np.round(sv, 4))
