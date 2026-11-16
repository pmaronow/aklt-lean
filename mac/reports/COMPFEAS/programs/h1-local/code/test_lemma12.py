"""Numerical test of Lemma 1.2: for |beta_j| <= r_j, the mean of n under lambda(dn) prod_j (1 + beta_j.n) has norm
<= rho_lambda(r), with equality for parallel fields of full length.  Random radii and directions, plus a local
maximisation from random starts."""
import numpy as np
rng = np.random.default_rng(5)


def mean(b, kind):
    b1, b2, b3 = b
    Z = 1 + (b1 @ b2 + b1 @ b3 + b2 @ b3) / 3
    V = (b1 + b2 + b3) / 3 + (b1 * (b2 @ b3) + b2 * (b1 @ b3) + b3 * (b1 @ b2)) / 15
    if kind == 'd':
        Z = 0.6 * Z + 0.4; V = 0.6 * V
    return np.linalg.norm(V) / Z


def rho(r, kind):
    r1, r2, r3 = r
    num = (r1 + r2 + r3) / 3 + r1 * r2 * r3 / 5
    den = 1 + (r1 * r2 + r1 * r3 + r2 * r3) / 3 + (2 / 3 if kind == 'd' else 0)
    return num / den


worst = -1.0
for trial in range(300000):
    r = rng.uniform(0, 1, 3) * (rng.uniform(size=3) < 0.85)
    u = rng.normal(size=(3, 3)); u /= np.linalg.norm(u, axis=1, keepdims=True)
    if trial % 3 == 0:                      # near-parallel configurations
        u = u[0] + 0.2 * rng.normal(size=(3, 3)); u /= np.linalg.norm(u, axis=1, keepdims=True)
    b = u * (r * rng.uniform(0.5, 1, 3) ** (trial % 2))[:, None]
    for kind in 'ud':
        worst = max(worst, mean(b, kind) - rho(r, kind))
print('300,000 random cases x 2 measures: max(|mean| - rho) =', worst, '(must be <= 0)')
eq = max(abs(mean(np.outer(r, [0, 0, 1.0]), k) - rho(r, k)) for r in rng.uniform(0, 1, (1000, 3)) for k in 'ud')
print('parallel fields: max |mean - rho| =', eq)
