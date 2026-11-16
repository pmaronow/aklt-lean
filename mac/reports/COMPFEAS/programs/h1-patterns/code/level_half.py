"""'Level 1/2' relaxation (agent 57): condition on the four corner spins (shared unit vectors), tips integrated
(mean in B(3/5)); given these, e, N, W are independent, ratio = I(mu)/J(mu)."""
import numpy as np
from scipy.optimize import minimize
def mean3(u1, u2, u3):
    Z = 1 + (u1 @ u2 + u1 @ u3 + u2 @ u3) / 3
    m = (u1 + u2 + u3) / 3 + (u1 * (u2 @ u3) + u2 * (u1 @ u3) + u3 * (u1 @ u2)) / 15
    return m / Z
def unit(y):
    return y / np.linalg.norm(y)
def ball(y, r):
    return r * y / np.sqrt(1 + y @ y)   # maps R^3 onto the open ball of radius r
def ratio(z, out):
    Y = z.reshape(-1, 3)
    c1, c2, c3, c4 = [unit(Y[i]) for i in range(4)]
    te, tN, tW = [ball(Y[4 + i], 0.6) for i in range(3)]
    me, mN, mW = mean3(te, c1, c3), mean3(tN, c1, c2), mean3(tW, c2, c4)
    I = 1 + (me @ mN + me @ mW + mN @ mW) / 3
    J = 1 + (me @ mW) / 5 if out == 'N' else 1 + (mN @ mW) / 5
    return I / J
rng = np.random.default_rng(0)
for out in ['N', 'E']:
    best = 9
    for t in range(40):
        r = minimize(ratio, rng.normal(size=21) * 3, args=(out,), method='BFGS')
        best = min(best, r.fun)
    print('out', out, 'level-1/2 min', round(best, 5))
