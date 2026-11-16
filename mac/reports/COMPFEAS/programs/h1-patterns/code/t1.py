import numpy as np, time
from patch import *
# generic straight step: trail (0,-3),(0,-2),(0,-1),(0,0); out = N
for name, trail, out in [('straight', [(0, -3), (0, -2), (0, -1), (0, 0)], (0, 1)), ('turnE', [(0, -3), (0, -2), (0, -1), (0, 0)], (1, 0))]:
    pat = pattern_from_trail(trail, out)
    R = Ratio(pat)
    print(name, 'sites', len(pat['sites']), 'slots', R.K)
    m = np.random.default_rng(1).normal(size=(R.K, 3)); m /= np.linalg.norm(m, axis=1, keepdims=True)
    # gradient check
    y = m.ravel().copy()
    f, g = R.fg_unconstrained(y)
    eps = 1e-6; gn = np.zeros_like(y)
    for i in range(len(y)):
        yp = y.copy(); yp[i] += eps; ym = y.copy(); ym[i] -= eps
        gn[i] = (R.fg_unconstrained(yp)[0] - R.fg_unconstrained(ym)[0]) / (2 * eps)
    print(' grad check', np.max(np.abs(g - gn)))
    t = time.time(); best, vals = R.minimize(restarts=8)
    print(' min', best[0], 'vals', np.round(vals, 6), 'time', round(time.time() - t, 1), flush=True)
