import numpy as np
from patch import *
for name, trail, out in [('straight', [(0, -3), (0, -2), (0, -1), (0, 0)], (0, 1)), ('turnE', [(0, -3), (0, -2), (0, -1), (0, 0)], (1, 0))]:
    pat = pattern_from_trail(trail, out)
    R = Ratio(pat)
    best, vals = R.minimize(restarts=2)
    m = best[1]
    ax = m[0]
    print(name, best[0])
    for k, s in enumerate(pat['slots']):
        print('  slot at', s, 'dot with slot0 %.6f' % (m[k] @ ax))
