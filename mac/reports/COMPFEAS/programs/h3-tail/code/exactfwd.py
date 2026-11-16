"""Exact forward-order kernel per n from agent 59's symbolic data (k3_{B,C}_22.txt), contracted with h, theta = 1.
   Usage: python3 exactfwd.py cs ct a b hB hC"""
import sys
import numpy as np
D = '/home/user/otis-claude/research/aklt-gap/agents/59-swm-certificate/out/'
cs, ct, a, b, hB, hC = map(float, sys.argv[1:7])
xs, xt = 1 / min(cs, 1), 1 / min(ct, 1)
for X in 'BC':
    A = np.loadtxt(D + f'k3_{X}_22.txt', comments='#')
    n, st, NS, NT, q, Y, sh, val = (A[:, i] for i in range(8))
    base = val * np.where(st == 0, xs, xt) * xs ** NS * xt ** NT * np.where(q == 0, a, b) * np.where(Y == 0, hB, hC)
    MB = (val * np.where(st == 0, xs, xt) * xs ** NS * xt ** NT * np.where(q == 0, a, b))
    tot = 0
    for nn in np.unique(n):
        v = base[n == nn].sum(); tot += v
        print(X, int(nn), f"{v:.12e}")
    print(X, 'sum', tot, 'MB', MB[Y == 0].sum(), 'MC', MB[Y == 1].sum())
