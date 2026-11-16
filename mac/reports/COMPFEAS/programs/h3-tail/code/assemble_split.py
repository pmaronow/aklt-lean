"""Certificate from split mode-A runs (tailmem5, classes of the first direction; row B = W + 2 N by symmetry,
   row C = W + N + S) and unsplit mode-B runs (tailmem4).  Sigma_{n<=22}: per n, the class sums of the exact DFS
   values (n <= L, per-trail optimal order) and of the DP values (L < n <= 22).
   Usage: python3 assemble_split.py hB hC prefix_A prefix_B   (files prefix_A_{B,C}_{1,2,3}.txt, prefix_B_{B,C}.txt)"""
import re
import sys


def rd(fn):
    E, D, tot, hdr = {}, {}, None, ''
    for l in open(fn):
        f = l.split()
        if not f:
            continue
        if f[0] == 'E':
            E[int(f[1])] = float(f[2])
        elif f[0] in ('D', 'F') and len(f) == 3:
            D[int(f[1])] = float(f[2])
        elif l.startswith('# TAIL'):
            tot = float(re.search(r'<= ([0-9.eE+-]+)', l).group(1))
            assert 'NOT RIGOROUS' not in l, fn
        elif l.startswith('# remainder'):
            hdr += l
        elif l.startswith('# tailmem'):
            hdr += l
    assert tot is not None, fn + ' incomplete'
    return E, D, tot, hdr


hB, hC = float(sys.argv[1]), float(sys.argv[2]); pa, pb = sys.argv[3], sys.argv[4]
classes = {'B': {2: 1, 1: 2}, 'C': {1: 1, 2: 1, 3: 1}}
worst = 0
for X, h in (('B', hB), ('C', hC)):
    S = 0.0; tA = 0.0
    for d0, mult in classes[X].items():
        E, D, tot, hdr = rd(f'{pa}_{X}_{d0}.txt')
        S += mult * (sum(v for n, v in E.items() if n <= 22) + sum(v for n, v in D.items() if n <= 22 and n not in E))
        tA += mult * (tot - sum(v for n, v in D.items() if n > 107))  # erratum: mode A valid for n <= 2P-5 = 107
    E, D, tB, hdr = rd(f'{pb}_{X}.txt')
    NEXB = int(re.search(r'NEX=(\d+)', hdr).group(1)); ATB = int(re.search(r' AT=(\d+)', hdr).group(1))
    assert ATB < 108
    gap = sum(D.get(n, 0.0) for n in range(108, NEXB + 1))
    r = (S + tA + tB + gap) / h
    worst = max(worst, r)
    print(f'row {X}: Sigma_n<=22 = {S:.6f}  tau(22,107] = {tA:.6f}  tau[108,inf) = {tB + gap:.6f}  -> ratio {r:.6f}')
    print('   ' + [l for l in hdr.splitlines() if 'remainder' in l][0])
print(f'CERTIFIED: rho(M_1) <= {worst:.6f}   (h = ({hB}, {hC}))')
