"""Fully self-contained variant of the certificate: own exact straights-first values for n <= L (directed rounding)
   and own DP over-count for L < n <= 22 (no use of agent 59's data).  Usage: python3 selfcontained.py hB hC A_B B_B A_C B_C"""
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
            assert 'NOT RIGOROUS' not in l
        elif l.startswith('# tailmem'):
            hdr = l
    return E, D, tot, hdr


hB, hC = float(sys.argv[1]), float(sys.argv[2])
worst = 0
for X, h, fa, fb in (('B', hB, sys.argv[3], sys.argv[4]), ('C', hC, sys.argv[5], sys.argv[6])):
    E, D, tA, ha = rd(fa)
    _, DB, tB, hb = rd(fb)
    TA = int(re.search(r' T=(\d+)', ha).group(1)); NEXB = int(re.search(r'NEX=(\d+)', hb).group(1))
    S = sum(v for n, v in E.items() if n <= 22) + sum(v for n, v in D.items() if n <= 22 and n not in E)
    # erratum (NOTES Entry 16): mode A valid for n <= 2P-5; n in (2P-5, NEX_B] from mode B per-n values
    Kd = int(re.search(r' K=(\d+)', ha).group(1)); P = 2 * Kd if 'diagonal' in ha else Kd; cut = 2 * P - 5
    tA -= sum(v for n, v in D.items() if n > cut)
    gap = sum(DB.get(n, 0.0) for n in range(cut + 1, NEXB + 1))
    r = (S + tA + tB + gap) / h
    worst = max(worst, r)
    print(f'{X}: own n<=22 {S:.6f}  tail A {tA:.6f}  tail B {tB + gap:.6f}  ratio {r:.6f}')
print(f'SELF-CONTAINED: rho(M_1) <= {worst:.6f}')
