"""Exact re-assembly of the (H3') certificate from the per-n output of tailmem5 (split mode A) and tailmem4 (mode B).
Every printed number of those programs is rounded UPWARD (glibc printf honours FE_UPWARD; checked), so the decimal
strings are upper bounds; here they are summed exactly as rationals (fractions.Fraction), and the final quotient is
rounded up. Optionally the exact part n <= 20 is replaced by the values of exact75.c (column 'optimal_h').
Usage: python3 assemble75.py DIR prefixA prefixB hC [exactdir exactsuffix]
  files DIR/prefixA_{B,C}_{d}.txt (row B: d = 1 (N, multiplicity 2), 2 (W); row C: d = 1, 2, 3) and DIR/prefixB_{B,C}.txt"""
import sys
import re
from fractions import Fraction as Fr
import math

D, pa, pb, hCs = sys.argv[1:5]
exdir = sys.argv[5] if len(sys.argv) > 5 else None
exsuf = sys.argv[6] if len(sys.argv) > 6 else None
hC = Fr(float(hCs))           # the double actually used by the C code (atof)
hB = Fr(1)


def rd(fn):
    E, Dv, tail, rem, hdr, lam = {}, {}, None, None, '', None
    for l in open(fn):
        f = l.split()
        if not f:
            continue
        if f[0] == 'E' and len(f) == 3:
            E[int(f[1])] = Fr(f[2])
        elif f[0] in ('D', 'F') and len(f) == 3:
            Dv[int(f[1])] = Fr(f[2])
        elif l.startswith('# TAIL'):
            tail = Fr(re.search(r'<= ([0-9.eE+-]+)', l).group(1))
            assert 'NOT RIGOROUS' not in l
        elif l.startswith('# remainder'):
            assert 'check=OK' in l, fn
            rem = Fr(re.search(r'remainder<=([0-9.eE+-]+)', l).group(1))
            lam = float(re.search(r'lcheck=([0-9.]+)', l).group(1))
            assert lam < 1 and rem >= 0, 'remainder lemma needs lambda < 1'
        elif l.startswith('# tailmem'):
            hdr = l
    assert tail is not None, fn + ' incomplete'
    return E, Dv, tail, rem, hdr, lam


def rex(fn):
    r = {}
    for l in open(fn):
        if l.startswith('#') or not l.strip():
            continue
        f = l.split()
        r[int(f[0])] = Fr(f[6])
    return r


classes = {'B': {1: 2, 2: 1}, 'C': {1: 1, 2: 1, 3: 1}}
worst = Fr(0)
for X, h in (('B', hB), ('C', hC)):
    S_ex, S_22, tA = Fr(0), Fr(0), Fr(0)
    for d, mult in classes[X].items():
        E, Dv, tot, _, hdr, _ = rd(f'{D}/{pa}_{X}_{d}.txt')
        assert ' AT=109 ' in hdr and 'NEX=22' in hdr and 'L=20' in hdr and f'D0={d}' in hdr, hdr
        if exdir:
            ex = rex(f'{exdir}/e{X}{d}_{exsuf}.txt')
            assert sorted(n for n in ex if n <= 20) == sorted(E)
            S_ex += mult * sum(v for n, v in ex.items() if n <= 20)
        else:
            S_ex += mult * sum(E.values())
        assert max(E) <= 20 and 21 not in Dv
        S_22 += mult * Dv[22]
        tA += mult * sum(v for n, v in Dv.items() if 22 < n <= 107)
        # consistency with the C-side sum (which also contains n = 108, 109)
        assert abs(sum(v for n, v in Dv.items() if n > 22) - tot) <= Fr(1, 10**9) * tot
    E, Dv, tot, rem, hdr, lam = rd(f'{D}/{pb}_{X}.txt')
    assert ' AT=53 ' in hdr and 'NEX=109' in hdr and 'T=260' in hdr, hdr
    tB = sum(v for n, v in Dv.items() if n >= 108) + rem
    assert all(n <= 260 for n in Dv)
    num = S_ex + S_22 + tA + tB
    r = num / h
    worst = max(worst, r)
    print(f'row {X}: Sigma_(n<=20) = {float(S_ex):.9f}  D_22 = {float(S_22):.9f}  tau(22,107] = {float(tA):.9f}  '
          f'tau[108,inf) = {float(tB):.9f} (remainder {float(rem):.6e}, lambda {lam})  ratio = {float(r):.9f}')
up = math.ceil(worst * 10**6) / 10**6
print(f'CERTIFIED (exact rational sum of upward-rounded decimals): rho(M_1) <= {float(worst):.9f} <= {up:.6f}')
