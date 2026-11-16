"""Assemble the certified bound rho(M_1) <= max_X [(M_{<=22} h)_X + tau_X] / h_X  (Collatz-Wielandt).
   M_{<=22}: per n and row, the smaller of (i) agent 59's sorted-order data (k2_{X}_22_T_alm.txt; exact enumeration,
   float sums; inflated by a relative 1e-8 for summation error) and (ii) our own exact straights-first DFS values
   (E lines of tailmem2 output; directed rounding).  tau_X: mode-A sum (D lines, 22 < n <= 2K-3) + mode-B total
   (F/D lines n >= 2K-2 plus the remainder).  Usage: python3 assemble.py hB hC fileA_B fileB_B fileA_C fileB_C"""
import sys
import re

D59 = '/home/user/otis-claude/research/aklt-gap/agents/59-swm-certificate/out/'


def load59(X, hB, hC):
    out = {}
    for line in open(D59 + f'k2_{X}_22_T_alm.txt'):
        if line.startswith('#'):
            continue
        f = line.split()
        out[int(f[0])] = (float(f[3]) * hB + float(f[4]) * hC) * (1 + 1e-8)
    return out


def parse(fn):
    E, Dv, tailA, total = {}, {}, None, None
    rem = None
    hdr = {}
    for line in open(fn):
        f = line.split()
        if not f:
            continue
        if line.startswith('# tailmem'):
            hdr = dict(kv.split('=', 1) for kv in f if '=' in kv)
            hdr['_line'] = line
        if f[0] == 'E':
            E[int(f[1])] = float(f[2])
        elif f[0] in ('D', 'F'):
            Dv[int(f[1])] = float(f[2])
        elif line.startswith('# TAIL'):
            m = re.search(r'<= ([0-9.eE+-]+)', line)
            total = float(m.group(1))
            if 'NOT RIGOROUS' in line:
                raise SystemExit(f'{fn}: remainder check failed')
        elif line.startswith('# remainder'):
            rem = line.strip()
    return E, Dv, total, rem, hdr


def main():
    hB, hC = float(sys.argv[1]), float(sys.argv[2])
    files = {'B': sys.argv[3:5], 'C': sys.argv[5:7]}
    h = {'B': hB, 'C': hC}
    worst = 0
    for X in 'BC':
        m59 = load59(X, hB, hC)
        EA, DA, tA, _, hA = parse(files[X][0])
        EB, DB, tB, rem, hB_ = parse(files[X][1])
        # gap between mode A (n <= T_A) and mode B (n > NEX_B): add mode-B per-n values (valid for n >= 2P-2)
        TA, NEXB, Kd, ATB = int(hA['T']), int(hB_['NEX']), int(hB_['K']), int(hB_['AT'])
        P = 2 * Kd if 'diagonal' in hB_['_line'] else Kd
        # erratum (NOTES Entry 16): mode A is valid only for n <= 2P-5 (pair death at torus-c, split sites);
        # the per-n values of mode B are valid for every n > AT_B.
        cutA = 2 * P - 5
        tA -= sum(v for n, v in DA.items() if n > cutA)
        gap = [n for n in range(cutA + 1, NEXB + 1)]
        assert all(n > ATB for n in gap), 'gap not covered validly'
        tB += sum(DB.get(n, 0.0) for n in gap)
        S = 0
        for n in sorted(set(m59) | set(EA)):
            if n > 22:
                continue
            cands = [v for v in (m59.get(n), EA.get(n)) if v is not None]
            if n not in EA and n in DA:
                cands.append(DA[n])
            S += min(cands)
        tot = (S + tA + tB) / h[X]
        print(f'row {X}: sum_n<=22 = {S:.6f}, tail (22,2K-3] = {tA:.6f}, tail >= 2K-2 = {tB:.6f}  ->  ({S:.4f}+{tA + tB:.4f})/h = {tot:.6f}')
        print(f'   {rem}')
        worst = max(worst, tot)
    print(f'CERTIFIED (given the inputs): rho(M_1) <= {worst:.6f}')


if __name__ == '__main__':
    main()
