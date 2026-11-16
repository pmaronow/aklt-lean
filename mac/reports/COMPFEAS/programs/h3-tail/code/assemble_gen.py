"""General certificate assembly (agent 62, Entries 16, 20, 21).
Row X: Sigma_{n<=22} (exact DFS values n <= L and DP values L < n <= 22, summed over the split classes with their
multiplicities) + mode-A tail (22, cut] (classes; per-n values above cut removed) + mode-B per-n values (cut, NEX_B]
+ mode-B TAIL (n > NEX_B, incl. remainder).  cut = 2P-5 for the one-step split / unsplit, 2P-7 for the two-step split.
Usage: python3 assemble_gen.py hB hC split prefixA prefixB
  split = 1 : files prefixA_{X}_{D0}.txt            (B: D0 = 2 x1, 1 x2;  C: D0 = 1, 2, 3)
  split = 2 : files prefixA_{X}_{D0}{D1}.txt        (B: 22 x1, 21 x2, 11 x2, 12 x2, 10 x2;  C: all 9 classes)
  mode B: prefixB_{X}.txt"""
import re
import sys

CLASSES = {
    1: {'B': {'2': 1, '1': 2}, 'C': {'1': 1, '2': 1, '3': 1}},
    2: {'B': {'22': 1, '21': 2, '11': 2, '12': 2, '10': 2},
        'C': {'11': 1, '10': 1, '12': 1, '22': 1, '21': 1, '23': 1, '33': 1, '30': 1, '32': 1}},
}


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
        elif l.startswith('# remainder') or l.startswith('# tailmem'):
            hdr += l
    assert tot is not None, fn + ' incomplete'
    return E, D, tot, hdr


def main():
    hB, hC = float(sys.argv[1]), float(sys.argv[2]); split = int(sys.argv[3]); pa, pb = sys.argv[4], sys.argv[5]
    worst = 0
    for X, h in (('B', hB), ('C', hC)):
        S = tA = 0.0; cutA = None; hdrs = ''
        for cl, mult in CLASSES[split][X].items():
            E, D, tot, hdr = rd(f'{pa}_{X}_{cl}.txt'); hdrs += hdr
            K = int(re.search(r' K=(\d+)', hdr).group(1)); P = 2 * K
            assert 'diagonal' in hdr or 'tailmem3' in hdr or 'tailmem' in hdr
            T = int(re.search(r' T=(\d+)', hdr).group(1)); assert T == 2 * P - 3
            cutA = 2 * P - 5 if split == 1 else 2 * P - 7
            S += mult * (sum(v for n, v in E.items() if n <= 22) + sum(v for n, v in D.items() if n <= 22 and n not in E))
            tA += mult * (tot - sum(v for n, v in D.items() if n > cutA))
        E, D, tB, hdr = rd(f'{pb}_{X}.txt')
        NEXB = int(re.search(r'NEX=(\d+)', hdr).group(1)); ATB = int(re.search(r' AT=(\d+)', hdr).group(1))
        assert ATB < cutA + 1
        gap = sum(D.get(n, 0.0) for n in range(cutA + 1, NEXB + 1))
        r = (S + tA + tB + gap) / h
        worst = max(worst, r)
        rem = [l for l in hdr.splitlines() if 'remainder' in l][0]
        print(f'row {X}: Sigma_n<=22 = {S:.6f}  tau(22,{cutA}] = {tA:.6f}  tau[{cutA + 1},inf) = {tB + gap:.6f}  -> ratio {r:.6f}')
        print('   ' + rem)
    print(f'CERTIFIED: rho(M_1) <= {worst:.6f}   (h = ({hB}, {hC}), split {split})')


if __name__ == '__main__':
    main()
