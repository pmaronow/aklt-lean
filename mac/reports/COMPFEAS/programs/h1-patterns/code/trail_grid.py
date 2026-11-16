import sys
from fractions import Fraction as Fr
hist = sys.argv[1]
H = [tuple(map(int, l.split())) for l in open(hist)]
nmax = max(h[0] for h in H)
def S(c0, cs, ct):
    w0, ws, wt = 1 / (3 * c0), 1 / (3 * cs), 1 / (3 * ct)
    out = [0.0] * (nmax + 1)
    for n, a, t, r, rx, cnt in H:
        out[n] += cnt * w0 * ws ** a * wt ** t * 0.2 ** r * 0.25 ** rx
    K = max(ws, wt, 0.25) / w0
    return out, K
c0 = 0.98543
print('c_s \\ c_t  -> first n with K*S_n<1 (n<=%d), q bound' % nmax)
for cs in [1.0, 0.98, 0.96, 0.94]:
    row = []
    for ct in [0.96, 0.95, 0.94, 0.93, 0.92]:
        s, K = S(c0, cs, ct)
        ns = [n for n in range(1, nmax + 1) if K * s[n] < 1]
        row.append(f"{ct}:{ns[0] if ns else '-'}/{(K*s[nmax])**(1/nmax):.4f}" if ns else f"{ct}:-/{s[nmax]:.3f}")
    print(cs, ' '.join(row))
