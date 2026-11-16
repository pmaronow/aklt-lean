"""Exact (rational) evaluation of the weighted trail sums from the type histogram (agent 57).
Usage: trail_exact.py hist.txt c0 cs ct   (c's as decimal strings, converted exactly to rationals).
S_n = sum count * w0 * ws^ns * wt^nt * (1/5)^nr * (1/4)^nrx,  w = 1/(3c).  Prints S_n and the certified decay
bound q_n = (K S_n)^(1/n), K = max(ws, wt, 1/5, 1/4)/w0."""
import sys
from fractions import Fraction as Fr
hist, c0, cs, ct = sys.argv[1], Fr(sys.argv[2]), Fr(sys.argv[3]), Fr(sys.argv[4])
w0, ws, wt, wr, wrx = 1 / (3 * c0), 1 / (3 * cs), 1 / (3 * ct), Fr(1, 5), Fr(1, 4)
K = max(ws, wt, wr, wrx) / w0
S = {}
for line in open(hist):
    n, a, t, r, rx, cnt = map(int, line.split())
    S[n] = S.get(n, 0) + cnt * w0 * ws ** a * wt ** t * wr ** r * wrx ** rx
for n in sorted(S):
    KS = K * S[n]
    print(n, f"S_n={float(S[n]):.10f}", f"K*S_n={float(KS):.6f}", f"q_bound={float(KS) ** (1 / n):.6f}" if KS < 1 else "")
print('K =', float(K), '(exact', K, ')')
