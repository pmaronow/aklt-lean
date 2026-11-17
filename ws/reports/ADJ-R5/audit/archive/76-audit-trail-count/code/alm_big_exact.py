"""alm_big_exact.py (agent 76): exact rational evaluation of the certificate produced by almbig.rs.
For each parameter block "P cs ct rnum rden": lam = max_O sum_{(a,t,r)} S[O][a,t,r] ws^a wt^t rhat^r / hnum[O]
exactly (ws = 1/(3 c_s), wt = 1/(3 c_t), c's exact decimal rationals), q_up with q_up^k >= lam checked exactly.
Usage: alm_big_exact.py file"""
import sys
from fractions import Fraction as F
import mpmath
mpmath.mp.dps = 40


def finish(hdr, P, hnum, S):
    m, k = hdr
    cs, ct, rn, rd = P
    ws, wt, wr = 1 / (3 * F(cs)), 1 / (3 * F(ct)), F(int(rn), int(rd))
    lam, arg = F(0), None
    for o, d in S.items():
        v = sum((F(s) * ws ** a * wt ** t * wr ** r for (a, t, r), s in d.items()), F(0)) / hnum[o]
        if v > lam:
            lam, arg = v, o
    qf = mpmath.root(mpmath.mpf(lam.numerator) / lam.denominator, k)
    q_up = F(int(mpmath.ceil(qf * 10 ** 8)), 10 ** 8)
    while q_up ** k < lam:
        q_up += F(1, 10 ** 8)
    lam_up = F(int(mpmath.ceil(mpmath.mpf(lam.numerator) / lam.denominator * 10 ** 10)), 10 ** 10)
    assert lam_up >= lam
    print(f"m={m} k={k} c_s={cs} c_t={ct} rhat={rn}/{rd}: lam <= {float(lam_up):.10f}, q <= {float(q_up):.8f} "
          f"(exact), h_max/h_min = {max(hnum.values()) / min(hnum.values()):.4g}")


hdr, P, hnum, S = None, None, {}, {}
for line in open(sys.argv[1]):
    p = line.split()
    if p[0] == 'H':
        hdr = (int(p[1]), int(p[2]))
        print(f"m={p[1]} k={p[2]} windows={p[3]} orbits={p[4]} sum|O|*continuations={p[5]}")
    elif p[0] == 'P':
        if P is not None:
            finish(hdr, P, hnum, S)
        P, hnum, S = p[1:], {}, {}
    elif p[0] == 'h':
        hnum[int(p[1])] = int(p[2])
    elif p[0] == 'S':
        o, a, t, r, s = map(int, p[1:])
        S.setdefault(o, {})[(a, t, r)] = s
if P is not None:
    finish(hdr, P, hnum, S)
