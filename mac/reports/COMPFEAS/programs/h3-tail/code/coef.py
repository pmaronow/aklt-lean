"""Rigorous type-dependent coefficients of Lemma 3.3' using (H1) for the step itself (agent 69 NOTES Entry 14;
re-derived in agent 62 NOTES Entry 19).  Ball arithmetic (python-flint arb); every printed number is an UPPER bound,
rounded up in the last printed digit.

For a first-visit passage of type tau in {straight, turn} with constant c = c_tau:
  lambda = a r_fg + b (r_fo + r_go),  a = 1/(3 L_I) - 1/(5 L_J),  b = 1/(3 L_I),
  L_I = L(x_I, y_I), L_J = L(x_J, y_J), L = logarithmic mean,  x = pinned (tau), y = free expectations,
  x_J = 1 + P/5 (P = E^tau[P_fg] in [-0.36, 0.36]),  x_I >= max(Imin(P), c x_J),  Imin(p) = 1 + (p - 0.6 sqrt(0.72+2p))/3,
  y_J = 1 + t/5 (t = E^0[P_fg] in [0, 0.36]),  y_I >= 1 + t/3.
  b_tau  <= 1/(3 L(max(0.82, 0.928 c), 1))                          (closed form)
  a_tau  <= sup_{P,t} [1/(3 L(X(P), 1 + t/3)) - 1/(5 L(1 + P/5, 1 + t/5))]  (interval branch and bound)
  b'_tau <= 1/(3 L(max(0.88, c), 1))   two-neighbour passage (one of f, g removed; then J = 1, I = 1 + P_go/3).
Usage: python3 coef.py cs ct"""
import sys
from flint import arb, ctx

ctx.prec = 80


def Llo(x, y):
    """lower bound of the logarithmic mean of x, y > 0 (arb inputs)"""
    d = x - y
    den = x.log() - y.log()
    if not den.contains(0):
        v = d / den
        return v.lower()
    return (x * y).sqrt().lower()  # L >= geometric mean


def Lhi(x, y):
    d = x - y
    den = x.log() - y.log()
    if not den.contains(0):
        return (d / den).upper()
    return ((x + y) / 2).upper()  # L <= arithmetic mean


def up(v, nd=6):
    """round an arb upper bound up to nd decimals (as a string)"""
    import math
    f = float(v.upper()) if isinstance(v, arb) else float(v)
    s = math.ceil(f * 10 ** nd + 1e-9) / 10 ** nd
    return s


def Imin_lo(P1, P2):
    """lower bound of Imin on [P1, P2] (Imin convex, minimal at p = -0.18)"""
    p = min(max(arb(-0.18), arb(P1)), arb(P2)) if False else None
    pc = -0.18 if P1 <= -0.18 <= P2 else (P1 if P1 > -0.18 else P2)
    pc = arb(pc)
    v = 1 + (pc - arb('0.6') * (arb('0.72') + 2 * pc).sqrt()) / 3
    return v.lower()


def F_upper(P1, P2, t1, t2, c):
    """upper bound of a on the box [P1,P2] x [t1,t2]"""
    X = max(Imin_lo(P1, P2), (c * (1 + arb(P1) / 5)).lower(), arb('0.82').lower())
    X = arb(X)
    first = arb(1) / (3 * arb(Llo(X, 1 + arb(t1) / 3)))
    second = arb(1) / (5 * arb(Lhi(1 + arb(P2) / 5, 1 + arb(t2) / 5)))
    return (first - second).upper()


def F_point(P, t, c):
    import math
    Im = 1 + (P - 0.6 * math.sqrt(max(0.72 + 2 * P, 0))) / 3
    X = max(Im, c * (1 + P / 5), 0.82)

    def L(x, y):
        return x if abs(x - y) < 1e-14 else (x - y) / math.log(x / y)
    return 1 / (3 * L(X, 1 + t / 3)) - 1 / (5 * L(1 + P / 5, 1 + t / 5))


def sup_a(c, N0=60, tol=2e-6):
    c = arb(c)
    cf = float(c.mid())
    boxes = []
    for i in range(N0):
        for j in range(N0):
            P1 = -0.36 + 0.72 * i / N0; P2 = -0.36 + 0.72 * (i + 1) / N0
            t1 = 0.36 * j / N0; t2 = 0.36 * (j + 1) / N0
            boxes.append((P1, P2, t1, t2))
    best = max(F_point(0.5 * (b[0] + b[1]), 0.5 * (b[2] + b[3]), cf) for b in boxes)
    for it in range(30):
        ub = [(float(F_upper(*b, c)), b) for b in boxes]
        top = max(u for u, _ in ub)
        keep = [b for u, b in ub if u > best + tol / 2]
        if top - best < tol or not keep:
            return top, best, it, len(boxes)
        nb = []
        for (P1, P2, t1, t2) in keep:
            Pm, tm = 0.5 * (P1 + P2), 0.5 * (t1 + t2)
            nb += [(P1, Pm, t1, tm), (Pm, P2, t1, tm), (P1, Pm, tm, t2), (Pm, P2, tm, t2)]
        boxes = nb
        best = max(best, max(F_point(0.5 * (b[0] + b[1]), 0.5 * (b[2] + b[3]), cf) for b in boxes))
    return max(float(F_upper(*b, c)) for b in boxes), best, -1, len(boxes)


def coefs(cs, ct):
    out = {}
    for name, c in (('s', cs), ('t', ct)):
        ca = arb(c)
        Xb = max(arb('0.928') * ca, arb('0.82'))  # both exact-ish balls
        b = arb(1) / (3 * arb(Llo(arb(Xb.lower()), arb(1))))
        bp = arb(1) / (3 * arb(Llo(arb(max(ca, arb('0.88')).lower()), arb(1))))
        a_up, a_lo, it, nb = sup_a(c)
        out[name] = (up(a_up), up(b), up(bp), a_lo)
    return out


if __name__ == '__main__':
    cs, ct = sys.argv[1], sys.argv[2]
    o = coefs(cs, ct)
    print(f"# coefficients (upper bounds, 6 decimals rounded up) at (c_s, c_t) = ({cs}, {ct})")
    for k in 'st':
        a, b, bp, alo = o[k]
        print(f"{'straight' if k == 's' else 'turn'}: a <= {a:.6f} (point value {alo:.6f}), b <= {b:.6f}, b' <= {bp:.6f}")
    print(f"ARGS {o['s'][0]:.6f} {o['s'][1]:.6f} {o['s'][2]:.6f} {o['t'][0]:.6f} {o['t'][1]:.6f} {o['t'][2]:.6f}")
