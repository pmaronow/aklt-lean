"""Small exact checks for the R4 referee report (standard library only)."""
from fractions import Fraction as F
from itertools import product
from math import log


def moment(exponents):
    if any(e % 2 for e in exponents):
        return F(0)
    numerator = 1
    for e in exponents:
        for k in range(1, e, 2):
            numerator *= k
    denominator = 1
    for k in range(3, sum(exponents) + 2, 2):
        denominator *= k
    return F(numerator, denominator)


def mm(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(4)), F(0))
             for j in range(4)] for i in range(4)]


def trace_product(*matrices):
    a = matrices[0]
    for b in matrices[1:]:
        a = mm(a, b)
    return sum((a[i][i] for i in range(4)), F(0))


def vertex(field, insertion=None):
    result = [[F(0) for _ in range(4)] for _ in range(4)]
    for i, j in product(range(4), repeat=2):
        exponents = [0, 0, 0]
        for index in (i, j, insertion):
            if index:
                exponents[index - 1] += 1
        result[i][j] = moment(exponents)
        exponents[2] += 1
        result[i][j] += field * moment(exponents)
    return result


def opposite_correlation(pinned, octagon=False):
    # Radius-two diamond: four radius-one vertices form a ring through
    # the four corners; each has a tip. Radius-three example: the protected
    # annulus instead forms an eight-vertex ring with four tips and two
    # interior leaves. All boundary pins are (0,0,1) when pinned=True.
    corner = [[F(0) for _ in range(4)] for _ in range(4)]
    if pinned:
        corner[0][0] = F(4, 3)
        corner[0][3] = corner[3][0] = F(2, 3)
        corner[1][1] = corner[2][2] = F(2, 5)
        corner[3][3] = F(8, 15)
    else:
        corner[0][0] = F(1)
        for k in range(1, 4):
            corner[k][k] = F(1, 3)
    ring_length = 8 if octagon else 4
    fields = [F(3, 5) if pinned and (not octagon or i % 2 == 0) else F(0)
              for i in range(ring_length)]
    vertices = [vertex(field) for field in fields]
    denominator = trace_product(*(matrix for v in vertices for matrix in (v, corner)))
    numerator = F(0)
    for k in range(1, 4):
        inserted = [vertex(field, k) if i in (0, ring_length // 2) else vertices[i]
                    for i, field in enumerate(fields)]
        numerator += trace_product(*(matrix for v in inserted for matrix in (v, corner)))
    # For the radius-three example, f,o are uniform leaves of two
    # opposite axial vertices of this ring; each conditional mean is n/3.
    return numerator / denominator / (9 if octagon else 1)


def neg_log_one_minus(z, terms=20):
    """Exact rational enclosure of -log(1-z), for 0 < z < 1."""
    lower = sum((z ** k / k for k in range(1, terms + 1)), F(0))
    upper = lower + z ** (terms + 1) / ((terms + 1) * (1 - z))
    return lower, upper


def reciprocal_log_mean_with_one(a):
    if a == 1:
        return F(1), F(1)
    assert 0 < a < 1
    bounds = neg_log_one_minus(1 - a)
    return bounds[0] / (1 - a), bounds[1] / (1 - a)


def closure_checks():
    graph = {(x, y) for x in range(-4, 5) for y in range(-4, 5)}
    neighbours = lambda p: {(p[0] + dx, p[1] + dy)
                            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1))} & graph
    centre, start, target = (0, 0), (-1, 0), (1, 0)
    protected = {p for p in graph if max(abs(p[0]), abs(p[1])) >= 3}

    def trace(w):
        statuses = {p: ("X" if p == centre else "U") for p in graph}
        kept = {p: neighbours(p) for p in graph}
        used = set()
        snapshots = []
        for i, (a, b) in enumerate(zip(w, w[1:])):
            if i == 0:
                kept[start].discard(centre)
            edge = frozenset((a, b))
            assert edge not in used and b in kept[a] and a in kept[b]
            assert statuses[a] != "X" and statuses[b] != "X"
            used.add(edge)
            kept[a].discard(b)
            kept[b].discard(a)
            statuses[a] = "D" if statuses[a] == "U" else "X"
            snapshots.append((statuses[b], len(kept[b])))
        return snapshots, statuses, kept

    w = [start, (-1, 1), (-2, 1), (-2, 0), start,
         (-1, -1), (0, -1), (1, -1), target]
    assert not (set(w[:-1]) & (protected | {target}))
    snapshots, _, _ = trace(w)
    assert snapshots[3] == ("D", 1)
    print("Exact closure check: after four steps, live endpoint u has status D and one kept bond.")
    boundary_w = [start, (-2, 0), (-3, 0)]
    _, statuses, kept = trace(boundary_w)
    end = boundary_w[-1]
    assert end in protected and statuses[end] == "U" and kept[end] != neighbours(end)
    print("Exact boundary check: stopped endpoint e in S has lost its arrival bond.")


if __name__ == "__main__":
    closure_checks()
    correlations = {}
    ratios = {}
    for name, pinned in (("free", False), ("pinned", True)):
        correlations[name] = opposite_correlation(pinned)
        ratios[name] = F(3, 5) / (1 + correlations[name] / 5)
        print(f"E' opposite correlation ({name}) = {correlations[name]} = {float(correlations[name]):.12f}")
        print(f"one-step ratio from a two-bond D site ({name}) = {ratios[name]} = {float(ratios[name]):.12f}")
    assert correlations["free"] == F(27, 1094)
    assert ratios["free"] != ratios["pinned"]
    print("Exact counterexample: exposure RHS is zero, but ratio difference is nonzero.")

    print("Counterexample without a stopped-boundary defect (radius-three diamond):")
    for name, pinned in (("free", False), ("pinned", True)):
        p = opposite_correlation(pinned, octagon=True)
        rho = F(3, 5) / (1 + p / 5)
        print(f"E'[P_fo] ({name}) = {p} = {float(p):.12f}")
        print(f"rho ({name}) = {rho} = {float(rho):.12f}")
    assert opposite_correlation(False, octagon=True) != opposite_correlation(True, octagon=True)

    lm = lambda a, b: (a - b) / (log(a) - log(b)) if a != b else a
    beta = 1 / (3 * lm(.82, 1))
    alpha_upper = beta - 1 / (5 * 1.072)
    alpha_lower = 1 / (3 * 1.36) - 1 / (5 * lm(.928, 1))
    beta_prime = 1 / (3 * lm(.88, 1))
    print("Numerical coefficient checks:", alpha_upper, alpha_lower, beta, beta_prime)

    log_82 = neg_log_one_minus(F(9, 50))
    log_928 = neg_log_one_minus(F(9, 125))
    log_88 = neg_log_one_minus(F(3, 25))
    beta_upper_exact = log_82[1] / (3 * F(9, 50))
    assert beta_upper_exact < F(36751, 100000)
    assert beta_upper_exact - F(25, 134) < F(18094, 100000)
    assert F(25, 102) - log_928[1] / (5 * F(9, 125)) > F(375, 10000)
    assert log_88[1] / (3 * F(3, 25)) < F(35510, 100000)
    print("The four response-coefficient inequalities also pass exact rational log enclosures.")

    for name, c in (("straight", .961), ("turn", .935)):
        beta_typed = 1 / (3 * lm(.928 * c, 1))
        alpha_typed = beta_typed - 1 / (5 * lm(.928, 1))
        beta_prime_typed = 1 / (3 * lm(c, 1))
        print("Numerical conservative type bounds (alpha need not be optimal):", name, alpha_typed, beta_typed, beta_prime_typed)

    for c, alpha_limit, beta_limit, prime_limit in (
        (F(961, 1000), F(145217, 1000000), F(352782, 1000000), F(340008, 1000000)),
        (F(187, 200), F(149953, 1000000), F(357549, 1000000), F(344661, 1000000)),
    ):
        assert reciprocal_log_mean_with_one(F(116, 125) * c)[1] / 3 < beta_limit
        assert reciprocal_log_mean_with_one(c)[1] / 3 < prime_limit
        if c == F(961, 1000):
            p0 = F(-9, 25)
        else:
            # See the report's verification notes: Imin decreases to p=-9/50.
            # At this p0 it is still at least c*(1+p0/5).
            p0 = F(-1119, 3125)
            discriminant_side = 3 + p0 - 3 * c * (1 + p0 / 5)
            assert discriminant_side > 0
            assert discriminant_side ** 2 >= F(9, 25) * (F(18, 25) + 2 * p0)
        j0 = 1 + p0 / 5
        upper_alpha = reciprocal_log_mean_with_one(c * j0)[1] / 3 - reciprocal_log_mean_with_one(j0)[0] / 5
        assert upper_alpha < alpha_limit
    print("All six type-dependent bounds pass exact rational log enclosures (with the Imin bound for turns).")
