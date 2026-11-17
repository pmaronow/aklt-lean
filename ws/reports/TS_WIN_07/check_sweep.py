"""Supplementary small-case checks for TS_WIN_07; no Lean proofs.

Uses only the Python standard library. These checks corroborate the review;
the arguments in the report, not numerical sampling, determine the verdicts.
"""

from fractions import Fraction as F
from itertools import combinations, product
from math import prod, sqrt
import json


class Q5:
    """Exact a + b*sqrt(5), used for even icosahedral moments."""

    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    @staticmethod
    def lift(x):
        return x if isinstance(x, Q5) else Q5(x)

    def __add__(self, other):
        other = self.lift(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.lift(other)

    def __mul__(self, other):
        other = self.lift(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.lift(other)
        denominator = other.a**2 - 5 * other.b**2
        assert denominator != 0
        return self * Q5(other.a / denominator, -other.b / denominator)

    def __pow__(self, n):
        assert n >= 0
        return prod([self] * n, start=Q5(1))

    def __eq__(self, other):
        other = self.lift(other)
        return self.a == other.a and self.b == other.b

    def key(self):
        return self.a, self.b


phi = Q5(F(1, 2), F(1, 2))
r_sq = phi + 2
raw = []
for axis, a, b in product(range(3), [-1, 1], [-1, 1]):
    raw.append((Q5(0), Q5(a), phi * b) if axis == 0 else
               (Q5(a), phi * b, Q5(0)) if axis == 1 else
               (phi * b, Q5(0), Q5(a)))
raw_keys = {tuple(x.key() for x in v) for v in raw}
assert len(raw_keys) == 12
assert all(sum((x*x for x in v), Q5(0)) == r_sq for v in raw)
assert all(tuple((-x).key() for x in v) in raw_keys for v in raw)


def raw_monomial(v, exponents):
    return prod((x**n for x, n in zip(v, exponents)), start=Q5(1))


moment_count = 0
for exponents in product(range(5), repeat=3):
    degree = sum(exponents)
    if degree > 4:
        continue
    numerator = sum((raw_monomial(v, exponents) for v in raw), Q5(0))
    if degree % 2:
        assert numerator == 0
    else:
        actual = numerator / (12 * r_sq**(degree // 2))
        expected = (F(1) if degree == 0 else
                    F(1, 3) if degree == 2 and 2 in exponents else
                    F(1, 5) if degree == 4 and 4 in exponents else
                    F(1, 15) if degree == 4 and all(n % 2 == 0 for n in exponents) else
                    F(0))
        assert actual == expected, exponents
    moment_count += 1


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


# The finite removed-site average is exact for arbitrary rational fields.
fields = [(F(2, 3), F(-1, 5), F(7, 4)),
          (F(-3, 2), F(4, 7), F(1, 3)),
          (F(1, 11), F(8, 5), F(-2, 3)),
          (F(5, 6), F(-4, 9), F(3, 2))]
subset_count = 0
for mask in range(16):
    chosen = [a for i, a in enumerate(fields) if mask & (1 << i)]
    integrated = Q5(0)
    for size in range(0, len(chosen) + 1, 2):
        for subset in combinations(chosen, size):
            numerator = sum((prod((sum((v[i] * a[i] for i in range(3)), Q5(0))
                                  for a in subset), start=Q5(1)) for v in raw), Q5(0))
            integrated += numerator / (12 * r_sq**(size // 2))
    expected = 1 + sum((dot(a, b) for a, b in combinations(chosen, 2)), F(0)) / 3
    if len(chosen) == 4:
        a, b, c, d = chosen
        expected += (dot(a, b)*dot(c, d) + dot(a, c)*dot(b, d) + dot(a, d)*dot(b, c)) / 15
    assert integrated == expected, mask
    subset_count += 1


def neighbours(x):
    return {(x[0] + a, x[1] + b) for a, b in [(1, 0), (0, 1), (-1, 0), (0, -1)]}


def distance(x, y):
    return abs(x[0] - y[0]) + abs(x[1] - y[1])


G = set(product(range(-3, 4), repeat=2))
outside = set(product(range(-4, 5), repeat=2)) - G
depth = {x: min(distance(x, y) for y in outside) for x in G}
x = (0, 0)
eligible = sorted(z for z in G if z != x and depth[z] >= 3)
geometry_count = 0
for mask in range(1 << len(eligible)):
    Y = {z for i, z in enumerate(eligible) if mask & (1 << i)}
    D = G - Y - {x}
    V = neighbours(x) & D
    assert len(V) <= 4
    if not Y:
        assert len(V) == 4
    if Y & neighbours(x):
        assert len(V) <= 3
    assert all(depth[z] >= 2 for z in V)
    assert all(distance(z, w) == 2 for z, w in combinations(V, 2))
    assert all(len(neighbours(z) & D) <= 3 for z in V)
    assert all(neighbours(z) <= G for z in V)
    geometry_count += 1


# Exhaust all 12^4 support assignments for the quartic observable.
phi_f = (1 + sqrt(5)) / 2
r_f = sqrt(phi_f + 2)
atoms = []
for axis, a, b in product(range(3), [-1, 1], [-1, 1]):
    vector = ((0, a, b*phi_f) if axis == 0 else
              (a, b*phi_f, 0) if axis == 1 else (b*phi_f, 0, a))
    atoms.append(tuple(t/r_f for t in vector))
dot_table = [[dot(a, b) for b in atoms] for a in atoms]
max_quartic = 0.0
for a, b, c, d in product(range(12), repeat=4):
    q = (dot_table[a][b]*dot_table[c][d] +
         dot_table[a][c]*dot_table[b][d] +
         dot_table[a][d]*dot_table[b][c])
    max_quartic = max(max_quartic, abs(q))
assert max_quartic <= 3 + 1e-12
assert abs(max_quartic - 3) < 1e-12


# Positive and zero conditioning fibres, with exactly k independent sites.
# Triple parallel fields realize the extremal mean +/-(3/5)*a.
fibre_models = []
for k in range(5):
    pair_average = 0.0
    norms = []
    model_states = 0
    for h, mass in [(0, 0.3), (1, 0.7), (2, 0.0)]:
        local_laws, means = [], []
        for j in range(k):
            field = atoms[0 if h == 0 else 3]
            if j % 2:
                field = tuple(-t for t in field)
            weights = [max(0.0, 1 + dot(n, field))**3 / 12 for n in atoms]
            normalizer = sum(weights)
            assert normalizer > 0
            law = [w/normalizer for w in weights]
            mean = tuple(sum(p*n[i] for p, n in zip(law, atoms)) for i in range(3))
            norms.append(dot(mean, mean))
            assert dot(mean, mean) <= F(9, 25) + 1e-12
            local_laws.append(law)
            means.append(mean)
        enumerated_mass, conditional_pairs = 0.0, 0.0
        pair_values = {(i, j): 0.0 for i, j in combinations(range(k), 2)}
        for letters in product(range(12), repeat=k):
            weight = prod(local_laws[j][letters[j]] for j in range(k))
            enumerated_mass += weight
            for i, j in pair_values:
                pair_values[i, j] += weight * dot_table[letters[i]][letters[j]]
            model_states += 1
        assert abs(enumerated_mass - 1) < 1e-10
        for (i, j), actual in pair_values.items():
            assert abs(actual - dot(means[i], means[j])) < 1e-10
            conditional_pairs += actual
        pair_average += mass * conditional_pairs
    assert pair_average >= -F(9, 50)*k - 1e-10
    fibre_models.append({"k": k, "states_enumerated": model_states,
                         "pair_expectation": pair_average,
                         "max_squared_mean": max(norms, default=0.0)})


lower_bounds = []
for k in range(5):
    worst_pair = -F(9, 50)*k
    value = 1 + worst_pair/3 - (F(3, 15) if k == 4 else 0)
    target = F(14, 25) if k == 4 else F(41, 50)
    assert value >= target
    lower_bounds.append({"k": k, "derived": str(value), "target": str(target)})

print(json.dumps({
    "exact_support_atoms": 12,
    "exact_monomials_through_degree_four": moment_count,
    "exact_removed_site_subsets": subset_count,
    "survivor_geometry_cases": geometry_count,
    "quartic_assignments": 12**4,
    "quartic_max_absolute_value_float": max_quartic,
    "fibre_models": fibre_models,
    "exact_polynomial_bounds": lower_bounds,
    "status": "PASS",
}, indent=2))
