"""Exact finite-case audit in Q(phi), phi^2 = phi + 1; no Lean proofs."""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json


@dataclass(frozen=True)
class QPhi:
    a: F = F(0)
    b: F = F(0)

    @staticmethod
    def of(value):
        return value if isinstance(value, QPhi) else QPhi(F(value))

    def __add__(self, other):
        other = self.of(other)
        return QPhi(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return QPhi(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.of(other)

    def __mul__(self, other):
        other = self.of(other)
        return QPhi(
            self.a * other.a + self.b * other.b,
            self.a * other.b + self.b * other.a + self.b * other.b,
        )

    __rmul__ = __mul__

    def inverse(self):
        field_norm = self.a**2 + self.a * self.b - self.b**2
        assert field_norm != 0
        return QPhi((self.a + self.b) / field_norm, -self.b / field_norm)

    def __truediv__(self, other):
        return self * self.of(other).inverse()

    def __pow__(self, n):
        assert n >= 0
        result = QPhi.of(1)
        for _ in range(n):
            result = result * self
        return result


ZERO, ONE, PHI = QPhi(), QPhi.of(1), QPhi(F(0), F(1))
R2 = PHI + 2
LABELS = tuple(product(range(3), range(2), range(2)))


def numerator(label):
    group, a_bit, b_bit = label
    a = QPhi.of(1 if a_bit == 0 else -1)
    b = (1 if b_bit == 0 else -1) * PHI
    return ((ZERO, a, b), (a, b, ZERO), (b, ZERO, a))[group]


VECTORS = {label: numerator(label) for label in LABELS}
INVERSE = {v: label for label, v in VECTORS.items()}
assert len(INVERSE) == 12
assert PHI**2 == PHI + 1
assert R2**2 == 5 * PHI**2
assert ONE + PHI**4 == 3 * PHI**2
for vector in VECTORS.values():
    assert sum((x**2 for x in vector), ZERO) == R2
    assert vector.count(ZERO) == 1

reflection_counts = []
for coordinate in range(3):
    reflection = {}
    for label, vector in VECTORS.items():
        reflected = tuple(-x if i == coordinate else x for i, x in enumerate(vector))
        reflection[label] = INVERSE[reflected]
    assert len(set(reflection.values())) == 12
    assert all(reflection[reflection[label]] == label for label in LABELS)
    reflection_counts.append(sum(reflection[label] == label for label in LABELS))


def exponent_triples(max_degree):
    return (m for m in product(range(max_degree + 1), repeat=3) if sum(m) <= max_degree)


def raw_average(m):
    total = ZERO
    for vector in VECTORS.values():
        term = ONE
        for coordinate in range(3):
            term = term * vector[coordinate] ** m[coordinate]
        total = total + term
    return total / 12


def exact_moment(m):
    raw = raw_average(m)
    if any(k % 2 for k in m):
        assert raw == ZERO
        return ZERO
    return raw / (R2 ** (sum(m) // 2))


def rational_moment(m):
    degree = sum(m)
    if degree == 0:
        return F(1)
    if degree == 2 and 2 in m:
        return F(1, 3)
    if degree == 4 and 4 in m:
        return F(1, 5)
    if degree == 4 and all(k % 2 == 0 for k in m):
        return F(1, 15)
    return F(0)


odd_checked = 0
for m in exponent_triples(12):
    if any(k % 2 for k in m):
        assert raw_average(m) == ZERO
        odd_checked += 1

low_degree_counts = Counter()
for m in exponent_triples(4):
    assert exact_moment(m) == QPhi.of(rational_moment(m))
    low_degree_counts[sum(m)] += 1

tensor_counts = Counter()
pairing_counts = Counter()
for degree in range(1, 5):
    for indices in product(range(3), repeat=degree):
        m = tuple(indices.count(i) for i in range(3))
        if degree in (1, 3):
            tensor_value = F(0)
        elif degree == 2:
            tensor_value = F(int(indices[0] == indices[1]), 3)
        else:
            i, j, k, ell = indices
            pairings = sum((i == j and k == ell, i == k and j == ell, i == ell and j == k))
            tensor_value = F(pairings, 15)
            pairing_counts[pairings] += 1
        assert tensor_value == rational_moment(m)
        tensor_counts[degree] += 1

# Symbolic c is represented by the pair (constant term, coefficient of c).
# For positive degree the tensor and rational formula both have no constant
# term, so equality of these pairs checks every real c, including zero/negative c.
scaled_counts = Counter()
for m in exponent_triples(4):
    degree = sum(m)
    indices = tuple(i for i in range(3) for _ in range(m[i]))
    if degree == 0:
        tensor_polynomial = (F(1), F(0))
        scaled_polynomial = (F(1), F(0))
    else:
        if degree in (1, 3):
            coefficient = F(0)
        elif degree == 2:
            coefficient = F(int(indices[0] == indices[1]), 3)
        else:
            i, j, k, ell = indices
            coefficient = F(sum((i == j and k == ell, i == k and j == ell, i == ell and j == k)), 15)
        tensor_polynomial = (F(0), coefficient)
        scaled_polynomial = (F(0), rational_moment(m))
    assert tensor_polynomial == scaled_polynomial
    scaled_counts[degree] += 1

results = {
    "arithmetic": "exact Fraction coefficients in Q(phi), phi^2=phi+1",
    "distinct_numerators": len(INVERSE),
    "unit_numerator_checks": len(VECTORS),
    "coordinate_reflections": 3,
    "reflection_fixed_labels": reflection_counts,
    "odd_exponent_triples_through_total_degree_12": odd_checked,
    "monomials_through_total_degree_4": dict(sorted(low_degree_counts.items())),
    "tensor_index_tuples_by_degree": dict(sorted(tensor_counts.items())),
    "fourth_tensor_pairing_multiplicities": dict(sorted(pairing_counts.items())),
    "symbolic_scale_monomials_by_degree": dict(sorted(scaled_counts.items())),
    "status": "all checks passed",
    "limits": "Finite algebra checks supplement the mathematical audit; no Lean proofs are constructed. Radius positivity and arbitrary-degree parity are assessed mathematically.",
}
print(json.dumps(results, indent=2))
