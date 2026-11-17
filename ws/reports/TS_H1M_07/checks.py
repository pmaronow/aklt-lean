"""Supplementary small-case checks of the definitions; no Lean proofs.

The moment and group checks use exact rational arithmetic. Matrix checks use
Python complex arithmetic and an absolute error tolerance of 1e-10.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json


@dataclass(frozen=True)
class Q5:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "a", F(self.a))
        object.__setattr__(self, "b", F(self.b))

    def __add__(self, other):
        other = other if isinstance(other, Q5) else Q5(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        other = other if isinstance(other, Q5) else Q5(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = other if isinstance(other, Q5) else Q5(other)
        denominator = other.a * other.a - 5 * other.b * other.b
        assert denominator != 0
        return self * Q5(other.a / denominator, -other.b / denominator)

    def __pow__(self, exponent):
        answer = Q5(1)
        for _ in range(exponent):
            answer = answer * self
        return answer


def prod(values, start=1):
    for value in values:
        start = start * value
    return start


phi = Q5(F(1, 2), F(1, 2))
radius_squared = phi + 2
vertices = []
for position, sign_a, sign_b in product(range(3), (1, -1), (1, -1)):
    a, b = Q5(sign_a), sign_b * phi
    vertices.append(((Q5(), a, b), (a, b, Q5()), (b, Q5(), a))[position])

for vertex in vertices:
    assert sum((value * value for value in vertex), Q5()) == radius_squared


def rational_moment(exponents):
    degree = sum(exponents)
    if degree == 0:
        return F(1)
    if degree == 2 and 2 in exponents:
        return F(1, 3)
    if degree == 4 and 4 in exponents:
        return F(1, 5)
    if degree == 4 and all(e % 2 == 0 for e in exponents):
        return F(1, 15)
    return F(0)


moment_count = 0
for exponents in product(range(5), repeat=3):
    degree = sum(exponents)
    if degree > 4:
        continue
    numerator = sum((prod((v[i] ** exponents[i] for i in range(3)), Q5(1))
                     for v in vertices), Q5())
    if degree % 2:
        # The common nonzero normalization does not affect a zero numerator.
        assert numerator == Q5()
        unit_average = Q5()
    else:
        unit_average = numerator / (12 * radius_squared ** (degree // 2))
    for status in ("U", "D"):
        actual = unit_average
        if status == "D":
            actual = F(3, 5) * actual + (F(2, 5) if degree == 0 else 0)
        expected = rational_moment(exponents)
        if status == "D" and degree != 0:
            expected *= F(3, 5)
        assert actual == Q5(expected), (exponents, status, actual, expected)
        moment_count += 1


corners = [(1, 1), (-1, 1), (-1, -1), (1, -1)]
tips = [(2, 0), (0, 2), (-2, 0), (0, -2)]
leaders = [0, 2, 4, 6, 8, 11, 14, 17]
group_count = 0
for pair_flags in product((False, True), repeat=4):
    groups = [{leaders[i], min(19, leaders[i] + 1)} if pair_flags[i]
              else {leaders[i]} for i in range(4)]
    groups += [{leader} for leader in leaders[4:]]
    assert sum(map(len, groups)) == len(set.union(*groups))
    for i, flag in enumerate(pair_flags):
        if flag:
            assert corners[i] != (0, 0)
            assert leaders[i] != min(19, leaders[i] + 1)
    group_count += 1


# Nonvacuity: an east-going covered pattern with the arrival site removed,
# first with a U corner and then with a D corner at (1, 1).
steps = {(1, 0), (0, 1), (-1, 0), (0, -1)}
template = {(x, y) for x in range(-2, 3) for y in range(-2, 3)
            if abs(x) + abs(y) <= 2}
tips_set = set(tips)
corners_set = set(corners)


def translate(x, d):
    return x[0] + d[0], x[1] + d[1]


nonvacuity_count = 0
for chosen_status in ("U", "D"):
    status = {x: "U" for x in template}
    status[(0, -1)] = "X"
    status[(1, 1)] = chosen_status
    kept = {x: {translate(x, d) for d in steps} for x in template}
    kept[(0, 0)] = {(1, 0), (0, 1), (-1, 0)}
    if chosen_status == "D":
        kept[(1, 1)] = {(1, 0), (0, 1)}
    assert status[(0, 0)] == "U" and status[(0, -1)] == "X"
    assert status[(1, 0)] != "X"  # Outgoing east.
    for d in {(1, 0), (0, 1), (-1, 0)}:
        assert status[d] in ("U", "X") or (
            status[d] == "D" and len(kept[d]) == 2 and (0, 0) in kept[d])
    for x in corners:
        assert status[x] in ("U", "X") or (status[x] == "D" and len(kept[x]) == 2)
    for x in template - tips_set - {(0, 0)}:
        if status[x] == "U":
            assert kept[x] == {translate(x, d) for d in steps}
    assert all(status[x] == "U" for x in tips)
    for x, y in product(template - tips_set, repeat=2):
        if status[x] != "X" and status[y] != "X" and (
                abs(x[0] - y[0]) + abs(x[1] - y[1]) == 1):
            assert (y in kept[x]) == (x in kept[y])
    bonds = {(x, translate(x, d)) for x in template for d in {(1, 0), (0, 1)}
             if translate(x, d) in template}
    bonds = {(x, y) for x, y in bonds if status[x] != "X" and status[y] != "X"
             and (x in tips_set or y in kept[x])
             and (y in tips_set or x in kept[y])}
    degrees = {x: sum(x in edge for edge in bonds) for x in template}
    for representation in ("reduced", "unreduced"):
        def single(x):
            return degrees[x] == 1 and (
                x in tips_set or (representation == "reduced" and x in corners_set))

        retained = {x for x in template if status[x] != "X" and x not in tips_set
                    and (x not in corners_set or (degrees[x] != 0 and not single(x)))}
        groups = {x for x in corners_set | tips_set if degrees[x] > 0}
        pairs = {x for x in groups if x in corners_set and not single(x)}
        assert (1, 1) in pairs and (1, 1) in retained
        assert all(x in retained and x != (0, 0) for x in pairs)
        nonvacuity_count += 1


def identity(size):
    return [[complex(i == j) for j in range(size)] for i in range(size)]


def add(a, b):
    return [[x + y for x, y in zip(row_a, row_b)] for row_a, row_b in zip(a, b)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, column)) for column in zip(*b)]
            for row in a]


def error(a, b):
    return max((abs(x - y) for row_a, row_b in zip(a, b)
                for x, y in zip(row_a, row_b)), default=0)


max_error = 0
matrix_check_count = 0


def check_equal(a, b):
    global max_error, matrix_check_count
    residual = error(a, b)
    max_error = max(max_error, residual)
    assert residual < 1e-10, residual
    matrix_check_count += 1


def basis(slots):
    return list(product(range(2), repeat=slots))


def lift(slots, j, a):
    states = basis(slots)
    return [[a[sigma[j]][tau[j]] if all(sigma[k] == tau[k]
             for k in range(slots) if k != j) else 0
             for tau in states] for sigma in states]


def exchange(slots, j, k):
    states = basis(slots)
    swapped = [tuple(tau[k] if x == j else tau[j] if x == k else tau[x]
                     for x in range(slots)) for tau in states]
    return [[complex(sigma == tau) for tau in swapped] for sigma in states]


pauli = [identity(2), [[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]]


def bloch(n):
    answer = [[0j, 0j], [0j, 0j]]
    for k in range(3):
        answer = add(answer, scale(n[k], pauli[k + 1]))
    return answer


def pair(slots, j, k, eta, n):
    b = add(identity(2), scale(eta, bloch(n)))
    return multiply(lift(slots, j, b), lift(slots, k, b))


# Coefficient one in the product of (Kronecker delta + t A) entries.
a = [[1 + 2j, -3 + 1j], [F(1, 2) - 2j, -1 + F(3, 2) * 1j]]
for slots in range(5):
    states = basis(slots)
    actual = []
    for sigma in states:
        row = []
        for tau in states:
            coefficients = [1]
            for k in range(slots):
                new = [0j] * (len(coefficients) + 1)
                for degree, value in enumerate(coefficients):
                    new[degree] += value * (sigma[k] == tau[k])
                    new[degree + 1] += value * a[sigma[k]][tau[k]]
                coefficients = new
            row.append(coefficients[1] if len(coefficients) > 1 else 0)
        actual.append(row)
    expected = scale(0, identity(len(states)))
    for k in range(slots):
        expected = add(expected, lift(slots, k, a))
    check_equal(actual, expected)


unit_vectors = [(1, 0, 0), (0, 1, 0), (0, 0, 1),
                (F(2, 3), F(1, 3), F(2, 3)), (F(-2, 7), F(3, 7), F(6, 7))]
all_vectors = unit_vectors + [(0, 0, 0), (F(1, 4), F(-1, 3), 0), (2, 0, 0)]
for slots, j, k in [(1, 0, 0), (2, 0, 1), (2, 0, 0),
                    (3, 0, 2), (3, 2, 0), (3, 1, 1)]:
    e = exchange(slots, j, k)
    projection = scale(F(1, 2), add(identity(2 ** slots), e))
    check_equal(multiply(e, e), identity(2 ** slots))
    check_equal(multiply(projection, projection), projection)
    for eta, n in product((-2, -1, 0, 1, F(3, 2)), all_vectors):
        term = pair(slots, j, k, eta, n)
        check_equal(multiply(term, e), multiply(e, term))
        if eta in (-1, 1) and n in unit_vectors:
            check_equal(multiply(projection, term), term)
            check_equal(multiply(term, projection), term)


# Transfer with signed complex coefficients and auxiliary factors that commute
# with exchange but need not commute with the pair term itself.
slots, j, k = 3, 0, 1
e = exchange(slots, j, k)
projection = scale(F(1, 2), add(identity(8), e))
h = add(add(lift(3, 0, pauli[1]), lift(3, 1, pauli[1])), lift(3, 2, a))
check_equal(multiply(h, e), multiply(e, h))
check_equal(multiply(h, projection), multiply(projection, h))
for unit_only, vectors in [(True, unit_vectors), (False, all_vectors[:-1]), (True, [])]:
    operator = scale(0, identity(8))
    for index, n in enumerate(vectors):
        operator = add(operator, scale((-1) ** index * (index + 1j),
                       multiply(pair(slots, j, k, -1, n), h)))
    check_equal(multiply(operator, e), multiply(e, operator))
    if unit_only:
        check_equal(multiply(multiply(projection, operator), projection), operator)


print(json.dumps({
    "exact_unit_ico_checks": len(vertices),
    "exact_status_monomial_checks_degree_at_most_four": moment_count,
    "exact_group_partition_checks": group_count,
    "covered_pattern_representation_nonvacuity_checks": nonvacuity_count,
    "complex_matrix_equalities": matrix_check_count,
    "matrix_tolerance": 1e-10,
    "maximum_matrix_residual": max_error,
    "tensor_sizes_checked": [0, 1, 2, 3, 4],
    "checks_are_supplementary_not_proofs": True,
}, indent=2))
