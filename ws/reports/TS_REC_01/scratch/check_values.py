"""Exact low-degree atom checks and numerical log-mean smoke checks; no Lean proofs."""
from decimal import Decimal, getcontext
from fractions import Fraction as F
from itertools import product
import json


def q(a=0, b=0):
    return F(a), F(b)  # a + b sqrt(5)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def mul(x, y):
    return x[0] * y[0] + 5 * x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def power(x, k):
    answer = q(1)
    for _ in range(k):
        answer = mul(answer, x)
    return answer


def divide(x, y):
    denominator = y[0] ** 2 - 5 * y[1] ** 2
    return mul(x, (y[0] / denominator, -y[1] / denominator))


phi = q(F(1, 2), F(1, 2))
radius_squared = add(phi, q(2))
atoms = []
for direction, sign_a, sign_b in product(range(3), (1, -1), (1, -1)):
    a, b = q(sign_a), mul(q(sign_b), phi)
    atoms.append(((q(), a, b), (a, b, q()), (b, q(), a))[direction])
assert len(set(atoms)) == 12
for atom in atoms:
    actual = q()
    for coordinate in atom:
        actual = add(actual, power(coordinate, 2))
    assert actual == radius_squared
    assert tuple(mul(q(-1), coordinate) for coordinate in atom) in atoms

moment_checks = 0
for exponent in product(range(5), repeat=3):
    degree = sum(exponent)
    if degree > 4:
        continue
    numerator = q()
    for atom in atoms:
        term = q(1)
        for coordinate, k in zip(atom, exponent):
            term = mul(term, power(coordinate, k))
        numerator = add(numerator, term)
    if degree % 2:
        assert numerator == q()
        actual = q()
    else:
        actual = divide(numerator, mul(q(12), power(radius_squared, degree // 2)))
    if degree == 0:
        expected = F(1)
    elif any(k % 2 for k in exponent):
        expected = F(0)
    elif degree == 2:
        expected = F(1, 3)
    else:
        expected = F(1, 5) if 4 in exponent else F(1, 15)
    assert actual == q(expected), (exponent, actual, expected)
    # U and D: D has mass 3/5 on the unit alphabet and 2/5 at zero.
    for status in ('U', 'D'):
        weight = F(1) if status == 'U' else F(3, 5)
        zero_mass = F(2, 5) if status == 'D' and degree == 0 else F(0)
        assert add(mul(q(weight), actual), q(zero_mass)) == q(
            weight * expected + zero_mass
        )
        moment_checks += 1

assert 1 - F(27, 50) / 3 == F(41, 50)
assert 1 + F(27, 25) / 3 == F(34, 25)
assert 1 - F(9, 25) / 5 == F(116, 125)
assert 1 + F(9, 25) / 5 == F(134, 125)
assert 1 - F(9, 25) / 3 == F(22, 25)
assert 1 + F(9, 25) / 3 == F(28, 25)
assert F(1, 3) - F(1, 5) == F(2, 15)

getcontext().prec = 90
grid = tuple(map(Decimal, (
    '0.00000001', '0.1', '0.82', '0.88', '0.99999999999999999999',
    '1', '1.00000000000000000001', '1.12', '1.36', '2', '100000000',
)))


def log_mean(x, y):
    return x if x == y else (x - y) / (x.ln() - y.ln())


tolerance = Decimal('1e-65')
for x, y in product(grid, repeat=2):
    value = log_mean(x, y)
    assert 0 < value
    assert min(x, y) - tolerance <= value <= max(x, y) + tolerance
    assert abs(x.ln() - y.ln() - (x - y) / value) <= tolerance
monotonicity_checks = 0
for x, xp, y, yp in product(grid, repeat=4):
    if x <= xp and y <= yp:
        assert log_mean(x, y) <= log_mean(xp, yp) + tolerance
        monotonicity_checks += 1

print(json.dumps({
    'distinct_antipodal_unit_atoms': len(atoms),
    'exact_U_D_monomial_checks_through_degree_four': moment_checks,
    'exact_response_endpoint_arithmetic_checks': 7,
    'decimal_precision': getcontext().prec,
    'log_mean_basic_grid_pairs': len(grid) ** 2,
    'log_mean_monotonicity_grid_checks': monotonicity_checks,
    'interpretation': 'Supplementary checks; not proofs of the universal statements.',
}, indent=2))
