"""Finite and symbolic checks only; this file contains no Lean proofs."""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


@dataclass(frozen=True)
class Q5:
    """Exact arithmetic in Q(sqrt(5))."""

    a: F = F(0)
    b: F = F(0)

    def __add__(self, other):
        other = coerce(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -coerce(other)

    def __rsub__(self, other):
        return coerce(other) + -self

    def __mul__(self, other):
        other = coerce(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = coerce(other)
        denominator = other.a * other.a - 5 * other.b * other.b
        assert denominator != 0
        return self * Q5(other.a / denominator, -other.b / denominator)

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result = Q5(F(1))
        for _ in range(exponent):
            result *= self
        return result


def coerce(value):
    return value if isinstance(value, Q5) else Q5(F(value))


def finite_product(values, identity=1):
    result = identity
    for value in values:
        result *= value
    return result


# Geometry from Geometry.lean, Pattern.lean, and the exact externalSlot table.
sites = {(x, y) for x in range(-2, 3) for y in range(-2, 3)
         if abs(x) + abs(y) <= 2}
tips = {(2, 0), (0, 2), (-2, 0), (0, -2)}
corners = {(1, 1), (-1, 1), (-1, -1), (1, -1)}
slots = [
    ((1, 1), 'E'), ((1, 1), 'N'), ((-1, 1), 'N'), ((-1, 1), 'W'),
    ((-1, -1), 'W'), ((-1, -1), 'S'), ((1, -1), 'S'), ((1, -1), 'E'),
    ((2, 0), 'E'), ((2, 0), 'N'), ((2, 0), 'S'),
    ((0, 2), 'E'), ((0, 2), 'N'), ((0, 2), 'W'),
    ((-2, 0), 'N'), ((-2, 0), 'W'), ((-2, 0), 'S'),
    ((0, -2), 'E'), ((0, -2), 'W'), ((0, -2), 'S'),
]
steps = {'E': (1, 0), 'N': (0, 1), 'W': (-1, 0), 'S': (0, -1)}


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def adjacent(x, y):
    return abs(x[0] - y[0]) + abs(x[1] - y[1]) == 1


bonds = {(x, add(x, steps[d])) for x in sites for d in ('E', 'N')
         if add(x, steps[d]) in sites}
bond_degrees = Counter(x for edge in bonds for x in edge)
slot_counts = Counter(x for x, _ in slots)
assert len(sites) == 13 and len(bonds) == 16 and len(slots) == 20
assert len(set(slots)) == 20
assert all(x in sites and add(x, steps[d]) not in sites for x, d in slots)
assert all(x != y and adjacent(x, y) for x, y in bonds)
assert all(bond_degrees[x] + slot_counts[x] == 4 for x in sites)

# A semantic witness for the full Covered predicate: no D sites are needed.
status = {x: ('X' if x == (0, -1) else 'U') for x in sites}
kept = {x: {add(x, steps[d]) for d in steps} for x in sites}
kept[(0, 0)] = {(1, 0), (0, 1), (-1, 0)}
outgoing = 'E'
assert outgoing != 'S' and status[(0, 0)] == 'U'
assert kept[(0, 0)] == {(1, 0), (0, 1), (-1, 0)}
assert status[(0, -1)] == 'X'
assert all(status[steps[d]] in ('U', 'X') for d in ('E', 'N', 'W'))
assert status[steps[outgoing]] != 'X'
assert all(status[x] in ('U', 'X') for x in corners)
assert all(kept[x] == {add(x, steps[d]) for d in steps}
           for x in sites if x != (0, 0) and x not in tips and status[x] == 'U')
assert all(status[x] == 'U' for x in tips)
assert all((y in kept[x]) == (x in kept[y])
           for x in sites - tips for y in sites - tips
           if status[x] != 'X' and status[y] != 'X' and adjacent(x, y))


# Exactly match rationalMoment and rationalStatusMoment.
def rational_moment(m):
    degree = sum(m)
    if degree == 0:
        return F(1)
    if degree == 2 and 2 in m:
        return F(1, 3)
    if degree == 4 and 4 in m:
        return F(1, 5)
    if degree == 4 and all(exponent % 2 == 0 for exponent in m):
        return F(1, 15)
    return F(0)


def status_moment(s, m):
    return (F(3, 5) if s == 'D' and sum(m) != 0 else F(1)) * rational_moment(m)


phi = Q5(F(1, 2), F(1, 2))
radius_squared = phi + 2
atoms = []
for group, sign_a, sign_b in product(range(3), (1, -1), (1, -1)):
    a, b = coerce(sign_a), sign_b * phi
    atoms.append(((Q5(), a, b), (a, b, Q5()), (b, Q5(), a))[group])
assert len(set(atoms)) == 12
assert radius_squared.a > 0 and radius_squared.b > 0
assert all(sum(value * value for value in v) == radius_squared for v in atoms)

exponents = [m for m in product(range(5), repeat=3) if sum(m) <= 4]
assert len(exponents) == 35
for m in exponents:
    numerator = sum(finite_product((v[i] ** m[i] for i in range(3)), coerce(1))
                    for v in atoms) / 12
    if sum(m) % 2:
        assert numerator == Q5()
        actual_u = Q5()
    else:
        actual_u = numerator / (radius_squared ** (sum(m) // 2))
    actual_d = actual_u * F(3, 5) + (coerce(F(2, 5)) if sum(m) == 0 else Q5())
    assert actual_u == coerce(status_moment('U', m)), m
    assert actual_d == coerce(status_moment('D', m)), m


# Rational polynomial operations also support exact Gaussian integer pairs.
zero_exponent = (0, 0, 0)


def poly_add(left, right):
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, 0) + coefficient
        if result[exponent] == 0:
            del result[exponent]
    return result


def poly_scale(value, polynomial):
    return {exponent: value * coefficient for exponent, coefficient in polynomial.items()
            if value * coefficient != 0}


def poly_mul(left, right):
    result = {}
    for a, c in left.items():
        for b, d in right.items():
            exponent = tuple(x + y for x, y in zip(a, b))
            result[exponent] = result.get(exponent, 0) + c * d
    return {m: c for m, c in result.items() if c != 0}


def poly_power(polynomial, exponent):
    result = {zero_exponent: F(1)}
    for _ in range(exponent):
        result = poly_mul(result, polynomial)
    return result


variables = [{tuple(int(i == j) for i in range(3)): F(1)} for j in range(3)]
rotations = [
    [[F(3, 5), F(-4, 5), 0], [F(4, 5), F(3, 5), 0], [0, 0, 1]],
    [[F(int(i == j)) - 2 * v * w for j, w in enumerate((F(1, 3), F(2, 3), F(2, 3)))]
     for i, v in enumerate((F(1, 3), F(2, 3), F(2, 3)))],
]
covariance_checks = 0
for rotation in rotations:
    assert all(sum(rotation[k][i] * rotation[k][j] for k in range(3)) == int(i == j)
               for i in range(3) for j in range(3))
    linear_forms = []
    for row in rotation:
        value = {}
        for coefficient, variable in zip(row, variables):
            value = poly_add(value, poly_scale(coefficient, variable))
        linear_forms.append(value)
    for m in exponents:
        transformed = {zero_exponent: F(1)}
        for linear_form, exponent in zip(linear_forms, m):
            transformed = poly_mul(transformed, poly_power(linear_form, exponent))
        for s in ('U', 'D'):
            actual = sum(c * status_moment(s, exponent) for exponent, c in transformed.items())
            assert actual == status_moment(s, m)
            covariance_checks += 1


# Direct assignment sums for selected admissible monomials on zero, one, two sites.
letters = [(Q5(), Q5(), Q5())] + atoms


def weight(s, letter):
    if letter == 0:
        return F(2, 5) if s == 'D' else F(0)
    return F(1, 12) if s == 'U' else F(1, 20)


def direct_raw_monomial(statuses, monomials):
    degree = sum(sum(m) for m in monomials)
    numerator = Q5()
    for assignment in product(range(13), repeat=len(statuses)):
        term = coerce(1)
        for s, m, letter in zip(statuses, monomials, assignment):
            term *= weight(s, letter)
            term *= finite_product((letters[letter][i] ** m[i] for i in range(3)), coerce(1))
        numerator += term
    if degree % 2:
        assert numerator == Q5()
        return Q5()
    return numerator / (radius_squared ** (degree // 2))


contraction_checks = 0
sample_exponents = [(0, 0, 0), (2, 0, 0), (4, 0, 0), (2, 2, 0), (1, 0, 0), (1, 1, 1)]
for site_count in range(3):
    for statuses in product(('U', 'D'), repeat=site_count):
        for monomials in product(sample_exponents, repeat=site_count):
            actual = direct_raw_monomial(statuses, monomials)
            contracted = finite_product((status_moment(s, m) for s, m in zip(statuses, monomials)))
            assert actual == coerce(contracted)
            contraction_checks += 1


@dataclass(frozen=True)
class GaussianInteger:
    real: int = 0
    imag: int = 0

    def __add__(self, other):
        other = gaussian(other)
        return GaussianInteger(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __mul__(self, other):
        other = gaussian(other)
        return GaussianInteger(self.real * other.real - self.imag * other.imag,
                               self.real * other.imag + self.imag * other.real)

    __rmul__ = __mul__

    def conjugate(self):
        return GaussianInteger(self.real, -self.imag)

    def __eq__(self, other):
        if isinstance(other, (int, F)):
            return self.imag == 0 and self.real == other
        if isinstance(other, GaussianInteger):
            return self.real == other.real and self.imag == other.imag
        return False


def gaussian(value):
    if isinstance(value, GaussianInteger):
        return value
    assert int(value) == value
    return GaussianInteger(int(value))


# Reconstruct the Bloch matrix from the concrete Pauli matrices.
one, zero = GaussianInteger(1), GaussianInteger()
paulis = [
    [[zero, one], [one, zero]],
    [[zero, GaussianInteger(0, -1)], [GaussianInteger(0, 1), zero]],
    [[one, zero], [zero, GaussianInteger(-1)]],
]
bloch = [[{} for _ in range(2)] for _ in range(2)]
for k in range(3):
    for i in range(2):
        for j in range(2):
            bloch[i][j] = poly_add(bloch[i][j], poly_scale(paulis[k][i][j], variables[k]))
assert all({m: c.conjugate() for m, c in bloch[j][i].items()} == bloch[i][j]
           for i in range(2) for j in range(2))
assert poly_add(bloch[0][0], bloch[1][1]) == {}
norm_squared = {}
for variable in variables:
    norm_squared = poly_add(norm_squared, poly_mul(variable, variable))
for i in range(2):
    for j in range(2):
        entry = {}
        for k in range(2):
            entry = poly_add(entry, poly_mul(bloch[i][k], bloch[k][j]))
        assert entry == (norm_squared if i == j else {})


results = {
    'template_sites': len(sites),
    'full_internal_bonds': len(bonds),
    'external_slots': len(slots),
    'incidence_rows': [
        {'site': x, 'internal': bond_degrees[x], 'external': slot_counts[x],
         'total': bond_degrees[x] + slot_counts[x]}
        for x in sorted(sites)
    ],
    'covered_witness_valid': True,
    'exact_site_moment_checks': 2 * len(exponents),
    'exact_rational_rotation_and_reflection_moment_checks': covariance_checks,
    'exact_direct_product_sum_contraction_checks': contraction_checks,
    'symbolic_bloch_hermitian_square_and_trace_checks': 'passed',
    'method': 'Exact Fraction, Q(sqrt(5)), and Gaussian integer polynomial arithmetic; no numerical tolerance.',
    'scope': 'Finite checks and symbolic sanity checks supplement the definition-and-paper audit; they are not Lean proofs.',
}
output = Path(__file__).with_name('checks.json')
output.write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps({key: value for key, value in results.items() if key != 'incidence_rows'}, indent=2))
