"""Exact audit diagnostics only: no Lean proofs or repository writes."""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random


@dataclass(frozen=True)
class Q5:
    """An element p + q*sqrt(5), with exact rational coefficients."""
    p: F = F(0)
    q: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "p", F(self.p))
        object.__setattr__(self, "q", F(self.q))

    @staticmethod
    def lift(other):
        return other if isinstance(other, Q5) else Q5(other)

    def __add__(self, other):
        other = self.lift(other)
        return Q5(self.p + other.p, self.q + other.q)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.p, -self.q)

    def __sub__(self, other):
        return self + -self.lift(other)

    def __mul__(self, other):
        other = self.lift(other)
        return Q5(self.p * other.p + 5 * self.q * other.q,
                  self.p * other.q + self.q * other.p)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.lift(other)
        denominator = other.p**2 - 5 * other.q**2
        assert denominator
        return self * Q5(other.p / denominator, -other.q / denominator)

    def __pow__(self, exponent):
        assert exponent >= 0
        result = Q5(1)
        for _ in range(exponent):
            result = result * self
        return result


def clean(poly):
    return {key: value for key, value in poly.items() if value}


def constant(dim, value):
    return clean({(0,) * dim: F(value)})


def variable(dim, index):
    key = [0] * dim
    key[index] = 1
    return {tuple(key): F(1)}


def add(*polys):
    out = {}
    for poly in polys:
        for key, value in poly.items():
            out[key] = out.get(key, F(0)) + value
    return clean(out)


def scale(value, poly):
    return clean({key: F(value) * coefficient for key, coefficient in poly.items()})


def multiply(*polys):
    dim = len(next(iter(next(poly for poly in polys if poly))))
    out = constant(dim, 1)
    for poly in polys:
        result = {}
        for left, a in out.items():
            for right, b in poly.items():
                key = tuple(x + y for x, y in zip(left, right))
                result[key] = result.get(key, F(0)) + a * b
        out = clean(result)
    return out


def square(poly):
    return multiply(poly, poly)


def scalar_product(a, b):
    return sum(x * y for x, y in zip(a, b))


results = {}

# Literal numerator coordinates from icoVector, before division by icoRadius.
phi = Q5(F(1, 2), F(1, 2))
radius_sq = phi + 2
vertices = []
for group, sign1, sign2 in product(range(3), (1, -1), (1, -1)):
    a, b = Q5(sign1), sign2 * phi
    vertices.append(((Q5(), a, b), (a, b, Q5()), (b, Q5(), a))[group])
assert len(vertices) == 12 and len(set(vertices)) == 12
assert all(sum((x * x for x in vertex), Q5()) == radius_sq for vertex in vertices)

moments = {}
for exponent in product(range(5), repeat=3):
    degree = sum(exponent)
    if degree > 4:
        continue
    numerator = Q5()
    for vertex in vertices:
        term = Q5(1)
        for coordinate, power in zip(vertex, exponent):
            term = term * coordinate**power
        numerator = numerator + term
    if degree % 2:
        assert numerator == Q5()
        actual = Q5()
    else:
        actual = numerator / (12 * radius_sq**(degree // 2))
    if degree == 0:
        expected = F(1)
    elif any(power % 2 for power in exponent):
        expected = F(0)
    elif degree == 2:
        expected = F(1, 3)
    elif 4 in exponent:
        expected = F(1, 5)
    else:
        expected = F(1, 15)
    assert actual == Q5(expected), (exponent, actual, expected)
    moments[exponent] = expected
results["explicit_U_law"] = {
    "status": "PASS", "distinct_unit_atoms": 12,
    "exact_monomials_through_degree_four": len(moments),
    "arithmetic": "Fraction coefficients in Q(sqrt(5)); odd-degree numerators vanish exactly"
}

# All field coordinates remain formal indeterminates: these are identities for
# arbitrary fields, not a finite selection of field values.
spin = [variable(12, i) for i in range(3)]
fields = [[variable(12, 3 + 3 * j + i) for i in range(3)] for j in range(3)]
weight = multiply(*(add(constant(12, 1),
                        add(*(multiply(spin[i], fields[j][i]) for i in range(3))))
                    for j in range(3)))


def integrate(poly):
    out = {}
    for key, coefficient in poly.items():
        field_key = key[3:]
        out[field_key] = out.get(field_key, F(0)) + coefficient * moments[key[:3]]
    return clean(out)


a = [[variable(9, 3 * j + i) for i in range(3)] for j in range(3)]


def pdot(left, right):
    return add(*(multiply(x, y) for x, y in zip(left, right)))


p = add(pdot(a[0], a[1]), pdot(a[0], a[2]), pdot(a[1], a[2]))
assert integrate(weight) == add(constant(9, 1), scale(F(1, 3), p))
for i in range(3):
    expected = add(scale(5, add(*(a[j][i] for j in range(3)))),
                   multiply(a[0][i], pdot(a[1], a[2])),
                   multiply(a[1][i], pdot(a[0], a[2])),
                   multiply(a[2][i], pdot(a[0], a[1])))
    assert scale(15, integrate(multiply(spin[i], weight))) == expected
results["triple_moment_formulas"] = {
    "status": "PASS", "normalizer_polynomial": True,
    "numerator_coordinate_polynomials": 3,
    "formal_field_variables": 9, "unit_field_assumptions_used": False
}

# Six formal Gram entries. Check that the residual is precisely a linear
# combination of the three unit-length constraints, with polynomial factors.
la, lb, lc, x, y, z = [variable(6, i) for i in range(6)]
one = constant(6, 1)
five = constant(6, 5)
ca, cb, cc = add(five, z), add(five, y), add(five, x)
v_sq = add(multiply(square(ca), la), multiply(square(cb), lb),
           multiply(square(cc), lc), scale(2, multiply(ca, cb, x)),
           scale(2, multiply(ca, cc, y)), scale(2, multiply(cb, cc, z)))
X, Y, Z = add(one, scale(-1, z)), add(one, scale(-1, y)), add(one, scale(-1, x))
sos = add(scale(4, add(square(add(X, scale(-1, Y))),
                            square(add(X, scale(-1, Z))),
                            square(add(Y, scale(-1, Z))))),
          scale(6, multiply(X, Y, Z)))
lhs_residual = add(square(add(constant(6, 9), scale(3, add(x, y, z)))),
                   scale(-1, v_sq), scale(-1, sos))
constraint_residual = add(multiply(add(one, scale(-1, la)), square(ca)),
                          multiply(add(one, scale(-1, lb)), square(cb)),
                          multiply(add(one, scale(-1, lc)), square(cc)))
assert lhs_residual == constraint_residual
results["triple_SOS"] = {"status": "PASS", "exact_Gram_polynomial_identity": True,
                          "only_constraints": "la=lb=lc=1"}

# Enumerate every conditional outcome, including the common support's zero
# atom. Some factorizations use negative C and u; others have zero local atoms.
conditioning_cases = 0
for n, C, u, v in (
    (2, F(-2), [-F(i + 1) for i in range(13)], [F(i + 1) for i in range(13)]),
    (3, F(3, 7), [F(i % 3) for i in range(13)], [F(i % 4) for i in range(13)]),
    (3, F(2), [-F(i % 3) for i in range(13)], [-F(i % 4) for i in range(13)]),
):
    configs = list(product(range(13), repeat=n))
    fibre = lambda config: n == 2 or config[2] == 4
    w = {config: C * u[config[0]] * v[config[1]] if fibre(config)
         else F((config[0] + 2 * config[1] + config[2]) % 5) for config in configs}
    assert all(value >= 0 for value in w.values())
    total = sum(w.values())
    probability = {config: value / total for config, value in w.items()}
    event_mass = sum(value for config, value in probability.items() if fibre(config))
    assert total > 0 and event_mass > 0
    for i, j in product(range(13), repeat=2):
        joint = sum(value for config, value in probability.items()
                    if fibre(config) and config[0] == i and config[1] == j) / event_mass
        first = sum(value for config, value in probability.items()
                    if fibre(config) and config[0] == i) / event_mass
        second = sum(value for config, value in probability.items()
                     if fibre(config) and config[1] == j) / event_mass
        assert joint == first * second
        conditioning_cases += 1
results["conditioning"] = {"status": "PASS", "exact_joint_marginal_comparisons": conditioning_cases,
                             "features": ["n=2", "n=3", "negative factors", "zero atoms", "arbitrary weights off fibre"]}

# Construct and compare the entire polynomial in v for all four k values.
axes = [(F(1), F(0), F(0)), (F(0), F(3, 5), F(4, 5)),
        (F(2, 3), F(1, 3), F(2, 3))]
assert all(scalar_product(e, e) == 1 for e in axes)
mixture_cases = 0
for k in range(4):
    for parameters in product((F(0), F(1, 4), F(1, 2), F(1)), repeat=k):
        padded_parameters = list(parameters) + [F(1, 2)] * (3 - k)
        original_fields = [tuple((2 * parameters[j] - 1) * value for value in axes[j])
                           for j in range(k)]

        def linear_factor(field):
            return add(constant(3, 1), *(scale(value, variable(3, i))
                                        for i, value in enumerate(field)))

        original = constant(3, 1)
        for field in original_fields:
            original = multiply(original, linear_factor(field))
        expanded = {}
        total_t = F(0)
        for signs in product((1, -1), repeat=3):
            t = F(1)
            factors = []
            for j, sign in enumerate(signs):
                t *= padded_parameters[j] if sign == 1 else 1 - padded_parameters[j]
                factors.append(linear_factor(tuple(sign * value for value in axes[j])))
            assert t >= 0
            total_t += t
            expanded = add(expanded, scale(t, multiply(*factors)))
        assert total_t == 1 and original == expanded
        mixture_cases += 1
results["eight_slot_product_mixture"] = {
    "status": "PASS", "exact_polynomial_cases": mixture_cases,
    "k_values": [0, 1, 2, 3], "includes_endpoint_and_zero_weights": True,
    "v_is_formal_and_unrestricted": True
}

# Exact positive-mixture checks, especially zero radius and unequal A's.
rng = random.Random(20261116)
base_vectors = [(F(0), F(0), F(0)), (F(1), F(0), F(0)),
                (F(-1), F(0), F(0)), (F(0), F(3, 5), F(4, 5)),
                (F(2, 3), F(1, 3), F(2, 3))]
estimate_cases = 0
for size, r in product((1, 2, 5), (F(0), F(3, 5), F(1), F(2))):
    for _ in range(8):
        raw_weights = [rng.randrange(5) for _ in range(size)]
        if not sum(raw_weights):
            raw_weights[0] = 1
        t = [F(value, sum(raw_weights)) for value in raw_weights]
        A = [rng.choice((F(1, 2), F(1), F(3), F(100))) for _ in range(size)]
        Y = [tuple(r * value for value in rng.choice(base_vectors)) for _ in range(size)]
        B = [tuple(A[j] * value for value in Y[j]) for j in range(size)]
        denominator = sum(t[j] * A[j] for j in range(size))
        mu = tuple(sum(t[j] * B[j][i] for j in range(size)) / denominator for i in range(3))
        assert denominator >= F(1, 2)
        assert all(scalar_product(y, y) <= r**2 for y in Y)
        assert scalar_product(mu, mu) <= r**2
        estimate_cases += 1
results["positive_mixture_estimate"] = {
    "status": "PASS", "exact_cases": estimate_cases,
    "radii": ["0", "3/5", "1", "2"], "alphabet_sizes": [1, 2, 5],
    "includes_zero_weights_and_A_equal_half": True
}

output = Path(__file__).with_name("checks.json")
output.write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
