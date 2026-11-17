"""Finite arithmetic checks for the truth sweep; no Lean proofs or repo writes."""

from fractions import Fraction as F
from itertools import product
from math import comb, prod, sqrt
from random import Random


class Q5:
    """Exact a + b*sqrt(5)."""

    def __init__(self, a=0, b=0):
        if isinstance(a, Q5):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = F(a), F(b)

    def __add__(self, other):
        other = Q5(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -Q5(other)

    def __rsub__(self, other):
        return Q5(other) - self

    def __mul__(self, other):
        other = Q5(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Q5(other)
        denominator = other.a**2 - 5 * other.b**2
        assert denominator != 0
        return self * Q5(other.a / denominator, -other.b / denominator)

    def __pow__(self, n):
        result = Q5(1)
        for _ in range(n):
            result *= self
        return result

    def __eq__(self, other):
        other = Q5(other)
        return (self.a, self.b) == (other.a, other.b)

    def __repr__(self):
        return str(self.a) if not self.b else f"({self.a} + {self.b}*sqrt(5))"


class CQ:
    """Exact Gaussian rationals for polynomial coefficients and spinors."""

    def __init__(self, re=0, im=0):
        if isinstance(re, CQ):
            self.re, self.im = re.re, re.im
        else:
            self.re, self.im = F(re), F(im)

    def __add__(self, other):
        other = CQ(other)
        return CQ(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return CQ(-self.re, -self.im)

    def __sub__(self, other):
        return self + -CQ(other)

    def __rsub__(self, other):
        return CQ(other) - self

    def __mul__(self, other):
        other = CQ(other)
        return CQ(self.re * other.re - self.im * other.im,
                  self.re * other.im + self.im * other.re)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = CQ(other)
        numerator = self * other.conjugate()
        return CQ(numerator.re / other.norm_sq(), numerator.im / other.norm_sq())

    def __pow__(self, n):
        result = CQ(1)
        for _ in range(n):
            result *= self
        return result

    def conjugate(self):
        return CQ(self.re, -self.im)

    def norm_sq(self):
        return self.re**2 + self.im**2

    def __eq__(self, other):
        other = CQ(other)
        return (self.re, self.im) == (other.re, other.im)


def poly_add(p, q):
    result = dict(p)
    for exponent, coefficient in q.items():
        result[exponent] = result.get(exponent, CQ()) + coefficient
    return {e: c for e, c in result.items() if c != 0}


def poly_mul(p, q):
    result = {}
    for e, c in p.items():
        for f, d in q.items():
            exponent = tuple(a + b for a, b in zip(e, f))
            result[exponent] = result.get(exponent, CQ()) + c * d
    return {e: c for e, c in result.items() if c != 0}


def poly_pow(p, n):
    result = {(0, 0, 0): CQ(1)}
    for _ in range(n):
        result = poly_mul(result, p)
    return result


ONE = {(0, 0, 0): CQ(1)}
X = {(1, 0, 0): CQ(1)}
YI = {(0, 1, 0): CQ(0, 1)}
Z = {(0, 0, 1): CQ(1)}


def kernel(j, k):
    # This conditional and all exponents match Q.Definitions.quarticKernel.
    low, high = (j, k) if j <= k else (k, j)
    transverse = poly_add(X, {e: c if j <= k else -c for e, c in YI.items()})
    factors = [
        {(0, 0, 0): CQ(F(1, 16))},
        poly_pow(poly_add(ONE, Z), 4 - high),
        poly_pow(poly_add(ONE, {e: -c for e, c in Z.items()}), low),
        poly_pow(transverse, high - low),
    ]
    result = ONE
    for factor in factors:
        result = poly_mul(result, factor)
    return result


PHI = Q5(F(1, 2), F(1, 2))
RADIUS_SQ = PHI + 2
RAW_VERTICES = []
for group, sign_a, sign_b in product(range(3), (1, -1), (1, -1)):
    a, b = Q5(sign_a), sign_b * PHI
    RAW_VERTICES.append(((Q5(), a, b), (a, b, Q5()), (b, Q5(), a))[group])


def monomial_moment(exponent):
    numerator = sum(prod(v**n for v, n in zip(vertex, exponent))
                    for vertex in RAW_VERTICES)
    degree = sum(exponent)
    if degree % 2:
        assert numerator == 0
        return Q5()
    return numerator / (12 * RADIUS_SQ ** (degree // 2))


def polynomial_moment(p):
    real = sum(c.re * monomial_moment(e) for e, c in p.items())
    imag = sum(c.im * monomial_moment(e) for e, c in p.items())
    return real, imag


def polynomial_eval(p, v):
    return sum(c * prod(CQ(x)**n for x, n in zip(v, e)) for e, c in p.items())


def monomial(j, z):
    return z[0] ** (4 - j) * z[1] ** j


def exact_checks():
    assert PHI**2 == PHI + 1
    assert RADIUS_SQ**2 == 5 * PHI**2
    exponents = [e for e in product(range(5), repeat=3) if sum(e) <= 4]
    moments = {e: monomial_moment(e) for e in exponents}
    assert len(moments) == 35
    for e, value in moments.items():
        if any(n % 2 for n in e):
            expected = 0
        elif sum(e) == 0:
            expected = 1
        elif sum(e) == 2:
            expected = F(1, 3)
        elif 4 in e:
            expected = F(1, 5)
        else:
            expected = F(1, 15)
        assert value == expected, (e, value, expected)
    print("EXACT: all 35 monomial moments of degree <= 4 agree with the paper.")

    diagonal = []
    for j, k in product(range(5), repeat=2):
        p = kernel(j, k)
        assert max(map(sum, p)) <= 4
        expected = F(1, 5 * comb(4, j)) if j == k else 0
        assert polynomial_moment(p) == (Q5(expected), Q5()), (j, k)
        if j == k:
            diagonal.append(str(expected))
    print("EXACT: all 25 kernel degree bounds and all 25 kernel moments pass.")
    print("Diagonal moments:", ", ".join(diagonal))

    spinors = [(CQ(1), CQ()), (CQ(), CQ(1)), (CQ(0, 1), CQ())]
    for q in [(1, 2, 3), (F(1, 2), F(1, 3), F(-1, 4)),
              (0, 0, F(2, 3)), (-2, 1, 4), (F(3, 5), 0, F(4, 5))]:
        denominator = 1 + sum(F(t)**2 for t in q)
        coordinates = [(2 - denominator) / denominator] + [2 * F(t) / denominator for t in q]
        spinors.append((CQ(*coordinates[:2]), CQ(*coordinates[2:])))
    for z in spinors:
        assert sum(t.norm_sq() for t in z) == 1
        cross = z[0].conjugate() * z[1]
        v = (2 * cross.re, 2 * cross.im, z[0].norm_sq() - z[1].norm_sq())
        assert sum(t*t for t in v) == 1
        assert z[0] * z[1].conjugate() == CQ(v[0], -v[1]) / 2
        for j, k in product(range(5), repeat=2):
            assert monomial(j, z).conjugate() * monomial(k, z) == polynomial_eval(kernel(j, k), v)
    print(f"EXACT: all 25 kernel evaluations pass on {len(spinors)} compatible rational spinors, including both poles and complex phases.")


def numeric_checks():
    rng = Random(20261116)
    phi = (1 + sqrt(5)) / 2
    radius = sqrt(phi + 2)
    frame = []
    for group, sign_a, sign_b in product(range(3), (1, -1), (1, -1)):
        a, b = sign_a, sign_b * phi
        v = [(0, a, b), (a, b, 0), (b, 0, a)][group]
        x, y, t = (coordinate / radius for coordinate in v)
        spinor = (complex(sqrt((1 + t) / 2)), complex(x, y) / sqrt(2 * (1 + t)))
        frame.append((1 / 12, spinor))

    # Repeated atoms, signed weights, and spinors of norm two still resolve.
    signed = []
    for index, (weight, spinor) in enumerate(frame):
        phase = complex(0, 1) ** (index % 4)
        scaled = tuple(2 * phase * coordinate for coordinate in spinor)
        signed.extend([(2 * weight / 2**8, scaled), (-weight / 2**8, scaled)])
    extra_zero = frame + [(-7, (0j, 0j))]
    frames = [frame, signed, extra_zero]

    worst_gram = 0.0
    worst_resolution = 0.0
    for atoms in frames:
        for j, k in product(range(5), repeat=2):
            value = sum(5 * w * monomial(j, z).conjugate() * monomial(k, z) for w, z in atoms)
            expected = 1 / comb(4, j) if j == k else 0
            worst_gram = max(worst_gram, abs(value - expected))
        for _ in range(10):
            p = [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(5)]
            value = sum(5 * w * abs(sum(p[j] * monomial(j, z) for j in range(5)))**2 for w, z in atoms)
            expected = sum(abs(p[j])**2 / comb(4, j) for j in range(5))
            worst_resolution = max(worst_resolution, abs(value - expected))
    assert worst_gram < 1e-12 and worst_resolution < 1e-11
    print(f"NUMERIC: Gram and norm identities pass on alphabets of sizes 12, 24, 13; max errors {worst_gram:.3g}, {worst_resolution:.3g}.")

    # Direct product sums for the finite tensor algebra, with unequal alphabets.
    two_site_frames = [frame, signed]
    states = list(product(range(5), repeat=2))
    coefficients = {s: complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for s in states}
    value = 0.0
    for atoms in product(*two_site_frames):
        weight = prod(5 * a[0] for a in atoms)
        evaluation = sum(c * prod(sqrt(comb(4, j)) * monomial(j, atom[1])
                                 for j, atom in zip(s, atoms))
                         for s, c in coefficients.items())
        value += weight * abs(evaluation)**2
    expected = sum(abs(c)**2 for c in coefficients.values())
    assert abs(value - expected) < 1e-10
    print(f"NUMERIC: direct two-site tensor sum with alphabets 12 x 24 passes; absolute error {abs(value - expected):.3g}.")

    # Nine sites (the smallest allowed torus), sparse entangled state. Compute
    # the product sum by exact finite-sum factorization rather than 12^9 loops.
    configurations = [(0,) * 9, (4,) * 9, tuple(i % 5 for i in range(9)), tuple((2*i + 1) % 5 for i in range(9))]
    coefficients = [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in configurations]
    site_frames = [frames[i % 3] for i in range(9)]
    grams = []
    for atoms in site_frames:
        grams.append({(j, k): sum(5 * w * sqrt(comb(4, j) * comb(4, k)) *
                                  monomial(j, z).conjugate() * monomial(k, z)
                                  for w, z in atoms)
                      for j, k in product(range(5), repeat=2)})
    value = sum(coefficients[a].conjugate() * coefficients[b] *
                prod(grams[x][(s[x], t[x])] for x in range(9))
                for a, s in enumerate(configurations) for b, t in enumerate(configurations))
    expected = sum(abs(c)**2 for c in coefficients)
    assert abs(value - expected) < 1e-10
    print(f"NUMERIC: factorized nine-site tensor check with dependent sizes 12/24/13 passes; absolute error {abs(value - expected):.3g}.")


if __name__ == '__main__':
    exact_checks()
    numeric_checks()
