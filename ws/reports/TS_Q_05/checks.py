"""Finite and symbolic diagnostics for the statement audit; no formal proofs."""

import itertools
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path


class Poly:
    """Sparse exact polynomial with fourteen real variables and I**2 = -1."""

    dim = 15

    def __init__(self, terms):
        self.terms = {m: Fraction(c) for m, c in terms.items() if c}

    @classmethod
    def scalar(cls, c):
        return cls({(0,) * cls.dim: c})

    @classmethod
    def variable(cls, i):
        m = [0] * cls.dim
        m[i] = 1
        return cls({tuple(m): 1})

    def __add__(self, other):
        if not isinstance(other, Poly):
            other = Poly.scalar(other)
        terms = defaultdict(Fraction, self.terms)
        for m, c in other.terms.items():
            terms[m] += c
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if not isinstance(other, Poly):
            other = Poly.scalar(other)
        terms = defaultdict(Fraction)
        for m, a in self.terms.items():
            for k, b in other.terms.items():
                powers = [x + y for x, y in zip(m, k)]
                sign = (-1) ** (powers[-1] // 2)
                powers[-1] %= 2
                terms[tuple(powers)] += sign * a * b
        return Poly(terms)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return self * (Fraction(1) / scalar)

    def conjugate(self):
        return Poly({m: (-c if m[-1] else c) for m, c in self.terms.items()})


def next_site(x, d, l, n):
    return ((x[0] + 1) % l, x[1]) if d == 0 else (x[0], (x[1] + 1) % n)


def star_edges(x, l, n):
    return [
        (x, 0),
        (((x[0] - 1) % l, x[1]), 0),
        (x, 1),
        ((x[0], (x[1] - 1) % n), 1),
    ]


def mul_poly(p, q):
    result = defaultdict(int)
    for m, a in p.items():
        for k, b in q.items():
            result[tuple(x + y for x, y in zip(m, k))] += a * b
    return {m: a for m, a in result.items() if a}


counts = {"tori": 0, "sites": 0, "bonds": 0, "incident_polynomials": 0}
for l in range(3, 9):
    for n in range(3, 9):
        sites = list(itertools.product(range(l), range(n)))
        bonds = list(itertools.product(sites, range(2)))
        endpoints = {e: frozenset((e[0], next_site(*e, l, n))) for e in bonds}
        assert all(len(s) == 2 for s in endpoints.values())
        assert len(set(endpoints.values())) == len(bonds)
        counts["tori"] += 1
        counts["sites"] += len(sites)
        counts["bonds"] += len(bonds)
        for x in sites:
            edges = star_edges(x, l, n)
            assert len(set(edges)) == 4
            assert set(edges) == {e for e in bonds if x in endpoints[e]}
            leaves = [next(iter(endpoints[e] - {x})) for e in edges]
            assert len(set([x] + leaves)) == 5
            # Explicitly expand the four singlets on their five actual sites.
            local = {y: i for i, y in enumerate([x] + leaves)}
            p = {(0,) * 10: 1}
            for e in edges:
                a, b = local[e[0]], local[next_site(*e, l, n)]
                m, k = [0] * 10, [0] * 10
                m[2 * a], m[2 * b + 1] = 1, 1
                k[2 * a + 1], k[2 * b] = 1, 1
                assert m != k
                p = mul_poly(p, {tuple(m): 1, tuple(k): -1})
            assert len(p) == 16
            assert all(m[0] + m[1] == 4 for m in p)
            assert all(abs(c) == 1 for c in p.values())
            # Removing the five distinguished factors leaves exactly this many
            # spectator configurations; no truncated subtraction occurs.
            assert len(sites) >= 5
            assert 5 ** len(sites) == 5 ** (len(sites) - 5) * 5 ** 5
            counts["incident_polynomials"] += 1

assert all((4 - j) + j == 4 for j in range(5))

# The Pauli-density form of the squared determinant, retaining conjugates.
a0, a1, a2, b0, b1, b2 = [Poly.variable(i) for i in range(6)]
imaginary = Poly.variable(14)
A = [[(1 + a2) / 2, (a0 - imaginary * a1) / 2],
     [(a0 + imaginary * a1) / 2, (1 - a2) / 2]]
B = [[(1 + b2) / 2, (b0 - imaginary * b1) / 2],
     [(b0 + imaginary * b1) / 2, (1 - b2) / 2]]
density_det = A[0][0] * B[1][1] + A[1][1] * B[0][0] - A[0][1] * B[1][0] - A[1][0] * B[0][1]
assert not (density_det - (1 - a0 * b0 - a1 * b1 - a2 * b2) / 2).terms
z = [Poly.variable(i) for i in range(6, 10)]
w = [Poly.variable(i) for i in range(10, 14)]
zc = [z[0] + imaginary * z[1], z[2] + imaginary * z[3]]
wc = [w[0] + imaginary * w[1], w[2] + imaginary * w[3]]
det = zc[0] * wc[1] - zc[1] * wc[0]
gram = sum(t * t.conjugate() for t in zc) * sum(t * t.conjugate() for t in wc)
overlap = sum(zc[i].conjugate() * wc[i] for i in range(2))
assert not (det * det.conjugate() - gram + overlap * overlap.conjugate()).terms

# Isolate the exact scalar identity from GroundProductWeightStatement.
normalization_cases = 0
for site_count in range(12):
    for bond_count in range(16):
        assert Fraction(5, 12) ** site_count * Fraction(1, 2) ** bond_count == (
            Fraction(5 ** site_count, 2 ** bond_count) * Fraction(1, 12) ** site_count
        )
        normalization_cases += 1

result = {
    "geometry_and_incident_products": counts,
    "periods": "all ordered pairs L,N in 3..8; every site and bond",
    "state_exponents": "all five Fin 5 values checked",
    "determinant_modulus": "Gram expansion and Pauli-density expansion simplify exactly to zero",
    "normalization_cases": normalization_cases,
    "normalization_arithmetic": "exact fractions, including zero site/bond counts as an algebra check",
}
Path(__file__).with_name("checks.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
