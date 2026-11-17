"""Finite diagnostics for the truth sweep; this file contains no Lean proofs."""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from math import sqrt
from pathlib import Path
import json
import random


STEPS = ((1, 0), (-1, 0), (0, 1), (0, -1))
POSITIVE = ((1, 0), (0, 1))


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def square(a, m):
    return set(product(range(a[0] - m, a[0] + m + 1),
                       range(a[1] - m, a[1] + m + 1)))


def internal(w):
    return {(x, add(x, d)) for x in w for d in POSITIVE if add(x, d) in w}


def legs(w):
    return {(x, add(x, d)) for x in w for d in STEPS if add(x, d) not in w}


def exterior(w):
    return {y for _, y in legs(w)}


def reduce(x, l, n):
    return x[0] % l, x[1] % n


def bonds(l, n):
    return {(x, reduce(add(x, d), l, n))
            for x in product(range(l), range(n)) for d in POSITIVE}


def cycle_colour(m, i):
    return 2 if m % 2 and i == m - 1 else i % 2


counts = {}
counts['lift_geometries'] = 0
for m, dl, dn, a in product(range(1, 6), range(3), range(3),
                            ((0, 0), (-7, 4), (11, -10))):
    l, n = 2 * m + 3 + dl, 2 * m + 3 + dn
    q, h = square(a, m), square(a, m + 1)
    p = lambda z: reduce(z, l, n)
    image = {p(x) for x in q}
    assert len({p(x) for x in h}) == len(h)
    torus_edges = {frozenset(e) for e in bonds(l, n)}
    assert len(torus_edges) == 2 * l * n
    assert {frozenset((p(x), p(y))) for x, y in internal(q)} == {
        e for e in torus_edges if e <= image}
    assert {frozenset((p(x), p(y))) for x, y in legs(q)} == {
        e for e in torus_edges if len(e & image) == 1}
    assert all((p(x) in image) == (x in q) for x in h)
    assert all(frozenset((p(x), p(add(x, d)))) in torus_edges
               for x in h for d in STEPS)
    # Each full-halo exterior residue has a unique exterior lift at distance one.
    for y in {p(x) for x in h} - image:
        lifts = [x for x in h if p(x) == y]
        assert len(lifts) == 1 and lifts[0] not in q
        assert min(max(abs(lifts[0][0] - x[0]), abs(lifts[0][1] - x[1]))
                   for x in q) == 1
    counts['lift_geometries'] += 1

counts['square_edge_counts'] = 0
for a, m in product(((0, 0), (-10, 3), (9, -12)), range(11)):
    assert len(internal(square(a, m))) == 2 * (2 * m + 1) * (2 * m)
    counts['square_edge_counts'] += 1

counts['range_inclusions'] = 0
for l, n, m, a in product(range(3, 10), range(3, 10), range(11),
                           ((0, 0), (7, -8))):
    q = {reduce(x, l, n) for x in square(a, m)}
    h = {reduce(x, l, n) for x in square(a, m + 1)}
    nearest = {reduce(add(x, d), l, n) for x in q for d in STEPS} - q
    assert nearest <= h - q
    counts['range_inclusions'] += 1

counts['nested_finite_volumes'] = 0
ambient = sorted(square((0, 0), 1))
for labels in product(range(3), repeat=len(ambient)):
    w = {x for x, label in zip(ambient, labels) if label >= 1}
    v = {x for x, label in zip(ambient, labels) if label == 2}
    assert exterior(v) - w <= exterior(w)
    assert all(any(max(abs(z[0] - x[0]), abs(z[1] - x[1])) <= 1 for x in w)
               for z in exterior(w))
    counts['nested_finite_volumes'] += 1


@dataclass(frozen=True)
class Q5:
    """Exact a+b*sqrt(5), used only for finite arithmetic diagnostics."""
    a: F = F(0)
    b: F = F(0)

    def __add__(self, other):
        other = other if isinstance(other, Q5) else Q5(F(other))
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        other = other if isinstance(other, Q5) else Q5(F(other))
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = other if isinstance(other, Q5) else Q5(F(other))
        den = other.a * other.a - 5 * other.b * other.b
        assert den
        return self * Q5(other.a / den, -other.b / den)

    def sign(self):
        if not self.b:
            return (self.a > 0) - (self.a < 0)
        if not self.a:
            return (self.b > 0) - (self.b < 0)
        if self.a > 0 and self.b > 0:
            return 1
        if self.a < 0 and self.b < 0:
            return -1
        delta = self.a * self.a - 5 * self.b * self.b
        return ((delta > 0) - (delta < 0)) * ((self.a > 0) - (self.a < 0))

    def approx(self):
        return float(self.a) + float(self.b) * sqrt(5)


def prod(values):
    out = Q5(F(1))
    for v in values:
        out = out * v
    return out


letters = list(product(range(3), range(2), range(2)))
letter_index = {x: i for i, x in enumerate(letters)}
anti = [letter_index[(k, 1 - a, 1 - b)] for k, a, b in letters]
phi = Q5(F(1, 2), F(1, 2))
radius_sq = phi + 2
vectors = []
for colour in range(3):
    vs = []
    for k, a, b in letters:
        aa, bb = Q5(F((-1) ** a)), ((-1) ** b) * phi
        v = (Q5(), aa, bb) if k == 0 else ((aa, bb, Q5()) if k == 1 else (bb, Q5(), aa))
        for _ in range(colour):
            x, y, z = v
            v = (F(99, 101) * x - F(20, 101) * y,
                 F(20, 101) * x + F(99, 101) * y, z)
        vs.append(v)
    assert len(set(vs)) == 12
    assert all(vs[anti[i]] == tuple(-x for x in v) for i, v in enumerate(vs))
    vectors.append(vs)

factors = {}
positive_margins = []
for i, j, a, b in product(range(3), range(3), range(12), range(12)):
    dot = sum(x * y for x, y in zip(vectors[i][a], vectors[j][b])) / radius_sq
    factors[(i, j, a, b, 1)] = Q5(F(1)) + dot
    factors[(i, j, a, b, -1)] = Q5(F(1)) - dot
    if i != j:
        for sign in (1, -1):
            margin = factors[(i, j, a, b, sign)]
            assert margin.sign() == 1
            positive_margins.append(margin)
counts['exact_cross_frame_positive_factors'] = len(positive_margins)
counts['exact_injective_antipodal_frames'] = 3
min_margin = min(positive_margins, key=lambda x: x.approx())
expected = Q5(F(5, 505), F(-1, 505))
assert min_margin == expected
assert all((margin - expected).sign() >= 0 for margin in positive_margins)
counts['minimum_cross_frame_factor'] = '(5-sqrt(5))/505'

rng = random.Random(20261116)
counts['gauge_weight_ratio_placements'] = 0
counts['gauge_normalized_one_site_fibres'] = 0
for m, l, n, centre in ((1, 5, 5, (4, -3)), (1, 6, 7, (-5, 9)), (2, 7, 8, (9, -11))):
    p = lambda z: reduce(z, l, n)
    colour = lambda x: (cycle_colour(l, x[0]) + cycle_colour(n, x[1])) % 3
    q, h = square(centre, m), square(centre, m + 1)
    image = {p(x) for x in q}
    es = sorted(bonds(l, n))
    ints, crossings = sorted(internal(q)), sorted(legs(q))
    assert all(colour(x) != colour(y) for x, y in es)
    fixed = {x: rng.randrange(12) for x in product(range(l), range(n))}

    def flip(z, a):
        return anti[a] if (z[0] + z[1]) % 2 else a

    def torus_raw(sigma):
        return F(1, 12) ** (l * n) * prod(
            factors[(colour(x), colour(y), sigma[x], sigma[y], -1)] for x, y in es)

    def plane_raw(sigma):
        # Only the finite halo pulls back sigma; the extension elsewhere is fixed.
        boundary = {z: flip(z, fixed[p(z)]) for z in h - q}
        transformed = {z: flip(z, sigma[p(z)]) for z in q}
        return F(1, 12) ** len(q) * prod(
            [factors[(colour(p(x)), colour(p(y)), transformed[x], transformed[y], 1)]
             for x, y in ints] +
            [factors[(colour(p(x)), colour(p(y)), transformed[x], boundary[y], 1)]
             for x, y in crossings])

    ratios = []
    for _ in range(4):
        sigma = dict(fixed)
        sigma.update({x: rng.randrange(12) for x in image})
        tw, pw = torus_raw(sigma), plane_raw(sigma)
        assert tw.sign() == pw.sign() == 1
        ratios.append(tw / pw)
    assert all(r == ratios[0] for r in ratios)
    counts['gauge_weight_ratio_placements'] += 1

    tws, pws = [], []
    for a in range(12):
        sigma = dict(fixed)
        sigma[p(centre)] = a
        tws.append(torus_raw(sigma))
        pws.append(plane_raw(sigma))
    assert all(tw / sum(tws) == pw / sum(pws) for tw, pw in zip(tws, pws))
    counts['gauge_normalized_one_site_fibres'] += 1

output = Path(__file__).with_name('finite-checks.json')
output.write_text(json.dumps({'status': 'PASS', 'checks': counts}, indent=2) + '\n')
print(output.read_text(), end='')
