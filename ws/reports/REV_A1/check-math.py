#!/usr/bin/env python3
"""Exact finite checks for REV_A1. Uses only the Python standard library.

This checks arithmetic and finite examples; the quantified proofs are in
the section files. It does not verify any computational input from lane C.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent
PLAN = Path('/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md')
INTERFACES = PLAN.with_name('interfaces.tex')
LABELS = [
    'd:model', 't:main', 'd:poly', 'l:edge', 'l:divisibility',
    'p:toruskernel', 'l:star', 'd:frame', 'l:tight', 'l:threeframes',
    'l:colour', 'l:qmod', 'd:framemodel', 'l:quantumfibre', 't:QD',
    'l:planeenergy', 'l:boxlift',
]


def statements(text):
    return [(m.group(2), m.group(0)) for m in re.finditer(
        r'\\begin\{(definition|theorem|lemma|proposition)\}'
        r'\\label\{([^}]+)\}.*?\\end\{\1\}', text, re.S)]


def check_contract():
    plan = dict(statements(PLAN.read_text()))
    interfaces = dict(statements(INTERFACES.read_text()))
    text = '\n'.join((ROOT / name).read_text() for name in
                     ['sec1-result.tex', 'sec3-quantum-frames.tex'])
    actual = statements(text)
    assert [label for label, _ in actual] == LABELS
    for label, statement in actual:
        assert statement == plan[label], label
        if label in interfaces:
            assert statement == interfaces[label], label
    labels = set(re.findall(r'\\label\{([^}]+)\}', text))
    refs = set(re.findall(r'\\(?:eq)?ref\{([^}]+)\}', text))
    external = refs - labels
    assert external == {
        'd:moment', 'l:moments', 'l:density', 't:inputs', 't:rec',
        't:cutMOS', 't:mainW',
    }, external
    print('PASS: 17 statements match PLAN.md verbatim, in order; all seven')
    print('      applicable interface exports match interfaces.tex verbatim.')
    print('PASS: external citations are exactly the seven permitted dependencies.')


@dataclass(frozen=True)
class Q5:
    """a + b sqrt(5), with exact rational coefficients and exact ordering."""

    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))

    @staticmethod
    def cast(value):
        return value if isinstance(value, Q5) else Q5(value)

    def __add__(self, other):
        other = self.cast(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-self.cast(other))

    def __rsub__(self, other):
        return self.cast(other) - self

    def __mul__(self, other):
        other = self.cast(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        denominator = other.a**2 - 5 * other.b**2
        assert denominator != 0
        return self * Q5(other.a / denominator, -other.b / denominator)

    def __rtruediv__(self, other):
        return self.cast(other) / self

    def __pow__(self, n):
        assert isinstance(n, int)
        if n < 0:
            return (Q5(1) / self) ** (-n)
        answer = Q5(1)
        base = self
        while n:
            if n % 2:
                answer *= base
            base *= base
            n //= 2
        return answer

    def sign(self):
        if self.b == 0:
            return (self.a > 0) - (self.a < 0)
        if self.a == 0:
            return (self.b > 0) - (self.b < 0)
        if self.a > 0 and self.b > 0:
            return 1
        if self.a < 0 and self.b < 0:
            return -1
        difference = self.a**2 - 5 * self.b**2
        # A nonzero rational ratio cannot have square 5.
        assert difference != 0
        return (1 if difference > 0 else -1) * (1 if self.a > 0 else -1)

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __le__(self, other):
        return (self - other).sign() <= 0


ZERO = Q5(0)
ONE = Q5(1)
PHI = Q5(F(1, 2), F(1, 2))
R2 = PHI + 2
B = Q5(F(5, 505), F(-1, 505))
T = ((F(99, 101), F(-20, 101), F(0)),
     (F(20, 101), F(99, 101), F(0)),
     (F(0), F(0), F(1)))


def dot(u, v):
    return sum((x * y for x, y in zip(u, v)), ZERO)


def rotate(u):
    return tuple(dot(row, u) for row in T)


def prod(values):
    answer = ONE
    for value in values:
        answer *= value
    return answer


def check_frames():
    assert PHI**2 == PHI + 1
    assert B == 2 / (101 * R2)
    assert ZERO < B < ONE
    assert ZERO < B / (2 - B) < ONE
    for i in range(3):
        for j in range(3):
            assert dot(T[i], T[j]) == Q5(int(i == j))
    det = (T[0][0] * T[1][1] - T[0][1] * T[1][0]) * T[2][2]
    assert det == 1

    vertices = []
    for e, d in product([-1, 1], repeat=2):
        vertices += [(ZERO, Q5(e), d * PHI),
                     (Q5(e), d * PHI, ZERO),
                     (d * PHI, ZERO, Q5(e))]
    frames = [vertices]
    for _ in range(2):
        frames.append([rotate(v) for v in frames[-1]])

    exponents = [ex for ex in product(range(5), repeat=3) if sum(ex) <= 4]
    assert len(exponents) == 35
    moments = []
    for frame in frames:
        assert len(set(frame)) == 12
        assert {tuple(-x for x in v) for v in frame} == set(frame)
        assert all(dot(v, v) == R2 for v in frame)
        current = {}
        for ex in exponents:
            degree = sum(ex)
            raw = sum((prod(v[i]**ex[i] for i in range(3))
                       for v in frame), ZERO) / 12
            if degree % 2:
                assert raw == ZERO
                value = ZERO
            else:
                value = raw / R2**(degree // 2)
            if degree == 0:
                expected = F(1)
            elif any(e % 2 for e in ex):
                expected = F(0)
            elif degree == 2:
                expected = F(1, 3)
            elif degree == 4:
                expected = F(1, 5) if max(ex) == 4 else F(1, 15)
            else:
                raise AssertionError(ex)
            assert value == Q5(expected), (ex, value, expected)
            current[ex] = expected
        moments.append(current)

    lower_bounds = []
    for i, j in product(range(3), repeat=2):
        if i == j:
            continue
        assert not (set(frames[i]) & set(frames[j]))
        for u, v in product(frames[i], frames[j]):
            scalar = dot(u, v) / R2
            for sign in [-1, 1]:
                factor = 1 + sign * scalar
                assert B <= factor <= 2 - B
                lower_bounds.append(factor)
    assert len(lower_bounds) == 1728
    assert min(lower_bounds) == B
    u = (ZERO, ONE, PHI)
    assert 1 - dot(u, rotate(u)) / R2 == B
    print('PASS: exact SO(3), antipodality, unit length, and all 35 moments')
    print('      through degree four for each of the three frames.')
    print('PASS: all 1,728 signed cross-frame bond factors are in [b,2-b];')
    print('      the exact minimum is (5-sqrt(5))/505 and is attained.')

    # Exact finite Gram calculation from the explicit P_jk polynomials.
    for moment in moments:
        for j in range(5):
            for k in range(j, 5):
                real = F(0)
                imag = F(0)
                for u in range(5 - k):
                    for v in range(j + 1):
                        for h in range(k - j + 1):
                            ex = (k - j - h, h, u + v)
                            c = F(comb(4 - k, u) * comb(j, v)
                                  * (-1)**v * comb(k - j, h), 16)
                            c *= moment[ex]
                            if h % 4 == 0:
                                real += c
                            elif h % 4 == 1:
                                imag += c
                            elif h % 4 == 2:
                                real -= c
                            else:
                                imag -= c
                assert imag == 0
                assert 5 * real == (F(1, comb(4, j)) if j == k else 0)
    print('PASS: coherent monomial Gram matrices give diag(1,1/4,1/6,1/4,1)')
    print('      after multiplication by 5, in all three frames.')
    return frames


def transpose(a):
    return list(map(list, zip(*a)))


def matmul(a, b):
    columns = transpose(b)
    return [[sum(x * y for x, y in zip(row, column))
             for column in columns] for row in a]


def rank(a):
    a = [[F(x) for x in row] for row in a]
    row = 0
    for column in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][column]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        value = a[row][column]
        a[row] = [x / value for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][column]:
                value = a[i][column]
                a[i] = [x - value * y for x, y in zip(a[i], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def check_cartan():
    pairs4 = list(product(range(5), repeat=2))
    delta = [[int(j + k == r) for j, k in pairs4] for r in range(9)]
    mult = [[0] * 16 for _ in range(25)]
    for column, (j, k) in enumerate(product(range(4), repeat=2)):
        mult[pairs4.index((j, k + 1))][column] = 1
        mult[pairs4.index((j + 1, k))][column] = -1
    assert rank(delta) == 9
    assert rank(mult) == 16
    assert all(x == 0 for row in matmul(delta, mult) for x in row)
    source_norm = [F(1, comb(4, j) * comb(4, k)) for j, k in pairs4]
    target_norm = [F(1, comb(8, r)) for r in range(9)]
    adjoint = [[F(delta[r][column]) * target_norm[r] / source_norm[column]
                for r in range(9)] for column in range(25)]
    assert matmul(delta, adjoint) == [
        [int(i == j) for j in range(9)] for i in range(9)]
    projection = matmul(adjoint, delta)
    assert matmul(projection, projection) == projection
    assert all(source_norm[i] * projection[i][j]
               == source_norm[j] * projection[j][i]
               for i in range(25) for j in range(25))
    assert all(x == 0 for row in matmul(projection, mult) for x in row)
    print('PASS: Cartan map rank 9, determinant multiplication rank 16,')
    print('      Delta*q=0, and adjoint/projection identities in the specified norms.')


def a_cycle(m, i):
    assert 0 <= i < m
    return 2 if m % 2 and i == m - 1 else i % 2


def torus_neighbours(x, periods):
    l, n = periods
    i, j = x
    return {((i + 1) % l, j), ((i - 1) % l, j),
            (i, (j + 1) % n), (i, (j - 1) % n)}


def colour(x, periods):
    l, n = periods
    return (a_cycle(l, x[0]) + a_cycle(n, x[1])) % 3


DIRECTIONS = [(1, 0), (-1, 0), (0, 1), (0, -1)]


def plane_neighbours(z):
    return {(z[0] + d[0], z[1] + d[1]) for d in DIRECTIONS}


def check_geometry(frames):
    for l, n in product(range(3, 13), repeat=2):
        periods = (l, n)
        edges = set()
        for x in product(range(l), range(n)):
            neighbours = torus_neighbours(x, periods)
            assert len(neighbours) == 4 and x not in neighbours
            assert all(colour(x, periods) != colour(y, periods) for y in neighbours)
            edges.update(frozenset([x, y]) for y in neighbours)
        assert len(edges) == 2 * l * n
    print('PASS: simple four-regular tori and proper colouring for all 100')
    print('      period pairs 3<=L,N<=12, including period three and all parities.')

    count = 0
    gauge_bonds = 0
    for m in range(1, 6):
        for l, n in product(range(2 * m + 3, 2 * m + 7), repeat=2):
            periods = (l, n)
            def p(z):
                return (z[0] % l, z[1] % n)
            for centre in [(0, 0), (l - 1, n - 1), (-l - 1, -n + 1)]:
                def square(radius):
                    return {(centre[0] + i, centre[1] + j)
                            for i, j in product(range(-radius, radius + 1), repeat=2)}
                qprime = square(m)
                aprime = square(m + 1)
                assert len({p(z) for z in aprime}) == len(aprime)
                q = {p(z) for z in qprime}
                plane_inside = {frozenset([p(z), p(w)]) for z in qprime
                                for w in plane_neighbours(z) if w in qprime}
                torus_inside = {frozenset([x, y]) for x in q
                                for y in torus_neighbours(x, periods) if y in q}
                assert plane_inside == torus_inside
                assert len(plane_inside) == 2 * (2 * m + 1) * (2 * m)
                plane_crossing = {(p(z), p(w)) for z in qprime
                                  for w in plane_neighbours(z) if w not in qprime}
                torus_crossing = {(x, y) for x in q
                                  for y in torus_neighbours(x, periods) if y not in q}
                assert plane_crossing == torus_crossing
                count += 1
                # Factor-by-factor exact local gauge, including wraparound boxes.
                for z in qprime:
                    for w in plane_neighbours(z):
                        c_z, c_w = colour(p(z), periods), colour(p(w), periods)
                        assert c_z != c_w
                        sz = frames[c_z][(7 * z[0] + 5 * z[1]) % 12]
                        sw = frames[c_w][(7 * w[0] + 5 * w[1]) % 12]
                        ez = 1 if (z[0] + z[1]) % 2 == 0 else -1
                        ew = 1 if (w[0] + w[1]) % 2 == 0 else -1
                        assert ez * ew == -1
                        nz, nw = tuple(ez * u for u in sz), tuple(ew * u for u in sw)
                        assert 1 - dot(sz, sw) / R2 == 1 + dot(nz, nw) / R2
                        gauge_bonds += 1
    print(f'PASS: {count} lifted squares, including equality in L,N>=2M+3;')
    print('      neighbourhood injection, internal edges, crossing bonds, edge count.')
    print(f'PASS: {gauge_bonds} exact local-gauge bond checks on these lifts.')


if __name__ == '__main__':
    check_contract()
    frames = check_frames()
    check_cartan()
    check_geometry(frames)
    print('All exact checks passed. One Python process; no third-party packages.')
