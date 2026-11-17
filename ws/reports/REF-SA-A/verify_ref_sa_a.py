"""Independent, single-process exact checks for the algebraic referee report.

Only Python's standard library is used.  Coordinates before normalization and
all even moments / normalized dot products lie in Q(sqrt(5)).  No input files
are read, and no floating-point comparison is used.
"""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import comb, prod


@dataclass(frozen=True)
class Q5:
    a: F = F(0)
    b: F = F(0)

    @staticmethod
    def cast(x):
        return x if isinstance(x, Q5) else Q5(F(x))

    def __add__(self, other):
        y = self.cast(other)
        return Q5(self.a + y.a, self.b + y.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        y = self.cast(other)
        return Q5(self.a * y.a + 5 * self.b * y.b,
                  self.a * y.b + self.b * y.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        y = self.cast(other)
        denominator = y.a * y.a - 5 * y.b * y.b
        assert denominator
        return self * Q5(y.a / denominator, -y.b / denominator)

    def __pow__(self, n):
        assert n >= 0
        out = Q5(F(1))
        for _ in range(n):
            out = out * self
        return out

    def sign(self):
        if not self.b:
            return (self.a > 0) - (self.a < 0)
        if self.b < 0:
            return -(-self).sign()
        if self.a >= 0:
            return 1
        difference = 5 * self.b * self.b - self.a * self.a
        return (difference > 0) - (difference < 0)

    def __abs__(self):
        return self if self.sign() >= 0 else -self

    def __str__(self):
        return f"({self.a}) + ({self.b}) sqrt(5)"


ZERO = Q5()
ONE = Q5(F(1))
phi = Q5(F(1, 2), F(1, 2))
r2 = phi + 2
b = Q5(F(1, 101), F(-1, 505))
gamma = 1 - b
assert b == Q5.cast(2) / (101 * r2)
assert b.sign() > 0 and (Q5.cast(F(9, 50)) - b).sign() > 0


def rotate(v):
    x, y, z = v
    return ((99 * x - 20 * y) / 101,
            (20 * x + 99 * y) / 101, z)


vertices = []
for p, q in product((-1, 1), repeat=2):
    vertices.extend(((ZERO, Q5.cast(p), q * phi),
                     (Q5.cast(p), q * phi, ZERO),
                     (p * phi, ZERO, Q5.cast(q))))
frames = [vertices]
for _ in range(2):
    frames.append([rotate(v) for v in frames[-1]])
assert all(len(set(frame)) == 12 for frame in frames)
assert all(sum(x * x for x in v) == r2 for frame in frames for v in frame)
assert all(tuple(-x for x in v) in frame for frame in frames for v in frame)


def odd_double_factorial(n):
    return prod(range(1, n + 1, 2))


moment_count = 0
for frame in frames:
    for exponents in product(range(6), repeat=3):
        degree = sum(exponents)
        if degree > 5:
            continue
        unnormalized = sum(prod(x ** e for x, e in zip(v, exponents))
                           for v in frame) / 12
        if degree % 2:
            assert unnormalized == ZERO
        else:
            expected = F(0) if any(e % 2 for e in exponents) else F(
                prod(odd_double_factorial(e - 1) for e in exponents),
                odd_double_factorial(degree + 1))
            assert unnormalized / r2 ** (degree // 2) == Q5.cast(expected)
        moment_count += 1
print(f"PASS: {moment_count} exact spherical moment identities (degree <= 5)")

pair_count = 0
for i, j in ((0, 1), (0, 2), (1, 2)):
    values = [sum(x * y for x, y in zip(v, w)) / r2
              for v in frames[i] for w in frames[j]]
    maximum = ZERO
    for dot in values:
        assert (gamma - abs(dot)).sign() >= 0
        if (abs(dot) - maximum).sign() > 0:
            maximum = abs(dot)
    print(f"PASS: frames {i},{j}: max |dot| = {maximum}; "
          f"attains gamma: {maximum == gamma}")
    pair_count += len(values)
assert any(sum(x * y for x, y in zip(v, w)) / r2 == gamma
           for v in frames[0] for w in frames[1])
print(f"PASS: {pair_count} cross-frame pairs, both signed bond bounds; b = {b}")


def rational_rank(matrix):
    a = [[F(x) for x in row] for row in matrix]
    rank = 0
    for column in range(len(a[0])):
        pivot = next((row for row in range(rank, len(a)) if a[row][column]), None)
        if pivot is None:
            continue
        a[pivot], a[rank] = a[rank], a[pivot]
        divisor = a[rank][column]
        a[rank] = [x / divisor for x in a[rank]]
        for row in range(rank + 1, len(a)):
            multiplier = a[row][column]
            if multiplier:
                a[row] = [x - multiplier * y for x, y in zip(a[row], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


# Bidegree-(4,4) monomials indexed by their z_2 exponents.
rows = list(product(range(5), repeat=2))
columns = list(product(range(4), repeat=2))
qimage = [[int((i, j) == (k, l + 1)) - int((i, j) == (k + 1, l))
           for k, l in columns] for i, j in rows]
spin4 = [[comb(4, i) * comb(4, j) * int(i + j == m) for m in range(9)]
         for i, j in rows]
gram = [F(1, comb(4, i) * comb(4, j)) for i, j in rows]
assert rational_rank(qimage) == 16
assert rational_rank(spin4) == 9
assert all(sum(qimage[r][c] * gram[r] * spin4[r][m] for r in range(25)) == 0
           for c in range(16) for m in range(9))
print("PASS: exact two-site edge lemma: determinant image rank 16, "
      "spin-4 rank 9, orthogonal in the manuscript inner product")


def colour_cycle(m, i):
    return 2 if m % 2 and i == m - 1 else i % 2


def colour(L, N, vertex):
    i, j = vertex
    return (colour_cycle(L, i) + colour_cycle(N, j)) % 3


def torus_edges(L, N):
    edges = set()
    for x in product(range(L), range(N)):
        for delta in ((1, 0), (0, 1)):
            y = ((x[0] + delta[0]) % L, (x[1] + delta[1]) % N)
            if x != y:
                edges.add(tuple(sorted((x, y))))
    return edges


for L, N in product(range(3, 41), repeat=2):
    edges = torus_edges(L, N)
    degrees = Counter(x for edge in edges for x in edge)
    assert len(edges) == 2 * L * N
    assert set(degrees.values()) == {4}
    assert all(colour(L, N, x) != colour(L, N, y) for x, y in edges)
print("PASS: torus simplicity, four-regularity and proper colours for 3 <= L,N <= 40")


lift_cases = 0
repeated_cases = 0
opposite_sign_cases = 0
deltas = ((1, 0), (-1, 0), (0, 1), (0, -1))
for ell in (2, 4, 6, 8):
    for L, N in product(range(ell + 1, ell + 4), repeat=2):
        edges = torus_edges(L, N)
        for a in product(range(L), range(N)):
            box = set(product(range(a[0], a[0] + ell),
                              range(a[1], a[1] + ell)))
            projection = lambda z: (z[0] % L, z[1] % N)
            image = {projection(z) for z in box}
            assert len(image) == ell * ell
            internal = set()
            crossing = []
            exterior_images = {}
            touches = Counter()
            for z in box:
                for dx, dy in deltas:
                    w = (z[0] + dx, z[1] + dy)
                    assert (sum(z) + sum(w)) % 2 == 1
                    if w in box:
                        internal.add(tuple(sorted((projection(z), projection(w)))))
                    else:
                        assert projection(w) not in image
                        crossing.append(tuple(sorted((projection(z), projection(w)))))
                        touches[w] += 1
                        exterior_images.setdefault(projection(w), []).append(w)
            assert internal == {e for e in edges if all(x in image for x in e)}
            assert Counter(crossing) == Counter(e for e in edges
                                               if sum(x in image for x in e) == 1)
            assert all(n == 1 for n in touches.values())
            repeated = [ws for ws in exterior_images.values() if len(ws) > 1]
            repeated_cases += bool(repeated)
            opposite_sign_cases += any(len({sum(w) % 2 for w in ws}) == 2
                                       for ws in repeated)
            lift_cases += 1
print(f"PASS: {lift_cases} translated boundary-lift cases, "
      f"{repeated_cases} with repeated images, "
      f"{opposite_sign_cases} with opposite gauge signs")


# Check c_x beta_x rho_x for every orientation of the nonbipartite graph K_5.
K5 = [(i, j) for i in range(5) for j in range(i + 1, 5)]
z = [(i + 1, (i + 1) ** 2) for i in range(5)]
q = lambda x, y: z[x][0] * z[y][1] - z[x][1] * z[y][0]
assert all(q(x, y) for x, y in K5)
for orientations in product((-1, 1), repeat=len(K5)):
    B = prod(sign * q(x, y) for sign, (x, y) in zip(orientations, K5))
    for center in range(5):
        beta_x, rho_x = 1, 1
        for sign, (x, y) in zip(orientations, K5):
            if center in (x, y):
                other = y if center == x else x
                beta_x *= q(center, other)
                rho_x *= sign if center == x else -sign
            else:
                rho_x *= sign * q(x, y)
        assert B == beta_x * rho_x
print("PASS: local orientation factorization on all 1024 orientations of K_5")


for r, s in product(range(2, 21), repeat=2):
    degrees = [(i > 0) + (i < r - 1) + (j > 0) + (j < s - 1)
               for i in range(r) for j in range(s)]
    assert prod(5 - d for d in degrees) == 3 ** 4 * 2 ** (2 * r + 2 * s - 8)
for L, N in product(range(1, 13), repeat=2):
    edges = torus_edges(L, N)
    degrees = Counter(x for edge in edges for x in edge)
    actual = prod(5 - degrees[x] for x in product(range(L), range(N)))
    if min(L, N) >= 3:
        expected = 1
    elif sorted((L, N)) == [1, 1]:
        expected = 5
    elif sorted((L, N)) == [1, 2]:
        expected = 4 ** 2
    elif sorted((L, N)) == [2, 2]:
        expected = 3 ** 4
    elif min(L, N) == 1:
        expected = 3 ** max(L, N)
    else:
        expected = 2 ** (2 * max(L, N))
    assert actual == expected
print("PASS: open-rectangle and suppressed-loop/repeated-bond dimension formulas")
print("ALL CHECKS PASSED")
