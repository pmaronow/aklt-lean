"""Independent checks for the extension; exact Q(sqrt(5)) arithmetic.

This script imports no manuscript/referee code and uses one process.
Finite enumerations supplement the universal proofs in proof.tex.
"""
from fractions import Fraction as F
from itertools import product, combinations
from math import prod


class K:
    def __init__(self, a=0, b=0):
        if isinstance(a, K):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = F(a), F(b)

    def __add__(self, x):
        x = K(x)
        return K(self.a + x.a, self.b + x.b)

    __radd__ = __add__

    def __neg__(self):
        return K(-self.a, -self.b)

    def __sub__(self, x):
        return self + -K(x)

    def __rsub__(self, x):
        return K(x) + -self

    def __mul__(self, x):
        x = K(x)
        return K(self.a*x.a + 5*self.b*x.b, self.a*x.b + self.b*x.a)

    __rmul__ = __mul__

    def __truediv__(self, x):
        x = K(x)
        norm = x.a*x.a - 5*x.b*x.b
        assert norm
        return self*K(x.a/norm, -x.b/norm)

    def __pow__(self, n):
        assert n >= 0
        ans = K(1)
        for _ in range(n):
            ans *= self
        return ans

    def __eq__(self, x):
        x = K(x)
        return self.a == x.a and self.b == x.b

    def sign(self):
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        c = a*a - 5*b*b
        assert c != 0
        return ((c > 0) - (c < 0)) * ((a > 0) - (a < 0))

    def __lt__(self, x):
        return (self - x).sign() < 0

    def __repr__(self):
        return f"({self.a}) + ({self.b})*sqrt(5)"


phi = K(F(1, 2), F(1, 2))
rad2 = phi + 2
base = []
for s, t in product((-1, 1), repeat=2):
    base.extend([(K(0), K(s), t*phi), (K(s), t*phi, K(0)),
                 (t*phi, K(0), K(s))])


def rotate(v):
    x, y, z = v
    return ((99*x - 20*y)/101, (20*x + 99*y)/101, z)


designs = [base]
for _ in range(2):
    designs.append([rotate(v) for v in designs[-1]])


def df(n):
    return prod(range(n, 0, -2))


checks = 0
for vertices in designs:
    assert len(vertices) == 12
    assert all(sum(x*x for x in v) == rad2 for v in vertices)
    assert all(any(all(x == -y for x, y in zip(v, w)) for w in vertices)
               for v in vertices)
    for degree in range(6):
        for i in range(degree + 1):
            for j in range(degree - i + 1):
                powers = (i, j, degree-i-j)
                raw = sum(prod(v[k]**powers[k] for k in range(3))
                          for v in vertices)/12
                if degree % 2:
                    assert raw == 0
                else:
                    actual = raw/(rad2**(degree//2))
                    expected = (F(0) if any(p % 2 for p in powers)
                                else F(prod(df(p-1) for p in powers), df(degree+1)))
                    assert actual == expected, (powers, actual, expected)
                checks += 1
print(f"Three antipodal uniform 5-designs: {checks} exact monomial checks PASS")

delta = K(F(5, 505), F(-1, 505))
weights = []
for i, j in combinations(range(3), 2):
    for a, b in product(designs[i], designs[j]):
        dot = sum(x*y for x, y in zip(a, b))/rad2
        weight = 1 - dot
        assert not weight < delta
        assert not 2 - delta < weight
        weights.append(weight)
assert min(weights) == delta
assert min(weights).sign() > 0
print(f"All {len(weights)} cross-frame pairs: 1 +/- dot in [delta,2-delta] PASS")
print(f"Exact minimum delta = {delta}")
print(f"Minimum attained {sum(w == delta for w in weights)} times")


def cycle_colour(m, i):
    return 2 if m % 2 and i == m-1 else i % 2


def colour(l, n, x):
    return (cycle_colour(l, x[0]) + cycle_colour(n, x[1])) % 3


graph_cases = 0
for l, n in product(range(3, 35), repeat=2):
    for x in product(range(l), range(n)):
        neighbours = {((x[0]+d[0]) % l, (x[1]+d[1]) % n)
                      for d in ((1, 0), (-1, 0), (0, 1), (0, -1))}
        assert len(neighbours) == 4 and x not in neighbours
        assert all(colour(l, n, x) != colour(l, n, y) for y in neighbours)
    graph_cases += 1
print(f"Simple degree-four graphs and proper 3-colourings: {graph_cases} tori PASS")

# Every placement is equivalent to the following wrap tests for this graph
# assertion. Test placements too, including repeated exterior images.
lift_cases = repeated = 0
for ell in (2, 4, 6):
    for l, n in product((ell+1, ell+2), repeat=2):
        for a in product(range(l), range(n)):
            box = set(product(range(ell), repeat=2))
            image = lambda x: ((x[0]+a[0]) % l, (x[1]+a[1]) % n)
            assert len({image(x) for x in box}) == ell*ell
            for x, y in combinations(box, 2):
                ix, iy = image(x), image(y)
                torus_edge = ((ix[0] == iy[0] and (ix[1]-iy[1]) % n in (1, n-1))
                              or (ix[1] == iy[1] and (ix[0]-iy[0]) % l in (1, l-1)))
                assert torus_edge == (sum(abs(x[k]-y[k]) for k in range(2)) == 1)
            exterior = {tuple(x[k]+d[k] for k in range(2))
                        for x in box for d in ((1, 0), (-1, 0), (0, 1), (0, -1))
                        if tuple(x[k]+d[k] for k in range(2)) not in box}
            repeated += len({image(x) for x in exterior}) < len(exterior)
            for z in exterior:
                assert sum(sum(abs(z[k]-x[k]) for k in range(2)) == 1 for x in box) == 1
                # Local gauge: epsilon_x*epsilon_z=-1 on each boundary edge.
                for x in box:
                    if sum(abs(z[k]-x[k]) for k in range(2)) == 1:
                        assert (-1)**(sum(x)+sum(z)) == -1
                        assert colour(l, n, image(x)) != colour(l, n, image(z))
            lift_cases += 1
print(f"Box lifts and local gauges: {lift_cases} placements PASS; "
      f"{repeated} with repeated exterior images")
