"""Finite diagnostics for the truth sweep; no Lean leaf proofs are written."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import isclose, prod, sqrt


class Q5:
    """Exact rational a + b*sqrt(5), with exact order comparisons."""

    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    @staticmethod
    def cast(x):
        return x if isinstance(x, Q5) else Q5(x)

    def __add__(self, other):
        t = self.cast(other)
        return Q5(self.a + t.a, self.b + t.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        t = self.cast(other)
        return Q5(self.a*t.a + 5*self.b*t.b, self.a*t.b + self.b*t.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        t = self.cast(other)
        denominator = t.a*t.a - 5*t.b*t.b
        return self * Q5(t.a/denominator, -t.b/denominator)

    def sign(self):
        a, b = self.a, self.b
        if a == 0:
            return (b > 0) - (b < 0)
        if b == 0:
            return (a > 0) - (a < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        difference = a*a - 5*b*b if a > 0 else 5*b*b - a*a
        return (difference > 0) - (difference < 0)

    def real(self):
        return float(self.a) + float(self.b)*sqrt(5)


letters = list(product(range(3), range(2), range(2)))
phi = Q5(F(1, 2), F(1, 2))
radius_squared = phi + 2
bound = Q5(F(5, 505), F(-1, 505))
ratio = bound / (2 - bound)
assert bound.sign() > 0 and (1 - bound).sign() > 0
assert ratio.sign() > 0 and (1 - ratio).sign() > 0


def raw_vertex(letter):
    family, j, k = letter
    a, b = Q5(1 if j == 0 else -1), phi*(1 if k == 0 else -1)
    return [(Q5(), a, b), (a, b, Q5()), (b, Q5(), a)][family]


def rotate(v):
    x, y, z = v
    return (F(99, 101)*x - F(20, 101)*y,
            F(20, 101)*x + F(99, 101)*y, z)


vectors = [[raw_vertex(a) for a in letters]]
vectors += [[rotate(v) for v in vectors[0]]]
vectors += [[rotate(v) for v in vectors[1]]]
factors = {}
factor_checks = lower_equalities = upper_equalities = 0
for i, j, a, b, sign in product(range(3), range(3), range(12), range(12), (-1, 1)):
    if i == j:
        continue
    scalar = sum((x*y for x, y in zip(vectors[i][a], vectors[j][b])), Q5()) / radius_squared
    factor = 1 + sign*scalar
    assert (factor - bound).sign() >= 0
    assert (2 - bound - factor).sign() >= 0
    factor_checks += 1
    lower_equalities += (factor - bound).sign() == 0
    upper_equalities += (2 - bound - factor).sign() == 0
    factors[i, j, a, b, sign] = factor.real()
assert lower_equalities and upper_equalities
print(f"Exact Q(sqrt(5)) interaction checks: {factor_checks}; "
      f"lower/upper endpoint equalities: {lower_equalities}/{upper_equalities}")


def neighbours(x):
    a, b = x
    return {(a+1, b), (a-1, b), (a, b+1), (a, b-1)}


def internal(w):
    return {(x, y) for x in w for y in ((x[0]+1, x[1]), (x[0], x[1]+1)) if y in w}


def legs(w):
    return {(x, z) for x in w for z in neighbours(x) - w}


def subsets(s):
    sites = sorted(s)
    return [set(c) for k in range(len(sites)+1) for c in combinations(sites, k)]


board = set(product(range(3), repeat=2))
plane_geometries = 0
for w in subsets(board):
    iw, lw = internal(w), legs(w)
    assert len({frozenset(e) for e in iw | lw}) == len(iw | lw)
    for x in w:
        assert sum(x in e for e in iw) + sum(e[0] == x for e in lw) == 4
    for v in subsets(w):
        retained = {frozenset(e) for e in iw | lw if e[0] in v or e[1] in v}
        assert retained == {frozenset(e) for e in internal(v) | legs(v)}
        assert {z for _, z in legs(v) if z not in w} <= {z for _, z in lw}
        assert len({x for x in w if x in v}) == len(v)
        plane_geometries += 1
print(f"Plane nested-volume geometry checks: {plane_geometries} pairs V subset W in a 3x3 board")


def colour(x):
    return sum(x) % 3


def letter_at(x):
    return (3*x[0] + 5*x[1] + 7) % 12


def plane_weight(w, eta, sigma):
    value = 12.0**(-len(w))
    for x, y in internal(w):
        value *= factors[colour(x), colour(y), sigma[x], sigma[y], 1]
    for x, z in legs(w):
        value *= factors[colour(x), colour(z), sigma[x], eta[z], 1]
    return value


shapes = [set(), {(0, 0)}, {(0, 0), (1, 0)}, {(0, 0), (2, 0)},
          {(0, 0), (1, 0), (0, 1)}, {(0, 0), (1, 0), (2, 0)}]
conditional_cases = 0
plane_minimum = 1.0
plane_error = 0.0
reference_error = 0.0
alpha = ratio.real()**4 / 12
for w in shapes:
    order = sorted(w)
    eta = {z: letter_at(z) for _, z in legs(w)}
    configurations = [dict(zip(order, values)) for values in product(range(12), repeat=len(w))]
    weights = [plane_weight(w, eta, sigma) for sigma in configurations]
    assert all(t > 0 for t in weights)
    total = sum(weights)
    law = [t/total for t in weights]
    fixed = {x: (letter_at(x)+2) % 12 for x in w}
    for v in subsets(w):
        vo = sorted(v)
        mass, marginal = 0.0, defaultdict(float)
        for sigma, p in zip(configurations, law):
            if all(sigma[x] == fixed[x] for x in w-v):
                mass += p
                marginal[tuple(sigma[x] for x in vo)] += p
        assert mass > 0
        induced = {z: fixed[z] if z in w else eta[z] for _, z in legs(v)}
        direct = {values: plane_weight(v, induced, dict(zip(vo, values)))
                  for values in product(range(12), repeat=len(v))}
        direct_total = sum(direct.values())
        for values, weight in direct.items():
            left, right = marginal[values]/mass, weight/direct_total
            assert isclose(left, right, rel_tol=1e-10, abs_tol=1e-14)
            plane_error = max(plane_error, abs(left-right))
        conditional_cases += 1
    for x in w:
        exterior_mass = defaultdict(float)
        off = sorted(w - {x})
        for sigma, p in zip(configurations, law):
            exterior_mass[tuple(sigma[y] for y in off)] += p
        for sigma, p in zip(configurations, law):
            probability = p/exterior_mass[tuple(sigma[y] for y in off)]
            assert probability >= alpha
            plane_minimum = min(plane_minimum, probability)
    local = {}
    for x in w:
        h = [prod(factors[colour(x), colour(z), a, eta[z], 1]
                  for y, z in legs(w) if y == x)/12 for a in range(12)]
        assert min(h) > 0
        local[x] = [t/sum(h) for t in h]
    reference = [prod(local[x][sigma[x]] for x in w) for sigma in configurations]
    assert min(reference) > 0
    assert isclose(sum(reference), 1.0, abs_tol=1e-12)
    reference_error = max(reference_error, abs(sum(reference)-1.0))
print(f"Plane conditioning: {conditional_cases} cases; maximum error {plane_error:.3g}")
print(f"Plane one-site minimum across these volumes/fibres: {plane_minimum:.12g}; alpha={alpha:.12g}")
print(f"Positive product references: {len(shapes)} volumes, including empty; sum error {reference_error:.3g}")


def torus_geometry(m, n):
    sites = set(product(range(m), range(n)))
    bonds = [(x, ((x[0]+1) % m, x[1])) for x in sorted(sites)]
    bonds += [(x, (x[0], (x[1]+1) % n)) for x in sorted(sites)]
    near = {x: {((x[0]+1) % m, x[1]), ((x[0]-1) % m, x[1]),
                (x[0], (x[1]+1) % n), (x[0], (x[1]-1) % n)} for x in sites}
    assert all(x != y for x, y in bonds)
    assert len({frozenset(e) for e in bonds}) == 2*m*n
    assert all(sum(x in e for e in bonds) == 4 and len(near[x]) == 4 for x in sites)
    return sites, bonds, near


for m, n in product(range(3, 8), repeat=2):
    torus_geometry(m, n)
sites, bonds, near = torus_geometry(3, 3)
for u in subsets(sites):
    boundary = set().union(*(near[x] for x in u)) - u
    crossings = {z for x, y in bonds for z in (x, y) if ((x in u) != (y in u)) and z not in u}
    assert boundary == crossings
print("Torus geometry: 25 period pairs 3..7; all 512 blocks on 3x3 have the stated boundary")


def cycle_colour(m, i):
    return 2 if m % 2 and i == m-1 else i % 2


torus_cases, torus_error, torus_minimum = 0, 0.0, 1.0
for m, n in ((3, 3), (3, 4), (4, 3), (4, 4), (5, 3)):
    sites, bonds, near = torus_geometry(m, n)
    kappa = {x: (cycle_colour(m, x[0])+cycle_colour(n, x[1])) % 3 for x in sites}
    assert all(kappa[x] != kappa[y] for x, y in bonds)
    sigma = {x: letter_at(x) for x in sites}

    def law_on_block(u, exterior):
        order = sorted(u)
        values = {}
        for assignment in product(range(12), repeat=len(u)):
            tau = exterior | dict(zip(order, assignment))
            values[assignment] = 12.0**(-m*n) * prod(
                factors[kappa[x], kappa[y], tau[x], tau[y], -1] for x, y in bonds)
        z = sum(values.values())
        assert z > 0
        return {a: t/z for a, t in values.items()}

    blocks = [set(), {(0, 0)}, {(0, 0), (1, 0)}, {(0, 0), (m-1, 0)}, {(0, 0), (1, 1)}]
    for u in blocks:
        boundary = set().union(*(near[x] for x in u)) - u
        xi = {x: sigma[x] if x in boundary else (sigma[x]+5) % 12 for x in sites}
        left, right = law_on_block(u, sigma), law_on_block(u, xi)
        for a in left:
            assert isclose(left[a], right[a], rel_tol=1e-10, abs_tol=1e-14)
            torus_error = max(torus_error, abs(left[a]-right[a]))
        torus_cases += 1
    for x in sites:
        one_site = law_on_block({x}, sigma)
        assert min(one_site.values()) >= alpha
        torus_minimum = min(torus_minimum, min(one_site.values()))
print(f"Torus Markov: {torus_cases} conditional comparisons; maximum error {torus_error:.3g}")
print(f"Torus one-site minimum for sampled exteriors: {torus_minimum:.12g}")


partial_checks = 0
for sizes in ((), (2,), (2, 3), (2, 3, 1), (2, 3, 2)):
    sites = set(range(len(sizes)))
    states = list(product(*(range(n) for n in sizes)))
    weights = {sigma: F(1 + (7*i + 3*i*i) % 19) for i, sigma in enumerate(states)}
    total = sum(weights.values())
    p = {sigma: w/total for sigma, w in weights.items()}
    lower = F(1)
    for x in sites:
        fibre_sum = defaultdict(F)
        for sigma, w in p.items():
            fibre_sum[tuple(sigma[y] for y in sorted(sites-{x}))] += w
        lower = min(lower, *(w/fibre_sum[tuple(sigma[y] for y in sorted(sites-{x}))]
                             for sigma, w in p.items()))
    assert 0 < lower <= 1
    for u, j in product(subsets(sites), repeat=2):
        if u & j:
            continue
        for a, b in product(states, repeat=2):
            denominator = sum(w for sigma, w in p.items() if all(sigma[x] == a[x] for x in j))
            numerator = sum(w for sigma, w in p.items() if all(sigma[x] == a[x] for x in j)
                            and all(sigma[x] == b[x] for x in u))
            assert denominator > 0 and numerator/denominator >= lower**len(u)
            partial_checks += 1
print(f"Exact rational partial-assignment checks: {partial_checks}; includes empty sites and singleton alphabet")
print("All finite diagnostics passed. Floating-point checks are examples, not universal proofs.")
