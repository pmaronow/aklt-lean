"""Independent finite checks; these are diagnostics, not Lean proofs."""
from collections import deque
from fractions import Fraction
from itertools import combinations, product
from math import fsum, isclose, sqrt
from pathlib import Path
import json
import random

RNG = random.Random(8073)
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def neighbours(x):
    return [(x[0] + dx, x[1] + dy) for dx, dy in STEPS]


def dist(x, y):
    return abs(x[0] - y[0]) + abs(x[1] - y[1])


def internal_bonds(g):
    return [(x, z) for x in sorted(g)
            for z in ((x[0] + 1, x[1]), (x[0], x[1] + 1)) if z in g]


def original_legs(g):
    return [(x, z) for x in sorted(g) for z in neighbours(x) if z not in g]


def depths(g):
    # Exact graph distance to the exterior, by breadth-first search from its boundary.
    result = {x: 1 for x in g if any(z not in g for z in neighbours(x))}
    q = deque(result)
    while q:
        x = q.popleft()
        for z in neighbours(x):
            if z in g and z not in result:
                result[z] = result[x] + 1
                q.append(z)
    assert len(result) == len(g)
    return result


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


phi = (1 + sqrt(5)) / 2
radius = sqrt(phi + 2)
ico = []
for family, sign_a, sign_b in product(range(3), (1, -1), (1, -1)):
    a, b = sign_a, sign_b * phi
    v = ((0, a, b), (a, b, 0), (b, 0, a))[family]
    ico.append(tuple(t / radius for t in v))


def rotate(v):
    x, y, z = v
    return ((99 * x - 20 * y) / 101, (20 * x + 99 * y) / 101, z)


frames = [ico, list(map(rotate, ico)), list(map(rotate, map(rotate, ico)))]
monomials = [m for m in product(range(5), repeat=3) if sum(m) <= 4]
moment_residual = 0.0
for m in monomials:
    values = [fsum(v[0] ** m[0] * v[1] ** m[1] * v[2] ** m[2]
                   for v in f) / 12 for f in frames]
    moment_residual = max(moment_residual, *(abs(v - values[0]) for v in values))
assert moment_residual < 1e-14


def partition(g, y, pins, colour):
    """Direct enumeration of the concrete partition sum, without polynomial expansion."""
    active = sorted(g - y)
    index = {x: i for i, x in enumerate(active)}
    bonds = [(index[x], index[z]) for x, z in internal_bonds(g - y)]
    legs = [(index[x], pins[x, z]) for x, z in original_legs(g) if x in index]
    for x in active:
        appearances = sum(x == a or x == b for a, b in internal_bonds(g - y))
        appearances += sum(x == a for a, _ in original_legs(g))
        assert appearances <= 4
    alphabets = [frames[colour(x)] for x in active]

    def term(labels):
        spins = [alphabets[i][a] for i, a in enumerate(labels)]
        weight = 1.0
        for i, j in bonds:
            weight *= 1 + dot(spins[i], spins[j])
        for i, a in legs:
            weight *= 1 + dot(a, spins[i])
        return weight

    return fsum(term(labels) for labels in product(range(12), repeat=len(active))) / 12 ** len(active)


def random_unit():
    v = tuple(RNG.uniform(-1, 1) for _ in range(3))
    r = sqrt(dot(v, v))
    return tuple(x / r for x in v)


quadrature_cases = []
volumes = [set(), {(0, 0)}, {(0, 0), (1, 0)},
           {(0, 0), (1, 0), (0, 1)}, set(product(range(2), repeat=2)),
           {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)}]
for number, g in enumerate(volumes):
    pins = {e: random_unit() for e in original_legs(g)}
    ys = [set(), set(g), {(7, 9)}]
    if g:
        ys.append({min(g)})
    if len(g) == 5:
        ys = [{(0, 0)}, set(g)]
    for y in ys:
        colour = lambda x: (x[0] + 2 * x[1]) % 3
        actual = partition(g, y, pins, colour)
        base = partition(g, y, pins, lambda _: 0)
        assert isclose(actual, base, rel_tol=2e-13, abs_tol=2e-13)
        quadrature_cases.append({'volume': number, 'removed': sorted(y),
                                 'frame': actual, 'ico': base, 'residual': abs(actual - base)})


def plane_weight(f, boundary, sigma, colour):
    weight = 12.0 ** -len(f)
    for x, z in internal_bonds(f):
        weight *= 1 + dot(frames[colour(x)][sigma[x]], frames[colour(z)][sigma[z]])
    for x, z in original_legs(f):
        weight *= 1 + dot(frames[colour(x)][sigma[x]], frames[colour(z)][boundary[z]])
    return weight


def fibre_check(f, b, fixed, colour):
    boundary = {z: RNG.randrange(12) for _, z in original_legs(f)}
    assert b <= f and all(z in f for x in b for z in neighbours(x))
    # Enumerate the whole F state space and group by the actual B restriction.
    # This separately checks the multiplicity in marginalNumerator.
    sites = sorted(f)
    window = sorted(b)
    grouped = {s: [] for s in product(range(12), repeat=len(window))}
    for labels in product(range(12), repeat=len(sites)):
        sigma = dict(zip(sites, labels))
        key = tuple(sigma[x] for x in window)
        if fixed is None or key == fixed:
            grouped[key].append(plane_weight(f, boundary, sigma, colour))
    max_residual = 0.0
    for key, terms in grouped.items():
        if fixed is not None and key != fixed:
            continue
        s = dict(zip(window, key))
        g = f - b
        pins = {(x, z): frames[colour(z)][s[z] if z in b else boundary[z]]
                for x, z in original_legs(g)}
        w = 12.0 ** -len(b)
        for x, z in internal_bonds(b):
            w *= 1 + dot(frames[colour(x)][s[x]], frames[colour(z)][s[z]])
        lhs = fsum(terms)
        rhs = w * partition(g, set(), pins, colour)
        assert isclose(lhs, rhs, rel_tol=2e-13, abs_tol=2e-13), (lhs, rhs)
        max_residual = max(max_residual, abs(lhs - rhs))
    return max_residual


fibre_cases = [
    fibre_check(set(), set(), None, lambda x: sum(x) % 3),
    fibre_check({(0, 0), (1, 0)}, set(), None, lambda x: sum(x) % 3),
    fibre_check({(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)},
                {(0, 0)}, (4,), lambda x: sum(x) % 3),
]


geometry_volumes = [set(product(range(-r, r + 1), repeat=2)) for r in range(2, 6)]
geometry_volumes += [{x for x in product(range(-r, r + 1), repeat=2)
                      if dist(x, (0, 0)) <= r} for r in range(2, 6)]
box = set(product(range(-4, 5), repeat=2))
core = {x for x in box if dist(x, (0, 0)) <= 2}
geometry_volumes += [core | {x for x in box if RNG.random() < .8} for _ in range(50)]
geometry_pairs = 0
cost_cases = 0
for g in geometry_volumes:
    bdepth = depths(g)
    protected = {z for z in g if bdepth[z] <= 2}
    deep = {z for z in g if bdepth[z] >= 3}
    assert deep
    for x in deep:
        y = {z for z in deep - {x} if RNG.random() < .5}
        assert y | {x} <= g - protected
        surviving = set(neighbours(x)) & (g - (y | {x}))
        assert len(surviving) <= 4
        if not y:
            assert len(surviving) == 4
        if y & set(neighbours(x)):
            assert len(surviving) <= 3
        assert all(bdepth[z] >= 2 for z in surviving)
        for z, w in combinations(surviving, 2):
            assert dist(z, w) == 2
            distance = min(dist(v, p) for v in (z, w) for p in protected)
            assert distance >= bdepth[x] - 3
            geometry_pairs += 1
    # Produce a connected injective enumeration by BFS inside deep sites.
    seed = min(deep)
    order = [seed]
    seen = {seed}
    for x in order:
        for z in neighbours(x):
            if z in deep - seen:
                seen.add(z)
                order.append(z)
    for size in sorted({1, min(2, len(order)), len(order)}):
        enumeration = order[:size]
        assert all(any(dist(x, c) == 1 for c in enumeration[:j])
                   for j, x in enumerate(enumeration) if j)
        for a, theta in product((0, 2, 7), (Fraction(1, 10), Fraction(1, 2),
                                           Fraction(9, 10), Fraction(99, 100))):
            lhs = 1 + 4 * a * theta ** (bdepth[enumeration[0]] - 3)
            lhs += 2 * a * sum(theta ** (bdepth[z] - 3) for z in enumeration[1:])
            rhs = 1 + 4 * a + 2 * a * theta ** -3 * sum(theta ** bdepth[z] for z in enumeration)
            assert lhs <= rhs
            cost_cases += 1


result = {
    'status': 'PASS',
    'frame_monomials_through_degree_four': len(monomials),
    'frame_moment_max_residual': moment_residual,
    'quadrature_cases': quadrature_cases,
    'quadrature_max_residual': max(c['residual'] for c in quadrature_cases),
    'fibre_factorization_cases': len(fibre_cases),
    'fibre_max_residual': max(fibre_cases),
    'finite_geometry_volumes': len(geometry_volumes),
    'surviving_pairs_checked': geometry_pairs,
    'exact_rational_cost_comparisons': cost_cases,
    'scope': 'Finite diagnostics only. Global ResponseProperty and Lean provability are assessed mathematically, not established by this script.'
}
out = Path(__file__).with_name('small-case-results.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'quadrature_cases'}, indent=2))
