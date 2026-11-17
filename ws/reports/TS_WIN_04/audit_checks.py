"""Finite and exact-arithmetic sanity checks; no Lean proofs or repo writes."""

from collections import deque
from fractions import Fraction
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
STAR_STEPS = tuple(p for p in product((-1, 0, 1), repeat=2) if p != (0, 0))
COUNTS = {}


def add(p, q):
    return p[0] + q[0], p[1] + q[1]


def l1(p, q):
    return abs(p[0] - q[0]) + abs(p[1] - q[1])


def linf(p, q):
    return max(abs(p[0] - q[0]), abs(p[1] - q[1]))


def cross(p):
    return {p} | {add(p, d) for d in STEPS}


def distances(vertices, steps=STEPS):
    if not vertices:
        return {}
    root = min(vertices)
    result = {root: 0}
    queue = deque([root])
    while queue:
        p = queue.popleft()
        for d in steps:
            q = add(p, d)
            if q in vertices and q not in result:
                result[q] = result[p] + 1
                queue.append(q)
    return result


def connected(vertices, steps=STEPS):
    return bool(vertices) and len(distances(vertices, steps)) == len(vertices)


points = tuple(product(range(-1, 2), repeat=2))
subsets = [{p for j, p in enumerate(points) if mask & (1 << j)} for mask in range(512)]
assert not connected(set())

for p in product(range(-2, 3), repeat=2):
    c = cross(p)
    assert len(c) == 5 and connected(c)
    for q in product(range(-4, 5), repeat=2):
        assert (q in c) == (l1(q, p) <= 1)
    for step in STAR_STEPS:
        assert c & cross(add(p, step))
COUNTS['cross_centres'] = 25
COUNTS['cross_membership_pairs'] = 25 * 81
COUNTS['star_overlap_pairs'] = 25 * 8

star_connected = adjacent_connected = weight_checks = 0
for vertices in subsets:
    union = set().union(*(cross(p) for p in vertices))
    if connected(vertices, STAR_STEPS):
        star_connected += 1
        assert connected(union)
    if connected(vertices):
        adjacent_connected += 1
        depth = distances(vertices)
        ordered = sorted(vertices, key=lambda p: (depth[p], p))
        assert len(set(ordered)) == len(vertices) and set(ordered) == vertices
        last = len(vertices) - 1
        assert last >= 0 and len(ordered) == last + 1
        for j, p in enumerate(ordered[1:], 1):
            assert any(l1(p, q) == 1 for q in ordered[:j])
    for mode in range(3):
        def f(p):
            if mode == 0:
                return Fraction(0)
            if mode == 1:
                return Fraction(1)
            return Fraction((p[0] + 5) ** 2 + 2 * (p[1] + 5) ** 2 + 1, 7)
        c = Fraction(0) if mode == 0 else max(
            (f(q) / f(p) for p in vertices for q in cross(p)), default=Fraction(1)
        )
        lhs = sum((f(q) for q in union), Fraction(0))
        overcount = sum((sum((f(q) for q in cross(p)), Fraction(0)) for p in vertices), Fraction(0))
        rhs = 5 * c * sum((f(p) for p in vertices), Fraction(0))
        assert lhs <= overcount <= rhs
        weight_checks += 1
COUNTS['all_3x3_subsets'] = len(subsets)
COUNTS['star_connected_3x3_subsets'] = star_connected
COUNTS['adjacent_connected_enumerations'] = adjacent_connected
COUNTS['exact_rational_weight_checks'] = weight_checks

nearby = tuple(product(range(-2, 3), repeat=2))
queries = set(nearby) | {add(p, d) for p in nearby for d in STEPS}
decay_checks = 0
for volume in subsets:
    # A nearest exterior point for a site in volume lies in this expanded box.
    exterior = set(nearby) - volume
    depth = {p: min(l1(p, q) for q in exterior) if p in volume else 0 for p in queries}
    for p in nearby:
        for q in cross(p):
            assert depth[p] <= depth[q] + 1
            for theta in (Fraction(1, 5), Fraction(1, 2), Fraction(4, 5)):
                assert theta ** depth[q] <= theta ** depth[p] / theta
                decay_checks += 1
COUNTS['exact_rational_neighbour_decay_checks'] = decay_checks


def fourth_root_floor(n):
    return isqrt(isqrt(n))


threshold = 390 ** 4
volumes = {threshold + d for d in (0, 1, 2, 17, 390, 152100, 1000000)}
for spacing in (391, 392, 400, 512, 1000, 1000000):
    volumes.update((spacing ** 4 - 1, spacing ** 4, spacing ** 4 + 1))
rng = random.Random(404)
volumes.update(threshold + rng.randrange(10 ** 16) for _ in range(40))
scale_checks = 0
for u in sorted(volumes):
    top = fourth_root_floor(u)
    indices = set(range(2, top + 1)) if top <= 1000 else {2, 3, top // 2, top - 1, top}
    if top > 1000:
        indices.update(rng.randrange(2, top + 1) for _ in range(20))
    for i in indices:
        # Exact k=floor(i*u^(1/4)); all comparisons below use integers only.
        k = fourth_root_floor(i ** 4 * u)
        assert k ** 4 <= i ** 4 * u < (k + 1) ** 4
        assert u >= threshold
        assert (k + 1) ** 4 >= 16 * u  # 2*s-1 <= k
        assert k ** 2 <= u            # k <= s^2
        assert k <= u - 31
        assert (12 * i - 11) ** 4 * u < (12 * (k - 1)) ** 4
        scale_checks += 1
COUNTS['integer_fourth_root_scale_checks'] = scale_checks


def clipped_core(m, y, k):
    # Inner square [-m,m]^2 intersected with the radius-k square boundary.
    result = set()
    for delta in range(-k, k + 1):
        for p in ((y[0] - k, y[1] + delta), (y[0] + k, y[1] + delta),
                  (y[0] + delta, y[1] - k), (y[0] + delta, y[1] + k)):
            if max(abs(p[0]), abs(p[1])) <= m:
                result.add(p)
    return result


core_checks = 0
singleton_cores = 0
for m in (32, 33, 40, 64, 100):
    for k in {32, (32 + m) // 2, m}:
        coords = {-m - 32, -m - 1, -m, -m + 1, -k, 0, k, m - 1, m, m + 1, m + 32}
        for y in product(sorted(coords), repeat=2):
            vertices = clipped_core(m, y, k)
            assert connected(vertices)
            assert any(add(y, (sx * k, sy * k)) in vertices for sx, sy in product((-1, 1), repeat=2))
            for z in vertices:
                u = m + 31
                h = max(0, u + 1 - linf(z, (0, 0)))
                offset = abs(linf(z, y) - k)
                assert offset == 0 and h >= 32
                assert offset <= Fraction(65, 2) and offset + 32 <= h
            core_checks += 1
            singleton_cores += len(vertices) == 1
COUNTS['reduced_core_geometry_checks'] = core_checks
COUNTS['singleton_cores_in_reduced_checks'] = singleton_cores

# Actual nonvacuous CutSetup example at the threshold: a=(0,0), y=(u+1,0), i=2.
u, s, i = threshold, 390, 2
y, k = (u + 1, 0), 780
assert linf(y, (u, 0)) == 1 and y[0] > u
assert 2 <= i <= s and u == s ** 4
assert u - k > Fraction(s, 3)  # Shell's vertical range is far from every corner.
actual_core = clipped_core(u - 31, y, k)
assert connected(actual_core) and (u + 1 - k, 0) in actual_core
COUNTS['threshold_example_core_cardinality'] = len(actual_core)

output = {'status': 'PASS', 'checks': COUNTS,
          'scope': 'Finite sanity checks and exact scale arithmetic; not formal proofs.',
          'threshold_cutsetup_example': {'a': [0, 0], 'y': list(y), 'u': u, 'i': i, 's': s, 'k': k}}
path = Path(__file__).with_name('checks.json')
path.write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output, indent=2))
