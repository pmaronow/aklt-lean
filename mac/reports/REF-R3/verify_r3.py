"""Independent finite checks for referee lane R3; no manuscript proof is assumed."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json


def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for e, v in p.items():
            out[e] += v
    return {e: v for e, v in out.items() if v}


def scale(p, a):
    return {e: a * v for e, v in p.items() if a * v}


def mul(p, q):
    out = defaultdict(int)
    for e, v in p.items():
        for f, w in q.items():
            out[tuple(a + b for a, b in zip(e, f))] += v * w
    return {e: v for e, v in out.items() if v}


one = {(0, 0, 0): 1}
q, r, z = [{tuple(int(i == j) for i in range(3)): 1} for j in range(3)]
coeff = [add(scale(one, 5), x) for x in (q, r, z)]
v2 = add(*(mul(a, a) for a in coeff),
         scale(mul(mul(coeff[0], coeff[1]), z), 2),
         scale(mul(mul(coeff[0], coeff[2]), r), 2),
         scale(mul(mul(coeff[1], coeff[2]), q), 2))
a = add(scale(one, 9), scale(add(q, r, z), 3))
lhs = add(mul(a, a), scale(v2, -1))
rhs = add(*(scale(mul(add(x, scale(y, -1)), add(x, scale(y, -1))), 4)
            for x, y in ((q, r), (q, z), (r, z))),
          scale(mul(mul(add(one, scale(q, -1)), add(one, scale(r, -1))),
                    add(one, scale(z, -1))), 6))
assert lhs == rhs
lower4 = 1 - F(4, 6) * F(9, 25) - F(3, 15) * F(9, 25)**2
assert lower4 == F(4588, 6250) and lower4 >= F(734, 1000)
assert 1 / F(82, 100) <= F(122, 100)
assert 2 / F(734, 1000) <= F(273, 100)
assert F(7776, 10000) / (15 * F(734, 1000)) <= F(707, 10000)


def adj_masks(points, star):
    return [sum(1 << j for j, b in enumerate(points)
                if max(abs(a[0] - b[0]), abs(a[1] - b[1])) == 1
                and (star or abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1))
            for a in points]


def connected(mask, adj):
    if not mask:
        return True
    seen = 0
    todo = mask & -mask
    while todo:
        bit = todo & -todo
        todo -= bit
        seen |= bit
        todo |= adj[bit.bit_length() - 1] & mask & ~seen
    return seen == mask


small = list(product(range(4), repeat=2))
large = list(product(range(-1, 5), repeat=2))
large_index = {a: i for i, a in enumerate(large)}
adj_small_star = adj_masks(small, True)
adj_large_star = adj_masks(large, True)
adj_large_nn = adj_masks(large, False)
diagonals = []
for i, j in product(range(3), repeat=2):
    bits = [1 << small.index((i + a, j + b)) for a, b in product(range(2), repeat=2)]
    diagonals.append((sum(bits), (bits[0] | bits[3], bits[1] | bits[2])))
tested = 0
for mask in range(1, 1 << 16):
    if not connected(mask, adj_small_star):
        continue
    if any(mask & block in ds for block, ds in diagonals):
        continue
    a = sum(1 << large_index[p] for j, p in enumerate(small) if mask & (1 << j))
    complement = ((1 << len(large)) - 1) ^ a
    if not connected(complement, adj_large_star):
        continue
    boundary = 0
    for j in range(len(large)):
        if a & (1 << j):
            boundary |= adj_large_star[j]
    boundary &= ~a
    assert connected(boundary, adj_large_nn), mask
    tested += 1


NN = ((1, 0), (-1, 0), (0, 1), (0, -1))
STAR = tuple((a, b) for a, b in product((-1, 0, 1), repeat=2) if a or b)


def set_connected(a):
    seen = {next(iter(a))}
    todo = list(seen)
    while todo:
        x, y = todo.pop()
        for dx, dy in NN:
            p = x + dx, y + dy
            if p in a and p not in seen:
                seen.add(p)
                todo.append(p)
    return seen == a


def rectangle_distance(p, r):
    x0, x1, y0, y1 = r
    return max(x0 - p[0], 0, p[0] - x1) + max(y0 - p[1], 0, p[1] - y1)


def geometry_check(s, ell, i, kind, offset):
    m = s**4
    k = i * s
    y = ((0, -m - 1) if kind == 0 else
         (m + 1, -m - 1) if kind == 1 else
         (m - k - s, -m - 1) if kind == 2 else
         (m - k + s, -m - 1))
    width = s // 12
    outer, inner = k + width, k - width
    u = set()
    for b in range(max(-m, y[1] - outer), min(m, y[1] + outer) + 1):
        ranges = [(y[0] - outer, y[0] + outer)] if abs(b - y[1]) >= inner else [
            (y[0] - outer, y[0] - inner), (y[0] + inner, y[0] + outer)]
        for lo, hi in ranges:
            for a in range(max(-m, lo), min(m, hi) + 1):
                t = abs(max(abs(a - y[0]), abs(b - y[1])) - k)
                h = m + 1 - max(abs(a), abs(b))
                if t <= width and h - t >= ell // 2:
                    u.add((a, b))
    assert u
    candidates = {(a + da, b + db) for a, b in u for da, db in STAR} - u
    xset = set()
    second_counts = defaultdict(int)
    for a, b in candidates:
        t = abs(max(abs(a - y[0]), abs(b - y[1])) - k)
        if t <= width:
            second_counts[t] += 1
        for dx, dy in product((0, 1), repeat=2):
            p = (2 * a + offset + dx, 2 * b + dy)
            if any(((p[0] + ex - offset) // 2, (p[1] + ey) // 2) in u for ex, ey in STAR):
                xset.add(p)
    assert max(second_counts.values(), default=0) <= 48
    assert set_connected(xset)
    xmin, xmax, ymin, ymax = -2*m + offset, 2*m + offset + 1, -2*m, 2*m + 1
    r = (i - 1) * s
    notch = (2*(y[0]-r)+offset, 2*(y[0]+r)+offset+1, 2*(y[1]-r), 2*(y[1]+r)+1)
    brects = []
    lo, hi = -m + ell, m - ell
    for axis in (0, 1):
        for sign in (-1, 1):
            fix = y[axis] + sign*k
            l, h = max(y[1-axis]-k, lo), min(y[1-axis]+k, hi)
            if lo <= fix <= hi and l <= h:
                brects.append((2*fix+offset, 2*fix+offset+1, 2*l, 2*h+1) if axis == 0 else
                              (2*l+offset, 2*h+offset+1, 2*fix, 2*fix+1))
    depths = []
    for p in xset:
        a, b = (p[0]-offset)//2, p[1]//2
        t = abs(max(abs(a-y[0]), abs(b-y[1]))-k)
        depth = min(p[0]-xmin+1, xmax-p[0]+1, p[1]-ymin+1, ymax-p[1]+1,
                    rectangle_distance(p, notch), *(rectangle_distance(p, z) for z in brects))
        assert depth >= 3
        assert depth >= (2*max(t, F(ell, 4))-5 if t <= width else F(s, 6)-3)
        depths.append(depth)
    for theta in (0.5, 0.95, 0.999):
        lhs = sum(theta**b for b in depths)
        rhs = 192*theta**(ell/2-5)*(ell/4+1+1/(1-theta**2)) + 4*(2*m+1)**2*theta**(s/6-7)
        assert lhs <= rhs
    return len(xset)


geometry_cases = 0
largest_boundary = 0
for args in product((72, 84), (20, 22), (2, 5), range(4), (0, 1)):
    largest_boundary = max(largest_boundary, geometry_check(*args))
    geometry_cases += 1

print(json.dumps({
    "symbolic_35_identity": "exact polynomial identity passed",
    "removal_constants": "all rational comparisons passed",
    "four_factor_lower_bound": str(lower4),
    "topology_nonempty_subsets_examined": 65535,
    "topology_subsets_satisfying_hypotheses": tested,
    "topology_counterexamples": 0,
    "cut_geometry_cases": geometry_cases,
    "largest_cut_boundary": largest_boundary,
    "cut_geometry_checks": "exact connectivity, depth bounds, <=48 cells per taper level; floating-point weighted sums",
}, indent=2))
