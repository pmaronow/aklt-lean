"""Finite sanity checks for the truth audit; these are not Lean proofs."""
from fractions import Fraction as Q
from itertools import product
from math import isclose, prod, sqrt


def crude(s):
    t = (1 - s) / (1 + s)
    return 2 / (1 - s) * (t + t**3 / 3 + t**5 / (5 * (1 - t**2)))


b = crude(Q(22, 25)) / 3
bound = Q(35510, 100000)
assert b == Q(24332081, 68523180)
assert bound - b == Q(250109, 34261590000) > 0
print(f'Exact beta-prime endpoint: B(22/25)/3 = {b}')
print(f'Exact positive gap to 35510/100000: {bound - b}')

phi = (1 + sqrt(5)) / 2
radius = sqrt(phi + 2)
atoms = [(0.0, 0.0, 0.0)]
for group, a, sign in product(range(3), (1, -1), (1, -1)):
    v = ((0, a, sign * phi), (a, sign * phi, 0), (sign * phi, 0, a))[group]
    atoms.append(tuple(x / radius for x in v))
weights = {'U': [0.0] + [1 / 12] * 12, 'D': [2 / 5] + [1 / 20] * 12}


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


assert len(set(atoms[1:])) == 12
assert all(isclose(dot(a, a), 1, abs_tol=1e-14) for a in atoms[1:])
monomials = [(i, j, k) for i, j, k in product(range(5), repeat=3) if i + j + k <= 4]
for exps in monomials:
    degree = sum(exps)
    if degree == 0:
        expected = Q(1)
    elif any(e % 2 for e in exps):
        expected = Q(0)
    elif degree == 2:
        expected = Q(1, 3)
    elif max(exps) == 4:
        expected = Q(1, 5)
    else:
        expected = Q(1, 15)
    for status in weights:
        actual = sum(w * prod(x**e for x, e in zip(a, exps))
                     for w, a in zip(weights[status], atoms))
        target = expected * (Q(3, 5) if status == 'D' and degree else 1)
        assert isclose(actual, float(target), abs_tol=2e-14), (status, exps, actual, target)
print(f'Checked 12 distinct unit atoms and {len(monomials)} moments through degree four for each U/D law.')


def neighbours(v):
    x, y = v
    return {(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)}


def dist(a, b):
    return abs(a[0] - b[0]) + abs(a[1] - b[1])


y = (0, 0)
volume = {v for v in product(range(-2, 3), repeat=2) if dist(v, y) <= 2}
exterior = set(product(range(-3, 4), repeat=2)) - volume
depth = {v: min(dist(v, w) for w in exterior) for v in volume}
protected = {v for v in volume if depth[v] <= 2}
legs = {(v, w) for v in volume for w in neighbours(v) - volume}
assert len(volume) == 13 and depth[y] == 3 and y not in protected
assert all(not any(v == z for z, _ in legs) for v in neighbours(y))


def present(status, kept, a, b):
    return status.get(a, 'X') != 'X' and status.get(b, 'X') != 'X' and \
        b in neighbours(a) and b in kept[a] and a in kept[b]


def actual_neighbours(status, kept, a):
    return {b for b in neighbours(a) if present(status, kept, a, b)}


def auxiliary(status, kept):
    assert all(kept[v] <= neighbours(v) & volume for v in volume)
    assert all(status[v] == 'U' for v in protected)
    for v in volume:
        degree = len(actual_neighbours(status, kept, v))
        assert status[v] != 'D' or degree <= 2
        assert status[v] == 'X' or degree + sum(z == v for z, _ in legs) <= 4


def partition(status, kept, pinned, observed=()):
    active = {v for v in volume if status[v] != 'X'}
    bonds = [(a, b) for a in sorted(active) for b in sorted(active)
             if a < b and present(status, kept, a, b)]
    core = sorted({v for e in bonds for v in e} | (set(observed) & active))
    isolated = active - set(core)
    # All original pins are the unit vector (1,0,0); isolated factors are summed exactly as finite local sums.
    def local(v, letter):
        return weights[status[v]][letter] * ((1 + atoms[letter][0]) ** sum(z == v for z, _ in legs) if pinned else 1)
    outside = prod(sum(local(v, j) for j in range(13)) for v in isolated)
    total = 0.0
    for letters in product(range(13), repeat=len(core)):
        n = dict(zip(core, letters))
        term = prod(local(v, n[v]) for v in core)
        term *= prod(1 + dot(atoms[n[a]], atoms[n[b]]) for a, b in bonds)
        if observed:
            term *= dot(atoms[n[observed[0]]], atoms[n[observed[1]]])
        total += term
    return outside * total


for start_status, degree in [('U', 1), ('U', 2), ('U', 3), ('D', 1)]:
    status = {v: 'U' for v in volume}
    status[y] = start_status
    kept = {v: set() for v in volume}
    outgoing = [(1, 0), (-1, 0), (0, 1)][:degree]
    for v in outgoing:
        kept[y].add(v)
        kept[v].add(y)
    auxiliary(status, kept)
    assert (start_status == 'U' and degree <= 3) or (start_status == 'D' and degree <= 1)
    o = outgoing[0]
    traced_status = dict(status)
    traced_status[y] = 'D' if start_status == 'U' else 'X'
    traced_kept = {v: set(s) for v, s in kept.items()}
    traced_kept[y].discard(o)
    traced_kept[o].discard(y)
    auxiliary(traced_status, traced_kept)
    removed_status = dict(status)
    removed_status[y] = 'X'
    auxiliary(removed_status, kept)
    for pinned in [False, True]:
        pre = partition(status, kept, pinned)
        post = partition(traced_status, traced_kept, pinned)
        assert pre > 0 and post > 0
        assert isclose(post / pre, 1, abs_tol=2e-12)
        if degree == 2:
            pair = partition(removed_status, kept, pinned, tuple(outgoing)) / partition(removed_status, kept, pinned)
            assert isclose(pair, 0, abs_tol=2e-14)
    print(f'Nonvacuous diamond-volume example: start={start_status}, present degree={degree}; both ratios=1.')
print('The two-neighbour example has both I2 values equal to one, so its diagonal beta-prime is 1/3.')
print('All finite sanity checks passed; these examples do not establish the universal statements.')
