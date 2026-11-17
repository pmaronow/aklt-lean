"""Finite diagnostic checks for TS_H1M_04; no Lean proofs or dependencies."""

from fractions import Fraction as Q
from itertools import product
from math import isclose, sqrt
from random import Random


SITES = tuple(sorted((x, y) for x in range(-2, 3) for y in range(-2, 3)
                     if abs(x) + abs(y) <= 2))
CORNERS = ((1, 1), (-1, 1), (-1, -1), (1, -1))
TIPS = ((2, 0), (0, 2), (-2, 0), (0, -2))
OUTER = CORNERS + TIPS
O = (0, 0)
SOUTH = (0, -1)
DIRS = ((1, 0), (0, 1), (-1, 0), (0, -1))
SLOTS = tuple(x for x in CORNERS for _ in range(2)) + tuple(
    x for x in TIPS for _ in range(3))
LEADER = dict(zip(OUTER, (0, 2, 4, 6, 8, 11, 14, 17)))


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


EDGES = tuple((x, add(x, d)) for x in SITES for d in DIRS[:2]
              if add(x, d) in SITES)
assert len(SITES) == 13 and len(EDGES) == 16 and len(SLOTS) == 20


def degree(edges, x):
    return sum(x in e for e in edges)


def retained(active, edges, reduced):
    return set(x for x in active if x not in TIPS and
               (x not in CORNERS or
                (degree(edges, x) != 0 and not (reduced and degree(edges, x) == 1))))


def check_geometry():
    count = 0
    for mask in range(1 << len(EDGES)):
        edges = [e for i, e in enumerate(EDGES) if mask & (1 << i)]
        deg = {x: degree(edges, x) for x in SITES}
        for reduced in (False, True):
            keep = set(x for x in SITES if x not in TIPS and
                       (x not in CORNERS or (deg[x] != 0 and not (reduced and deg[x] == 1))))
            deleted = set(SITES) - keep
            for x in deleted:
                assert x in OUTER and deg[x] <= 1
                if deg[x] == 1:
                    e = next(e for e in edges if x in e)
                    y = e[1] if x == e[0] else e[0]
                    assert y in keep
                assert all(abs(x[0] - y[0]) + abs(x[1] - y[1]) != 1 for y in deleted)
            count += 1
    print(f"Peripheral geometry: {count} bond-subset/representation cases passed.")


def check_tokens():
    count = 0
    for corners in product((0, 1, 2), repeat=4):
        for tips in product((0, 1), repeat=4):
            used = []
            for x, size in zip(OUTER, corners + tips):
                block = [LEADER[x] + i for i in range(size)]
                assert all(0 <= j < 20 and j not in used for j in block)
                used += block
            count += 1
    print(f"Token allocation: {count} absent/single/pair allocations are disjoint.")


def matadd(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def kron(a, b):
    return [[x * y for x in ar for y in br] for ar in a for br in b]


def action(a, v):
    return tuple(sum(x * y for x, y in zip(row, v)) for row in a)


def scale(c, v):
    return tuple(c * x for x in v)


def check_ladders():
    ident = [[1, 0], [0, 1]]
    z = [[Q(1, 2), 0], [0, -Q(1, 2)]]
    plus = [[0, 1], [0, 0]]
    minus = [[0, 0], [1, 0]]
    ep, em = (1, 0), (0, 1)
    assert action(z, ep) == scale(Q(1, 2), ep)
    assert action(z, em) == scale(-Q(1, 2), em)
    assert action(plus, ep) == action(minus, em) == (0, 0)
    assert action(plus, em) == ep and action(minus, ep) == em
    zp, pp, mp = [matadd(kron(a, ident), kron(ident, a)) for a in (z, plus, minus)]
    vp, v0, vm, w = (1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1), (0, 1, -1, 0)
    zero = (0, 0, 0, 0)
    assert [action(zp, v) for v in (vp, v0, vm, w)] == [vp, zero, scale(-1, vm), zero]
    assert [action(pp, v) for v in (vp, v0, vm, w)] == [zero, scale(2, vp), v0, zero]
    assert [action(mp, v) for v in (vp, v0, vm, w)] == [v0, scale(2, vm), zero, zero]
    print("Spin actions: exact rational single, symmetric-pair, and exterior-pair tables passed.")


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


PHI = (1 + sqrt(5)) / 2
RADIUS = sqrt(PHI + 2)
ATOMS = [(0.0, 0.0, 0.0)]
for g, s, t in product(range(3), (1, -1), (1, -1)):
    a, b = s, t * PHI
    v = ((0, a, b), (a, b, 0), (b, 0, a))[g]
    ATOMS.append(tuple(c / RADIUS for c in v))
assert all(isclose(dot(v, v), 1, abs_tol=1e-14) for v in ATOMS[1:])


def weights(status):
    return [0 if status == 'U' else 2 / 5] + [1 / 12 if status == 'U' else 1 / 20] * 12


def site_field(m, x, v):
    ans = 1.0
    for j, site in enumerate(SLOTS):
        if site == x:
            ans *= 1 + dot(m[j], v)
    return ans


def covered(st, kept, outgoing):
    at = lambda x: st.get(x, 'X')
    neigh = lambda x: {add(x, d) for d in DIRS}
    assert outgoing != SOUTH and at(O) == 'U'
    assert kept[O] == {(1, 0), (0, 1), (-1, 0)}
    assert at(SOUTH) == 'X' or (at(SOUTH) == 'D' and len(kept[SOUTH]) == 2 and O not in kept[SOUTH])
    for d in DIRS[:3]:
        assert at(d) in ('U', 'X') or (at(d) == 'D' and len(kept[d]) == 2 and O in kept[d])
    assert at(outgoing) != 'X'
    for x in CORNERS:
        assert at(x) in ('U', 'X') or (at(x) == 'D' and len(kept[x]) == 2)
    for x in SITES:
        if x != O and x not in TIPS and at(x) == 'U':
            assert kept[x] == neigh(x)
    assert all(at(x) == 'U' for x in TIPS)
    for x in SITES:
        for y in SITES:
            if x not in TIPS and y not in TIPS and at(x) != 'X' and at(y) != 'X' and y in neigh(x):
                assert (y in kept[x]) == (x in kept[y])
    return [(x, y) for x, y in EDGES if at(x) != 'X' and at(y) != 'X' and
            (x in TIPS or y in kept[x]) and (y in TIPS or x in kept[y])]


def partition(unary, edges):
    """Direct finite factor elimination, over all 13 SpinLetter values."""
    factors = [((x,), list(values)) for x, values in unary.items()]
    factors += [((x, y), [1 + dot(a, b) for a in ATOMS for b in ATOMS]) for x, y in edges]
    remaining = set(unary)
    while remaining:
        def neighbours(x):
            return set(v for scope, _ in factors if x in scope for v in scope) - {x}
        x = min(remaining, key=lambda v: (len(neighbours(v)), v))
        bucket = [f for f in factors if x in f[0]]
        factors = [f for f in factors if x not in f[0]]
        rest = tuple(sorted(set(v for scope, _ in bucket for v in scope) - {x}))
        scope = (x,) + rest
        projections = [(tuple(scope.index(v) for v in old_scope), values)
                       for old_scope, values in bucket]
        result = []
        for assignment in product(range(13), repeat=len(rest)):
            total = 0.0
            for letter in range(13):
                values = (letter,) + assignment
                term = 1.0
                for positions, table in projections:
                    index = 0
                    for pos in positions:
                        index = index * 13 + values[pos]
                    term *= table[index]
                total += term
            result.append(total)
        factors.append((rest, result))
        remaining.remove(x)
    answer = 1.0
    for scope, values in factors:
        assert not scope and len(values) == 1
        answer *= values[0]
    return answer


def fixtures():
    for outgoing in DIRS[:3]:
        for d_corners in (False, True):
            st = {x: 'U' for x in SITES if x != SOUTH}
            kept = {x: {add(x, d) for d in DIRS} for x in SITES}
            kept[O] = set(DIRS[:3])
            if d_corners:
                for x in CORNERS:
                    st[x] = 'D'
                kept[(1, 1)] = {(1, 0), (0, 1)}
                kept[(-1, 1)] = {(-1, 0), (0, 1)}
                kept[(-1, -1)] = {(-1, 0), (-2, -1)}
                kept[(1, -1)] = {(1, 0), (2, -1)}
            yield st, kept, outgoing
    for more_d in (False, True):
        st = {O: 'U', (1, 0): 'D' if more_d else 'U', **{x: 'U' for x in TIPS}}
        kept = {x: {add(x, d) for d in DIRS} for x in SITES}
        kept[O] = set(DIRS[:3])
        if more_d:
            kept[(1, 0)] = {O, (2, 0)}
            st[SOUTH] = 'D'
            kept[SOUTH] = {(1, -1), (-1, -1)}
            st[(-1, 1)] = 'D'
            kept[(-1, 1)] = {(-2, 1), (-1, 2)}
        yield st, kept, (1, 0)


def check_functionals():
    rng = Random(104)
    random_pins = []
    for _ in range(20):
        v = tuple(rng.uniform(-1, 1) for _ in range(3))
        random_pins.append(scale(1 / sqrt(dot(v, v)), v))
    pins = [[(0, 0, 1)] * 20,
            [(0, 0, 1 if j % 2 == 0 else -1) for j in range(20)], random_pins]
    cases, worst = 0, 0.0
    for st, kept, outgoing in fixtures():
        edges = covered(st, kept, outgoing)
        active = set(st)
        for reduced, m in product((False, True), pins):
            retain = retained(active, edges, reduced)
            deleted = active - retain
            groups = [x for x in OUTER if degree(edges, x) > 0]
            pair = lambda x: x in CORNERS and not (reduced and degree(edges, x) == 1)
            rho = lambda x: 3 / 5 if x in TIPS else (1 / 2 if st[x] == 'U' else 1 / 3)
            u = [(0, 0, 0)] * 20
            K = 1.0
            integrated = {}
            for x in deleted:
                f = [w * site_field(m, x, n) for w, n in zip(weights(st[x]), ATOMS)]
                A = sum(f)
                assert A > 0
                K *= A
                if degree(edges, x) == 0:
                    integrated[x] = (None, [A])
                else:
                    e = next(e for e in edges if x in e)
                    y = e[1] if x == e[0] else e[0]
                    assert y in retain
                    integrated[x] = (y, [sum(a * (1 + dot(n, v)) for a, n in zip(f, ATOMS))
                                         for v in ATOMS])
                    mean = tuple(sum(a * n[k] for a, n in zip(f, ATOMS)) / A for k in range(3))
                    u[LEADER[x]] = scale(1 / rho(x), mean)
            for x in groups:
                if pair(x):
                    assert x in retain
                    u[LEADER[x]] = m[LEADER[x]]
                    u[LEADER[x] + 1] = m[LEADER[x] + 1]
            assert all(dot(v, v) <= 1 + 1e-12 for v in u)
            for nxt in (False, True):
                present_edges = [e for e in edges if not (nxt and set(e) == {O, outgoing})]
                law = lambda x: 'D' if nxt and x == O else st[x]
                original = {x: [w * site_field(m, x, v) for w, v in zip(weights(law(x)), ATOMS)]
                            for x in active}
                original_value = partition(original, present_edges)
                separated = {x: [w * site_field(m, x, v) for w, v in zip(weights(law(x)), ATOMS)]
                             for x in retain}
                scalar = 1.0
                for y, vals in integrated.values():
                    if y is None:
                        scalar *= vals[0]
                    else:
                        separated[y] = [a * b for a, b in zip(separated[y], vals)]
                retained_edges = [e for e in present_edges if set(e) <= retain]
                separated_value = scalar * partition(separated, retained_edges)
                raw = {x: weights(law(x)) for x in retain}
                for x in groups:
                    j = LEADER[x]
                    if pair(x):
                        raw[x] = [w * (1 + dot(v, u[j])) * (1 + dot(v, u[j + 1]))
                                  for w, v in zip(raw[x], ATOMS)]
                    else:
                        e = next(e for e in edges if x in e)
                        y = e[1] if x == e[0] else e[0]
                        raw[y] = [w * (1 + rho(x) * dot(v, u[j])) for w, v in zip(raw[y], ATOMS)]
                reduced_value = K * partition(raw, retained_edges)
                for value in (separated_value, reduced_value):
                    error = abs(value - original_value) / max(1, abs(original_value))
                    worst = max(worst, error)
                    assert error < 1e-11, (st, reduced, nxt, original_value, value)
                cases += 1
    print(f"Finite functionals: {cases} covered fixture/representation/pin/next cases passed.")
    print(f"Largest relative error against the original 13-atom functional: {worst:.3g}.")


if __name__ == '__main__':
    check_geometry()
    check_tokens()
    check_ladders()
    check_functionals()
