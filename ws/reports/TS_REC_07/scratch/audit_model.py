"""Finite semantic checks, not Lean proofs. Run from this report directory."""
from collections import Counter, deque
from itertools import combinations
import json
import random

DIRS = ((1, 0), (0, 1), (-1, 0), (0, -1))
TIPS = {(2, 0), (0, 2), (-2, 0), (0, -2)}
CORNERS = {(1, 1), (-1, 1), (-1, -1), (1, -1)}
TEMPLATE = {(x, y) for x in range(-2, 3) for y in range(-2, 3)
            if abs(x) + abs(y) <= 2}
NON_TIPS = TEMPLATE - TIPS
COUNTS = Counter()
RNG = random.Random(701116)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def sub(x, y):
    return x[0] - y[0], x[1] - y[1]


def dist(x, y):
    return sum(map(abs, sub(x, y)))


def neighbours(x):
    return {add(x, d) for d in DIRS}


def rotate(incoming, x):
    a, b = x
    return ((b, -a), (a, b), (-b, a), (-a, -b))[DIRS.index(incoming)]


class Network:
    def __init__(self, G, status, kept):
        self.G = G
        self.status = status
        self.kept = kept

    def st(self, x):
        return self.status.get(x, 'X')

    def ks(self, x):
        return self.kept.get(x, set())

    def active(self, x):
        return x in self.G and self.st(x) != 'X'

    def present(self, x, y):
        return (self.active(x) and self.active(y) and dist(x, y) == 1
                and y in self.ks(x) and x in self.ks(y))

    def pn(self, x):
        return {y for y in neighbours(x) if self.present(x, y)}

    def legs(self, x):
        return len(neighbours(x) - self.G) if x in self.G else 0

    def normalize(self, u, c):
        kept = self.kept.copy()
        if self.st(u) == 'U':
            kept[u] = self.ks(u) - {c}
        return Network(self.G, self.status.copy(), kept)

    def remove(self, y):
        status = self.status.copy()
        status[y] = 'X'
        return Network(self.G, status, self.kept.copy())

    def step(self, y, o):
        status, kept = self.status.copy(), self.kept.copy()
        status[y] = 'D' if self.st(y) == 'U' else 'X'
        kept[y] = self.ks(y) - {o}
        kept[o] = self.ks(o) - {y}
        return Network(self.G, status, kept)


def protected(G):
    # Existence of an exterior point at distance <= 2 is equivalent to depth <= 2.
    return {x for x in G if any(add(x, z) not in G for z in TEMPLATE)}


def auxiliary(D, S):
    assert all(D.st(x) == 'U' for x in S)
    for x in D.G:
        assert D.ks(x) <= neighbours(x) & D.G
        assert D.st(x) != 'D' or len(D.pn(x)) <= 2
        if D.active(x):
            assert len(D.pn(x)) + D.legs(x) <= 4


def mutual(D):
    for x in D.G:
        if D.active(x):
            for z in neighbours(x) & D.G:
                if D.active(z):
                    assert (z in D.ks(x)) == (x in D.ks(z))


def ordinary(D, S):
    auxiliary(D, S)
    for x in D.G:
        if D.st(x) == 'U':
            assert D.ks(x) == neighbours(x) & D.G
        if D.st(x) == 'D':
            assert len(D.ks(x)) == 2
    mutual(D)


def covered(D, y, incoming, outgoing):
    # Construct the candidate in PatternData.Covered, then check every clause.
    image = lambda z: add(y, rotate(incoming, z))
    st = {z: ('U' if z in TIPS else D.st(image(z))) for z in TEMPLATE}
    ks = {}
    for z in TEMPLATE:
        if z == (0, 0):
            ks[z] = {(1, 0), (0, 1), (-1, 0)}
        elif st[z] == 'U':
            ks[z] = neighbours(z)
        else:
            ks[z] = {add(z, d) for d in DIRS if image(add(z, d)) in D.ks(image(z))}
    out = next(d for d in DIRS if rotate(incoming, d) == outgoing)
    if out == (0, -1) or st[(0, 0)] != 'U':
        return False
    arrival = (0, -1)
    if not (st[arrival] == 'X' or
            (st[arrival] == 'D' and len(ks[arrival]) == 2 and (0, 0) not in ks[arrival])):
        return False
    for z in ((1, 0), (0, 1), (-1, 0)):
        if not (st[z] in ('U', 'X') or
                (st[z] == 'D' and len(ks[z]) == 2 and (0, 0) in ks[z])):
            return False
    if st[out] == 'X':
        return False
    for z in CORNERS:
        if not (st[z] in ('U', 'X') or (st[z] == 'D' and len(ks[z]) == 2)):
            return False
    for z in NON_TIPS:
        if st[z] != D.st(image(z)):
            return False
        if st[z] != 'X' and {image(t) for t in ks[z]} & D.G != D.ks(image(z)):
            return False
        for t in NON_TIPS & neighbours(z):
            if st[z] != 'X' and st[t] != 'X' and ((t in ks[z]) != (z in ks[t])):
                return False
    return True


def pair_check(D, S, y, a, b):
    H = D.remove(y)
    assert H.active(a) and H.active(b) and H.st(y) == 'X'
    assert y in H.G and dist(a, y) == dist(b, y) == 1
    assert dist(a, b) == 2
    collinear = a[0] == b[0] or a[1] == b[1]
    # responsePairType {a,b} agrees with HasPairType (ordered a,b).
    assert collinear or (a[0] != b[0] and a[1] != b[1])
    for z in (a, b):
        assert H.st(z) == 'U' or (H.st(z) == 'D' and len(H.pn(z)) <= 1)


def prefix_check(D, S, y, departed, first=True, defect=None):
    auxiliary(D, S)
    mutual(D)
    for x in D.G - {y, defect}:
        assert D.st(x) != 'U' or D.ks(x) == neighbours(x) & D.G
        assert D.st(x) != 'D' or len(D.ks(x)) == 2
    assert all(D.st(x) != 'U' for x in departed)
    assert D.active(y)
    if first and y not in S:
        ordinary(D.remove(y), S)
        if D.st(y) == 'U':
            for a, b in combinations(D.pn(y), 2):
                pair_check(D, S, y, a, b)
                COUNTS['response_pairs'] += 1
    COUNTS['first_prefixes' if first else 'second_prefixes'] += 1


def trail_run(D0, u, incoming, T, S, limit=25, first=True, defect=None, choices=None):
    D, y = D0, u
    used, departed, path = set(), [], [u]
    for j in range(limit + 1):
        prefix_check(D, S, y, departed, first, defect)
        if y in T:
            return D, path
        if y in S or j == limit:
            return None
        possible = [z for z in D0.pn(y) if frozenset((y, z)) not in used]
        if not possible:
            return None
        z = choices[j] if choices is not None else RNG.choice(sorted(possible))
        assert z in possible and D.present(y, z)
        if D.st(y) == 'U':
            ok = covered(D, y, incoming, sub(z, y))
            if first:
                assert ok
                COUNTS['first_U_departures'] += 1
            else:
                if not ok:
                    assert 0 < dist(y, defect) <= 2
                    COUNTS['uncovered_second_U_departures'] += 1
                COUNTS['second_U_departures'] += 1
        else:
            COUNTS['D_departures'] += 1
        D = D.step(y, z)
        departed.append(y)
        used.add(frozenset((y, z)))
        incoming, y = sub(z, y), z
        path.append(y)
    return None


def domain(G, removed, D_sites=()):
    status = {x: ('X' if x in removed else 'U') for x in G}
    kept = {x: neighbours(x) & G for x in G}
    for x, flags in D_sites:
        status[x], kept[x] = 'D', set(flags)
    return Network(G, status, kept)


def audit_domain(D, u=(-1, 0), v=(1, 0), c=(0, 0), runs=8):
    S = protected(D.G)
    ordinary(D, S)
    assert D.st(c) == 'X' and D.active(u) and D.active(v)
    assert dist(u, c) == dist(v, c) == 1 and dist(u, v) == 2
    assert u not in S and v not in S
    for x in (u, v):
        assert D.st(x) == 'U' or (D.st(x) == 'D' and len(D.pn(x)) <= 1)
    H = D.normalize(u, c)
    assert all(D.present(x, z) == H.present(x, z) for x in D.G for z in neighbours(x))
    prefix_check(H, S, u, [])  # Includes the zero-length prefix.
    for _ in range(runs):
        result = trail_run(H, u, sub(u, c), S | {v}, S)
        if result is None:
            continue
        E, path = result
        e = path[-1]
        if e not in S:
            continue
        assert E.st(e) == 'U'
        assert all(E.ks(x) == neighbours(x) & D.G for x in S - {e})
        COUNTS['terminal_S_trails'] += 1
        E = E.normalize(v, c)
        auxiliary(E, S)
        assert E.active(v) and not E.present(c, v)
        assert ((E.st(v) == 'U' and len(E.pn(v)) <= 3) or
                (E.st(v) == 'D' and len(E.pn(v)) <= 1))
        assert E.active(e) and E.st(e) == 'U' and len(E.pn(e)) + E.legs(e) <= 3
        COUNTS['second_starts'] += 1
        trail_run(E, v, sub(v, c), S, S, first=False, defect=e)


def main():
    square = {(x, y) for x in range(-4, 5) for y in range(-4, 5)}
    S = protected(square)
    interior = sorted({x for x in square - S if max(map(abs, x)) <= 1}
                      - {(-1, 0), (1, 0), (0, 0)})
    # U/X domains on every removal choice in the small interior square.
    for mask in range(1 << len(interior)):
        removed = {(0, 0)} | {x for i, x in enumerate(interior) if mask & (1 << i)}
        audit_domain(domain(square, removed), runs=4)
        COUNTS['domains'] += 1
    # An initial D endpoint with one present and one removed-centre kept flag.
    u, v, c = (-1, 0), (1, 0), (0, 0)
    removed = {c, (-1, -1), (-2, 0)}
    audit_domain(domain(square, removed, [(u, {c, (-1, 1)})]), runs=80)
    COUNTS['domains'] += 1
    # Boundary corners with original legs: translated taxicab ball from repo Counterexample.
    ball = {(x, y) for x in range(-6, 3) for y in range(-4, 5)
            if dist((x, y), (-2, 0)) <= 4}
    D = domain(ball, {(-1, 0)})
    ordinary(D, protected(ball))
    assert covered(D.normalize((0, 0), (-1, 0)), (0, 0), (1, 0), (1, 0))
    audit_domain(D, u=(0, 0), v=(-2, 0), c=(-1, 0), runs=12)
    COUNTS['domains'] += 1
    COUNTS['boundary_corner_checks'] += 1
    # Concrete nonvacuous exception at second departure (1,2), distance two from e=(0,3).
    D = domain(square, {(0, 0)})
    H = D.normalize((-1, 0), (0, 0))
    first_path = [(-1, 1), (0, 1), (0, 2), (0, 3)]
    E, _ = trail_run(H, (-1, 0), (-1, 0), protected(square) | {(1, 0)}, protected(square), choices=first_path)
    E = E.normalize((1, 0), (0, 0))
    trail_run(E, (1, 0), (1, 0), protected(square), protected(square), first=False,
              defect=(0, 3), choices=[(1, 1), (1, 2), (1, 3)])
    loop = [(-1, 1), (-2, 1), (-2, 0), (-1, 0), (-1, -1), (-1, -2), (-1, -3)]
    trail_run(H, (-1, 0), (-1, 0), protected(square) | {(1, 0)}, protected(square), choices=loop)
    COUNTS['explicit_U_revisit_trails'] += 1
    print(json.dumps(dict(sorted(COUNTS.items())), indent=2))


if __name__ == '__main__':
    main()
