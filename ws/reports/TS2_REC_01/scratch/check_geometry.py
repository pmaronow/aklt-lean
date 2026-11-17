"""Finite definition checks for the truth sweep; this file contains no Lean proofs."""
from itertools import combinations
import json
import random

RNG = random.Random(20261116)
STEP = {'east': (1, 0), 'north': (0, 1), 'west': (-1, 0), 'south': (0, -1)}
T = {(x, y) for x in range(-2, 3) for y in range(-2, 3) if abs(x) + abs(y) <= 2}
TIPS = {(2, 0), (0, 2), (-2, 0), (0, -2)}
CORNERS = {(1, 1), (-1, 1), (-1, -1), (1, -1)}
NT = T - TIPS
ORIGIN = (0, 0)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def neighbours(x):
    return {add(x, d) for d in STEP.values()}


def rotation(direction, z):
    x, y = z
    return {'north': (x, y), 'east': (y, -x),
            'south': (-x, -y), 'west': (-y, x)}[direction]


def inverse(direction, z):
    return rotation({'north': 'north', 'east': 'west',
                     'south': 'south', 'west': 'east'}[direction], z)


def protected(G):
    return {x for x in G if any(add(x, d) not in G for d in T)}


class Network:
    def __init__(self, G, status, kept=None):
        self.G = G
        self.S = protected(G)
        self.status = status
        self.kept = kept if kept is not None else {x: neighbours(x) & G for x in G}

    def st(self, x):
        return self.status.get(x, 'X')

    def present(self, x, y):
        return (x in self.G and y in self.G and self.st(x) != 'X' and self.st(y) != 'X'
                and y in neighbours(x) and y in self.kept[x] and x in self.kept[y])

    def pn(self, x):
        return {z for z in neighbours(x) if self.present(x, z)}

    def bonds(self):
        return {frozenset((x, z)) for x in self.G for z in self.pn(x)}

    def auxiliary(self):
        return (all(k <= neighbours(x) & self.G for x, k in self.kept.items())
                and all(self.st(x) != 'D' or len(self.pn(x)) <= 2 for x in self.G)
                and all(self.st(x) == 'U' for x in self.S)
                and all(len(self.pn(x)) + len(neighbours(x) - self.G) <= 4
                        for x in self.G if self.st(x) != 'X'))

    def consistent(self):
        return (self.auxiliary()
                and all(self.kept[x] == neighbours(x) & self.G
                        for x in self.G if self.st(x) == 'U')
                and all(len(self.kept[x]) == 2 for x in self.G if self.st(x) == 'D')
                and all((z in self.kept[x]) == (x in self.kept[z])
                        for x in self.G if self.st(x) != 'X'
                        for z in neighbours(x) & self.G if self.st(z) != 'X'))

    def normalized(self, u, c):
        kept = {x: k.copy() for x, k in self.kept.items()}
        if self.st(u) == 'U':
            kept[u].discard(c)
        return Network(self.G, self.status.copy(), kept)

    def trace(self, y, o):
        status = self.status.copy()
        status[y] = 'D' if self.st(y) == 'U' else 'X'
        kept = {x: k.copy() for x, k in self.kept.items()}
        kept[y].discard(o)
        kept[o].discard(y)
        return Network(self.G, status, kept)


class Pattern:
    def __init__(self, status, kept, outgoing):
        self.status, self.kept, self.outgoing = status, kept, outgoing

    def internal(self, z, t):
        return (z in T and t in T and t in neighbours(z)
                and self.status[z] != 'X' and self.status[t] != 'X'
                and (z in TIPS or t in self.kept[z])
                and (t in TIPS or z in self.kept[t]))

    def covered(self):
        s, k = self.status, self.kept
        return (self.outgoing != 'south' and s[ORIGIN] == 'U'
                and k[ORIGIN] == {(1, 0), (0, 1), (-1, 0)}
                and (s[(0, -1)] == 'X' or
                     (s[(0, -1)] == 'D' and len(k[(0, -1)]) == 2
                      and ORIGIN not in k[(0, -1)]))
                and all(s[z] in ('U', 'X') or (s[z] == 'D' and len(k[z]) == 2
                                              and ORIGIN in k[z])
                        for z in ((1, 0), (0, 1), (-1, 0)))
                and s[STEP[self.outgoing]] != 'X'
                and all(s[z] in ('U', 'X') or (s[z] == 'D' and len(k[z]) == 2)
                        for z in CORNERS)
                and all(s[z] != 'U' or k[z] == neighbours(z) for z in NT - {ORIGIN})
                and all(s[z] == 'U' for z in TIPS)
                and all((t in k[z]) == (z in k[t]) for z in NT for t in NT
                        if s[z] != 'X' and s[t] != 'X' and t in neighbours(z)))

    def shared(self, E, y, incoming, outgoing):
        chart = lambda z: add(y, rotation(incoming, z))
        return (self.covered() and rotation(incoming, STEP[self.outgoing]) == STEP[outgoing]
                and all(self.status[z] == E.st(chart(z)) for z in NT)
                and all((not E.present(chart(z), chart(t)) or self.internal(z, t))
                        if t in TIPS else (self.internal(z, t) == E.present(chart(z), chart(t)))
                        for z in NT for t in T))

    def legacy(self, E, y, incoming, outgoing):
        chart = lambda z: add(y, rotation(incoming, z))
        return (self.covered() and rotation(incoming, STEP[self.outgoing]) == STEP[outgoing]
                and all(self.status[z] == E.st(chart(z)) and
                        (self.status[z] == 'X' or {chart(t) for t in self.kept[z]} & E.G
                         == E.kept[chart(z)]) for z in NT))


def pattern_at(E, y, incoming, outgoing):
    chart = lambda z: add(y, rotation(incoming, z))
    status = {z: 'U' if z in TIPS else E.st(chart(z)) for z in T}
    kept = {}
    for z in T:
        if z == ORIGIN:
            kept[z] = {(1, 0), (0, 1), (-1, 0)}
        elif status[z] == 'D':
            kept[z] = {inverse(incoming, sub(t, y)) for t in E.kept[chart(z)]}
        else:
            kept[z] = neighbours(z)
    out_step = inverse(incoming, STEP[outgoing])
    out = next(d for d in STEP if STEP[d] == out_step)
    return Pattern(status, kept, out)


def check_trace(E, start, incoming, vertices, counts):
    original = E.bonds()
    used = set()
    departed = set()
    counts['stopped_trails'] += 1
    for y, o in zip(vertices, vertices[1:]):
        assert y not in E.S and E.auxiliary()
        assert E.present(y, o)
        assert E.bonds() == original - used
        assert E.st(y) in ('U', 'D')
        assert len(E.pn(y)) <= (3 if E.st(y) == 'U' else 1)
        assert y not in departed or E.st(y) == 'D'
        if E.st(y) == 'U':
            out = next(d for d in STEP if STEP[d] == sub(o, y))
            p = pattern_at(E, y, incoming, out)
            assert p.covered() and p.shared(E, y, incoming, out)
            assert p.legacy(E, y, incoming, out)
            counts['covered_U_departures'] += 1
            counts['extra_cover_tip_bonds'] += sum(
                p.internal(z, t) and not E.present(add(y, rotation(incoming, z)),
                                                 add(y, rotation(incoming, t)))
                for z in NT for t in TIPS)
        else:
            counts['D_departures'] += 1
        incoming = next(d for d in STEP if STEP[d] == sub(o, y))
        departed.add(y)
        used.add(frozenset((y, o)))
        E = E.trace(y, o)
    assert E.auxiliary() and E.bonds() == original - used
    assert E.st(vertices[-1]) == 'U'


def random_stopped(E, u, maxlen=80):
    vertices, used = [u], set()
    while len(vertices) <= maxlen:
        y = vertices[-1]
        if y in E.S:
            return vertices
        choices = sorted(z for z in E.pn(y) if frozenset((y, z)) not in used)
        if not choices:
            return None
        z = RNG.choice(choices)
        used.add(frozenset((y, z)))
        vertices.append(z)
    return None


def main():
    counts = {'boundary_internal_obligations': len(NT) * len(T), 'stopped_trails': 0,
              'covered_U_departures': 0, 'D_departures': 0, 'D_starts': 0,
              'extra_cover_tip_bonds': 0, 'mixed_status_domains': 0}
    G = {(x, y) for x in range(-6, 3) for y in range(-4, 5)
         if abs(x + 2) + abs(y) <= 4}
    D = Network(G, {x: 'X' if x == (-1, 0) else 'U' for x in G})
    assert len(G) == 41 and D.consistent()
    E = D.normalized((0, 0), (-1, 0))
    P = pattern_at(E, (0, 0), 'east', 'east')
    assert P.covered() and P.shared(E, (0, 0), 'east', 'east')
    assert P.legacy(E, (0, 0), 'east', 'east')
    assert len(E.kept[(1, 1)]) == 2 and (2, 1) not in G and (1, 2) not in G
    for _ in range(150):
        w = random_stopped(E, (0, 0))
        if w:
            check_trace(E, (0, 0), 'east', w, counts)

    G = {(x, y) for x in range(-4, 5) for y in range(-4, 5)}
    S = protected(G)
    u, v, c = (1, 0), (0, 1), (0, 0)
    for j in range(160):
        status = {x: ('X' if x not in S and RNG.random() < 0.32 else 'U') for x in G}
        status[c], status[u], status[v] = 'X', 'U', 'U'
        if j % 4 == 0:
            status[(2, 0)] = status[(1, -1)] = 'X'
            status[(1, 1)] = 'U'
            status[u] = 'D'
        D = Network(G, status)
        for x in sorted(G - S):
            if x not in (u, v, c) and (x[0] + x[1]) % 2 == 0 and status[x] == 'U':
                alive = {z for z in neighbours(x) if status[z] != 'X'}
                if len(alive) <= 2 and RNG.random() < 0.7:
                    status[x] = 'D'
        for x in sorted(G):
            if status[x] == 'D':
                alive = {z for z in neighbours(x) if status[z] != 'X'}
                # D candidates are pairwise nonadjacent, including the chosen D start.
                if any(status[z] == 'D' for z in alive) or len(alive) > 2:
                    status[x] = 'U'
                else:
                    missing = sorted(neighbours(x) - alive)
                    D.kept[x] = alive | set(RNG.sample(missing, 2 - len(alive)))
        if not D.consistent():
            # Reject a sample if reverting a D neighbour changed a mandatory flag.
            continue
        assert status[c] == 'X' and status[v] == 'U'
        assert status[u] == 'U' or len(D.pn(u)) <= 1
        counts['mixed_status_domains'] += 1
        E = D.normalized(u, c)
        assert E.bonds() == D.bonds() and not E.present(c, u)
        for _ in range(24):
            w = random_stopped(E, u)
            if w:
                counts['D_starts'] += E.st(u) == 'D'
                check_trace(E, u, 'east', w, counts)
    print(json.dumps(counts, indent=2))


if __name__ == '__main__':
    main()
