"""Finite semantic checks of the audited definitions; no Lean proofs.

These checks complement the general arguments in report.md. They are not an
exhaustive verification of the universally quantified leaves.
"""

from collections import Counter
from itertools import combinations, product
from random import Random
import json

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
add = lambda a, b: (a[0] + b[0], a[1] + b[1])
sub = lambda a, b: (a[0] - b[0], a[1] - b[1])
dist = lambda a, b: abs(a[0] - b[0]) + abs(a[1] - b[1])
neighbours = lambda a: {add(a, d) for d in STEPS}
bond = lambda a, b: frozenset((a, b))
TEMPLATE = {z for z in product(range(-2, 3), repeat=2) if dist(z, (0, 0)) <= 2}
TIPS = {(2, 0), (0, 2), (-2, 0), (0, -2)}
NON_TIPS = TEMPLATE - TIPS
CORNERS = set(product((-1, 1), repeat=2))
counts = Counter()


class Network:
    def __init__(self, volume, removed=(), d_kept=None):
        self.g = set(volume)
        # Exactly distance <= 2 from the original exterior, restricted to G.
        self.s = {x for x in self.g if any(add(x, z) not in self.g for z in TEMPLATE)}
        self.status = {x: "X" if x in removed else "U" for x in self.g}
        self.kept = {x: neighbours(x) & self.g for x in self.g}
        for x, kept in (d_kept or {}).items():
            self.status[x] = "D"
            self.kept[x] = set(kept)

    def copy(self):
        other = Network(self.g)
        other.status = self.status.copy()
        other.kept = {x: set(k) for x, k in self.kept.items()}
        return other

    def active(self, x):
        return self.status.get(x, "X") != "X"

    def present(self, x, y):
        return (self.active(x) and self.active(y) and dist(x, y) == 1
                and y in self.kept[x] and x in self.kept[y])

    def degree(self, x):
        return sum(self.present(x, y) for y in neighbours(x))

    def consistent(self):
        for x in self.g:
            if not self.kept[x] <= neighbours(x) & self.g:
                return False
            if (x in self.s or self.status[x] == "U") and (
                    self.status[x] != "U" or self.kept[x] != neighbours(x) & self.g):
                return False
            if self.status[x] == "D" and (len(self.kept[x]) != 2 or self.degree(x) > 2):
                return False
            if self.active(x):
                if self.degree(x) + len(neighbours(x) - self.g) > 4:
                    return False
                for y in neighbours(x) & self.g:
                    if self.active(y) and ((y in self.kept[x]) != (x in self.kept[y])):
                        return False
        return True

    def normalize(self, u, c):
        out = self.copy()
        if out.status[u] == "U":
            out.kept[u].discard(c)
        return out

    def step(self, y, o):
        self.status[y] = "D" if self.status[y] == "U" else "X"
        self.kept[y].discard(o)
        self.kept[o].discard(y)


def rotate(incoming, z):
    if incoming == (0, 1):
        return z
    if incoming == (1, 0):
        return z[1], -z[0]
    if incoming == (0, -1):
        return -z[0], -z[1]
    return -z[1], z[0]


def constructed_cover(net, y, incoming, outgoing):
    """Check a specific covering witness, not nonexistence of other witnesses."""
    chart = {z: add(y, rotate(incoming, z)) for z in TEMPLATE}
    if not set(chart.values()) <= net.g:
        return False
    status = {z: "U" if z in TIPS else net.status[chart[z]] for z in TEMPLATE}
    kept = {}
    for z in TEMPLATE:
        if z == (0, 0):
            kept[z] = {(1, 0), (0, 1), (-1, 0)}
        elif status[z] == "U":
            kept[z] = neighbours(z)
        else:
            kept[z] = {add(z, d) for d in STEPS
                       if add(chart[z], rotate(incoming, d)) in net.kept[chart[z]]}
    out = next(d for d in STEPS if rotate(incoming, d) == outgoing)
    if out == (0, -1) or status[(0, 0)] != "U" or status[out] == "X":
        return False
    arrival = (0, -1)
    if status[arrival] != "X" and not (
            status[arrival] == "D" and len(kept[arrival]) == 2
            and (0, 0) not in kept[arrival]):
        return False
    for z in {(1, 0), (0, 1), (-1, 0)}:
        if status[z] == "D" and (len(kept[z]) != 2 or (0, 0) not in kept[z]):
            return False
    if any(status[z] == "D" and len(kept[z]) != 2 for z in CORNERS):
        return False
    for z in NON_TIPS:
        for t in NON_TIPS:
            if (status[z] != "X" and status[t] != "X" and dist(z, t) == 1
                    and ((t in kept[z]) != (z in kept[t]))):
                return False

    def pattern_present(z, t):
        return (dist(z, t) == 1 and status[z] != "X" and status[t] != "X"
                and (z in TIPS or t in kept[z]) and (t in TIPS or z in kept[t]))

    for z in NON_TIPS:
        for t in TEMPLATE:
            actual = net.present(chart[z], chart[t])
            template = pattern_present(z, t)
            if (t in TIPS and actual and not template) or (t not in TIPS and actual != template):
                return False
    return True


def check_response_pairs(net, y, incoming):
    deleted = net.copy()
    deleted.status[y] = "X"
    assert deleted.consistent()
    endpoints = (neighbours(y) - {sub(y, incoming)}) & net.g
    endpoints = {x for x in endpoints if net.active(x)}
    for a, b in combinations(endpoints, 2):
        assert dist(a, b) == 2
        assert deleted.active(a) and deleted.active(b)
        assert all(deleted.status[x] == "U" or
                   (deleted.status[x] == "D" and deleted.degree(x) <= 1) for x in (a, b))
        counts["response_pairs"] += 1


def check_path(initial, vertices, incoming, closure=False, defect=None):
    """Require the fixed-network stopped-trail conditions, then inspect prefixes."""
    assert all(initial.present(a, b) for a, b in zip(vertices, vertices[1:]))
    edges = [bond(a, b) for a, b in zip(vertices, vertices[1:])]
    assert len(set(edges)) == len(edges)
    assert all(y not in initial.s for y in vertices[:-1])
    net = initial.copy()
    u_departures = set()
    near_u = set()
    for y, o in zip(vertices, vertices[1:]):
        assert net.present(y, o), "Fixed-network presence failed to persist dynamically"
        if net.status[y] == "U":
            assert y not in u_departures
            u_departures.add(y)
            outgoing = sub(o, y)
            if closure:
                check_response_pairs(net, y, incoming)
                assert constructed_cover(net, y, incoming, outgoing)
            if defect is not None:
                assert dist(y, defect) > 0
                if dist(y, defect) > 2:
                    assert constructed_cover(net, y, incoming, outgoing)
                    counts["second_far_covered_u_departures"] += 1
                else:
                    near_u.add(y)
                    counts["second_near_u_departures"] += 1
        else:
            counts["d_departures"] += 1
        net.step(y, o)
        incoming = sub(o, y)
        counts["trace_steps"] += 1
    assert len(near_u) <= 12
    return net


def random_stopped_path(net, start, stop, rng):
    vertices, used = [start], set()
    while vertices[-1] not in stop:
        y = vertices[-1]
        options = [o for o in sorted(neighbours(y))
                   if net.present(y, o) and bond(y, o) not in used]
        if not options:
            return None
        o = rng.choice(options)
        used.add(bond(y, o))
        vertices.append(o)
    return vertices


def network_checks():
    rng = Random(20261116)
    square = set(product(range(-5, 6), repeat=2))
    c, u, v = (0, 0), (-1, 0), (1, 0)
    cases = [(Network(square, {c}), c, u, v),
             (Network(square, {c, (-1, 1), (-1, -1)}, {u: {c, (-2, 0)}}), c, u, v),
             (Network(square, {c, (1, 1), (1, -1)}, {v: {c, (2, 0)}}), c, u, v),
             (Network(square, {c, (-2, 0), (-2, -2)},
                      {(-2, -1): {(-3, -1), (-1, -1)}}), c, u, v)]
    diamond = {z for z in product(range(-6, 3), range(-4, 5)) if dist(z, (-2, 0)) <= 4}
    cases.append((Network(diamond, {(-1, 0)}), (-1, 0), (0, 0), (-2, 0)))
    # An explicit first trail revisits its start before the protected hit.
    first = [u, (-2, 0), (-2, -1), (-1, -1), u,
             (-1, 1), (-1, 2), (-1, 3), (-1, 4)]
    terminal = check_path(cases[0][0].normalize(u, c), first, sub(u, c), closure=True)
    second = [v, (1, 1), (1, 2), (1, 3), (0, 3), (-1, 3), (-2, 3), (-2, 4)]
    check_path(terminal.normalize(v, c), second, sub(v, c), defect=first[-1])
    counts["explicit_revisited_first_trails"] += 1
    for ordinary, c, u, v in cases:
        assert ordinary.consistent() and u not in ordinary.s and v not in ordinary.s
        assert ordinary.status[c] == "X" and dist(u, v) == 2
        assert all(ordinary.status[x] == "U" or ordinary.degree(x) <= 1 for x in (u, v))
        initial = ordinary.normalize(u, c)
        for _ in range(120):
            path = random_stopped_path(initial, u, initial.s | {v}, rng)
            if path is None:
                continue
            terminal = check_path(initial, path, sub(u, c), closure=True)
            counts["first_stopped_trails"] += 1
            if path[-1] not in initial.s:
                continue
            e = path[-1]
            assert all(terminal.status[x] == "U" for x in terminal.s)
            assert all(terminal.kept[x] == neighbours(x) & terminal.g for x in terminal.s - {e})
            second_initial = terminal.normalize(v, c)
            for _ in range(2):
                path2 = random_stopped_path(second_initial, v, second_initial.s, rng)
                if path2 is not None:
                    check_path(second_initial, path2, sub(v, c), defect=e)
                    counts["second_stopped_trails"] += 1


def raw_window_checks():
    # Exhaustive raw-successor closure at memories 1 through 7.
    def explore(vertices, edges, directions, target):
        if len(directions) == target:
            counts["raw_windows"] += 1
            y = vertices[-1]
            for d in STEPS:
                o = add(y, d)
                if d == (-directions[-1][0], -directions[-1][1]) or bond(y, o) in edges:
                    continue
                successor = directions[1:] + [d]
                sites = [(0, 0)]
                for step in successor:
                    sites.append(add(sites[-1], step))
                bonds = [bond(a, b) for a, b in zip(sites, sites[1:])]
                assert len(set(bonds)) == target
                counts["admissible_raw_successors"] += 1
            return
        y = vertices[-1]
        for d in STEPS:
            o = add(y, d)
            edge = bond(y, o)
            if edge not in edges:
                explore(vertices + [o], edges | {edge}, directions + [d], target)

    for m in range(1, 8):
        explore([(0, 0)], set(), [], m)


if __name__ == "__main__":
    network_checks()
    raw_window_checks()
    assert len(TEMPLATE - {(0, 0)}) == 12
    print(json.dumps({"status": "PASS", "seed": 20261116, **counts}, indent=2, sort_keys=True))
