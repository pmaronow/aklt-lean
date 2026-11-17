"""Finite sanity checks for the truth sweep; these are not Lean proofs."""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json
import random

DIRS = ((1, 0), (0, 1), (-1, 0), (0, -1))
U, C = (-1, 0), (0, 0)
TARGET = {"B": (1, 0), "C": (0, 1)}
INCOMING = (-1, 0)
ALPHA = {True: Q(145217, 10**6), False: Q(150000, 10**6)}
BETA = {True: Q(352782, 10**6), False: Q(357549, 10**6)}
BETA_PRIME = {True: Q(340008, 10**6), False: Q(344661, 10**6)}
PASSAGE = {True: Q(1000, 961), False: Q(200, 187)}
H = {"B": Q(1), "C": Q(5404319552844595, 4503599627370496)}
rng = random.Random(20261116)
stats = Counter()


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def dist(x, y):
    return abs(x[0] - y[0]) + abs(x[1] - y[1])


def neighbours(x):
    return {add(x, d) for d in DIRS}


def pair_type(p):
    return "B" if all(x[0] == y[0] or x[1] == y[1] for x in p for y in p) else "C"


def word_data(word):
    vertices = [U]
    for d in word:
        vertices.append(add(vertices[-1], d))
    count = Counter()
    records = []
    for i, outgoing in enumerate(word):
        y, o = vertices[i : i + 2]
        incoming = INCOMING if i == 0 else word[i - 1]
        other = neighbours(y) - {sub(y, incoming), o}
        other = {z for z in other if z != C and count[z] < 2}
        pairs = [frozenset(p) for p in combinations(sorted(other | {o}), 2)]
        straight = outgoing == incoming
        coefficients = {
            p: (BETA_PRIME[straight] if len(other) == 1 else BETA[straight])
            if o in p else ALPHA[straight]
            for p in pairs
        }
        records.append((count[y] > 0, straight, coefficients))
        count[y] += 1
    first = [i for i, (revisit, _, _) in enumerate(records) if not revisit]

    def short_key(i):
        _, straight, coefficients = records[i]
        kappa = sum((a * H[pair_type(p)] for p, a in coefficients.items()), Q(0))
        x = PASSAGE[straight]
        return (kappa == 0, (x - 1) / (x * kappa) if kappa else Q(0), i)

    order = sorted(first, key=short_key) if len(word) <= 12 else (
        [i for i in first if records[i][1]] + [i for i in first if not records[i][1]]
    )
    return vertices, records, first, order


def check_arbitrary_word(word):
    vertices, records, first, order = word_data(word)
    assert sorted(first) == sorted(order) and len(order) == len(set(order))
    for _, _, coefficients in records:
        for p, coefficient in coefficients.items():
            assert len(p) == 2 and coefficient > 0
            stats["arbitrary_word_response_pairs"] += 1
    stats["arbitrary_words"] += 1
    stats["short_order_words" if len(word) <= 12 else "long_order_words"] += 1


for n in range(6):
    for word in product(DIRS, repeat=n):
        check_arbitrary_word(word)
for n in (12, 13, 14):
    for _ in range(100):
        check_arbitrary_word(tuple(rng.choice(DIRS) for _ in range(n)))

# Enumerate every bond-distinct, centre-avoiding first-hit trail up to length 8.
length_coefficients = defaultdict(Q)
closed_by_type_length = Counter()


def closed_dfs(x_type, vertices, word, used):
    y, n = vertices[-1], len(word)
    if y == TARGET[x_type]:
        _, records, first, order = word_data(word)
        assert all(vertices[j] != C for j in range(n + 1))
        for i, (_, _, coefficients) in enumerate(records):
            for p, a in coefficients.items():
                shift = max(min(dist(z, U), dist(z, TARGET[x_type])) for z in p)
                assert 2 * shift <= n + 2
                assert shift <= n + 1
                stats["closed_trail_response_pairs"] += 1
        base = Q(1)
        for revisit, _, _ in records:
            base *= Q(1, 5) if revisit else Q(1, 3)
        exposure = Q(1)
        for i in order:
            _, straight, coefficients = records[i]
            exposure *= PASSAGE[straight]
            for p, a in coefficients.items():
                shift = max(min(dist(z, U), dist(z, TARGET[x_type])) for z in p)
                length_coefficients[x_type, pair_type(p), shift, n] += base * exposure * a
        closed_by_type_length[x_type, n] += 1
        stats["closed_trails"] += 1
        return
    if n == 8:
        return
    for d in DIRS:
        z = add(y, d)
        bond = frozenset((y, z))
        if z != C and bond not in used:
            closed_dfs(x_type, vertices + [z], word + (d,), used | {bond})


for x_type in TARGET:
    closed_dfs(x_type, [U], (), set())
assert closed_by_type_length["C", 2] > 0
assert closed_by_type_length["B", 4] > 0
assert all(a >= 0 for a in length_coefficients.values())
for x_type in TARGET:
    for y_type in TARGET:
        for theta in (Q(1, 2), Q(3, 4), Q(1), Q(2)):
            by_length = sum((
                sum((length_coefficients[x_type, y_type, s, n] * theta ** (-s)
                     for s in range(n + 2)), Q(0)) for n in range(9)
            ), Q(0))
            by_shift = sum((
                sum((length_coefficients[x_type, y_type, s, n] for n in range(9)), Q(0))
                * theta ** (-s) for s in range(10)
            ), Q(0))
            assert by_length == by_shift
            stats["finite_regroup_checks"] += 1

# Network checks use square volumes, for which S = {max(|x|, |y|) >= r-1}.
class Network:
    def __init__(self, g, status, kept):
        self.g, self.status, self.kept = g, status, kept

    def present(self, y, z):
        return (self.status.get(y, "X") != "X" and self.status.get(z, "X") != "X"
                and z in self.kept[y] and y in self.kept[z] and dist(y, z) == 1)

    def degree(self, y):
        return sum(self.present(y, z) for z in neighbours(y))

    def normalize(self, y, c):
        kept = self.kept.copy()
        if self.status[y] == "U":
            kept[y] = kept[y] - {c}
        return Network(self.g, self.status.copy(), kept)

    def step(self, y, z):
        assert self.present(y, z)
        status, kept = self.status.copy(), self.kept.copy()
        status[y] = "D" if status[y] == "U" else "X"
        kept[y], kept[z] = kept[y] - {z}, kept[z] - {y}
        return Network(self.g, status, kept)

    def consistent(self, protected):
        for x in self.g:
            s, k = self.status[x], self.kept[x]
            if not k <= neighbours(x) & self.g:
                return False
            if x in protected and (s != "U" or k != neighbours(x) & self.g):
                return False
            if s == "U" and k != neighbours(x) & self.g:
                return False
            if s == "D" and (len(k) != 2 or self.degree(x) > 2):
                return False
            if s != "X":
                for z in neighbours(x) & self.g:
                    if self.status[z] != "X" and ((z in k) != (x in self.kept[z])):
                        return False
        return True


def covered_v2(d, y, incoming, outgoing):
    # Rotation invariant form of PatternData.Covered and its V2 non-tip match.
    arrival = sub(y, incoming)
    if outgoing == (-incoming[0], -incoming[1]):
        return False
    if d.status[y] != "U" or d.kept[y] != neighbours(y) - {arrival}:
        return False
    if not (d.status[arrival] == "X" or (
            d.status[arrival] == "D" and len(d.kept[arrival]) == 2
            and y not in d.kept[arrival])):
        return False
    non_tips = {y} | neighbours(y) | {add(y, (a, b)) for a in (-1, 1) for b in (-1, 1)}
    for z in non_tips - {y}:
        s, k = d.status[z], d.kept[z]
        if s == "U" and k != neighbours(z) & d.g:
            return False
        if s == "D" and len(k) != 2:
            return False
        if z in neighbours(y) - {arrival} and s == "D" and y not in k:
            return False
    if d.status[add(y, outgoing)] == "X":
        return False
    for a in non_tips:
        for b in non_tips & neighbours(a):
            if d.status[a] != "X" and d.status[b] != "X":
                if (b in d.kept[a]) != (a in d.kept[b]):
                    return False
    return True


def random_stopped(d, start, target, protected):
    vertices, used, current = [start], set(), d
    for _ in range(180):
        y = vertices[-1]
        if y in target:
            return vertices, current
        assert y not in protected
        options = [z for z in neighbours(y) if current.present(y, z)
                   and frozenset((y, z)) not in used]
        if not options:
            return None
        z = rng.choice(sorted(options))
        assert d.present(y, z)
        used.add(frozenset((y, z)))
        current = current.step(y, z)
        vertices.append(z)
    return None


for trial in range(900):
    r = rng.choice((4, 5, 6, 8))
    g = set(product(range(-r, r + 1), repeat=2))
    protected = {x for x in g if max(abs(x[0]), abs(x[1])) >= r - 1}
    v = TARGET[rng.choice(("B", "C"))]
    interior = g - protected - {U, v, C}
    removed = {C} | {z for z in interior if rng.random() < 0.06}
    d = Network(g, {z: "X" if z in removed else "U" for z in g},
                {z: neighbours(z) & g for z in g})
    assert d.consistent(protected)
    # Some original pair domains also contain D sites from an earlier trace.
    if trial % 2 == 0:
        prep = random_stopped(d.normalize(U, C), U, protected | {v}, protected)
        if prep:
            prep_vertices, prep_d = prep
            for stop in range(1, len(prep_vertices) - 1):
                if rng.random() > 0.12:
                    continue
                scratch_d = d.normalize(U, C)
                for a, b in zip(prep_vertices[:stop], prep_vertices[1:stop + 1]):
                    scratch_d = scratch_d.step(a, b)
                status = scratch_d.status.copy()
                status[prep_vertices[stop]] = "X"
                candidate = Network(g, status, scratch_d.kept)
                if candidate.consistent(protected) and all(
                    candidate.status[z] == "U" or (
                        candidate.status[z] == "D" and candidate.degree(z) <= 1)
                    for z in (U, v)
                ):
                    d = candidate
                    stats["prepared_consistent_domains"] += 1
                    break
    assert d.consistent(protected)
    first = random_stopped(d.normalize(U, C), U, protected | {v}, protected)
    if first is None or first[0][-1] == v:
        continue
    first_vertices, after_first = first
    e = first_vertices[-1]
    assert e in protected and v not in first_vertices
    incoming = sub(v, C)
    second_start = after_first.normalize(v, C)
    second = random_stopped(second_start, v, protected, protected)
    if second is None:
        continue
    second_vertices, _ = second
    current, seen_u, uncovered = second_start, set(), 0
    for i, (y, z) in enumerate(zip(second_vertices, second_vertices[1:])):
        if current.status[y] == "U":
            assert y not in seen_u
            seen_u.add(y)
            outgoing = sub(z, y)
            inc = incoming if i == 0 else sub(y, second_vertices[i - 1])
            if not covered_v2(current, y, inc, outgoing):
                assert 0 < dist(y, e) <= 2
                uncovered += 1
                stats["exceptional_u_departures"] += 1
            stats["second_trail_u_departures"] += 1
        else:
            stats["second_trail_d_departures"] += 1
        current = current.step(y, z)
    assert uncovered <= 12
    stats["max_observed_exceptions"] = max(stats["max_observed_exceptions"], uncovered)
    stats["two_trail_instances"] += 1

for e in ((0, 0), (-11, 7), (100, -100)):
    diamond = {add(e, z) for z in product(range(-2, 3), repeat=2) if 0 < dist(z, (0, 0)) <= 2}
    assert len(diamond) == 12
    stats["diamond_centres"] += 1

result = {"status": "all finite checks passed", "seed": 20261116,
          "stats": dict(sorted(stats.items())),
          "closed_trails_by_type_length": {f"{x}:{n}": a for (x, n), a in sorted(closed_by_type_length.items())},
          "scope": "Finite sanity checks, not universal proofs; network checks use square volumes."}
out = Path(__file__).with_name("checks.json")
out.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
