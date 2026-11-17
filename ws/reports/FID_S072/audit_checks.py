"""Independent finite checks of definitions; reads no external data."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import json

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
START, CENTRE, INCOMING = (-1, 0), (0, 0), 2
XS, XT = F(1000, 961), F(200, 187)
H = F(5404319552844595, 4503599627370496)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def bond(x, y):
    return tuple(sorted((x, y)))


def raw_windows(m):
    counts = Counter()
    words = []
    rows = []

    def visit(w, x, vertices, used):
        counts[len(w)] += 1
        if len(w) == m:
            row = []
            for d, step in enumerate(STEPS):
                y = add(x, step)
                allowed = d != (w[-1] + 2) % 4 and bond(x, y) not in used
                kind = 2 if x in vertices[:-1] else (0 if d == w[-1] else 1)
                row.append((allowed, kind))
            words.append(w)
            rows.append(tuple(row))
            return
        for d, step in enumerate(STEPS):
            y = add(x, step)
            e = bond(x, y)
            if e not in used:
                visit(w + (d,), y, vertices + (y,), used | {e})

    visit((), (0, 0), ((0, 0),), set())
    index = {w: i for i, w in enumerate(words)}
    successors = [tuple(index[w[1:] + (d,)] if allowed else -1
                        for d, (allowed, _) in enumerate(row))
                  for w, row in zip(words, rows)]
    initial = [tuple(k if allowed else -1 for allowed, k in row) +
               ((w[-1] if any(a and k != 2 for a, k in row) else -1),)
               for w, row in zip(words, rows)]

    def classify(signatures):
        classes = {}
        return [classes.setdefault(s, len(classes)) for s in signatures]

    classes = classify(initial)
    refinement_counts = [len(set(classes))]
    while True:
        new_classes = classify((initial[i], tuple(classes[j] if j >= 0 else -1 for j in succ))
                               for i, succ in enumerate(successors))
        refinement_counts.append(len(set(new_classes)))
        if new_classes == classes:
            break
        classes = new_classes
    representatives = {}
    for i, a in enumerate(classes):
        representatives.setdefault(a, i)
    edge_counts = Counter()
    for i in representatives.values():
        for allowed, k in rows[i]:
            if allowed:
                edge_counts[k] += 1
    # Check the conditions of Correct on every raw word and direction.
    for i, (w, row, succ) in enumerate(zip(words, rows, successors)):
        rep = representatives[classes[i]]
        for d, (allowed, kind) in enumerate(row):
            assert allowed == rows[rep][d][0]
            if allowed:
                assert kind == rows[rep][d][1]
                assert classes[succ[d]] == classes[successors[rep][d]]
                if kind != 2:
                    assert w[-1] == words[rep][-1]
    return words, rows, classes, representatives, {
        "raw_counts": dict(sorted(counts.items())),
        "partition_refinement_counts": refinement_counts,
        "quotient_edges_straight_turn_revisit": [edge_counts[i] for i in range(3)],
    }


def true_departures(w):
    x = START
    count = Counter()
    result = []
    for i, d in enumerate(w):
        incoming = INCOMING if i == 0 else w[i - 1]
        outgoing = add(x, STEPS[d])
        arrival = (x[0] - STEPS[incoming][0], x[1] - STEPS[incoming][1])
        live = {add(x, s) for s in STEPS} - {arrival, outgoing}
        live = {y for y in live if y != CENTRE and count[y] < 2}
        straight = d == incoming
        reward = F(0)
        for p in combinations(sorted(live | {outgoing}), 2):
            if outgoing in p:
                numerator = (340008 if straight else 344661) if len(live) == 1 else (
                    352782 if straight else 357549)
            else:
                numerator = 145217 if straight else 150000
            ptype_h = 1 if p[0][0] == p[1][0] or p[0][1] == p[1][1] else H
            reward += F(numerator, 10**6) * ptype_h
        result.append((2 if count[x] else (0 if straight else 1), reward))
        count[x] += 1
        x = outgoing
    return result


def phase_update(p, k, reward):
    if k == 2:
        return tuple(v / 5 for v in p)
    a, b, c, d = p
    if k == 0:
        return XS*a/3, XS*b/3, XS*c/3, (d+XS*reward*b)/3
    return XT*a/3, b/3, (c+XT*reward*a)/3, d/3


def fold(p, departures):
    for k, reward in departures:
        p = phase_update(p, k, reward)
    return p


def check_phase(w):
    departures = true_departures(w)
    p = fold((F(1), F(1), F(0), F(0)), departures)
    order = [i for k in (0, 1) for i, (kind, _) in enumerate(departures) if kind == k]
    exposure = F(0)
    for i in reversed(order):
        k, reward = departures[i]
        exposure = (XS if k == 0 else XT) * (reward + exposure)
    base = F(1)
    for k, _ in departures:
        base *= F(1, 5) if k == 2 else F(1, 3)
    assert p[2] + p[3] == base * exposure
    for split in range(len(w) + 1):
        prefix_departures = true_departures(w[:split])
        assert prefix_departures == departures[:split]
        prefix = fold((F(1), F(1), F(0), F(0)), prefix_departures)
        split_total = F(0)
        for phi in range(4):
            suffix = fold(tuple(F(int(psi == phi)) for psi in range(4)), departures[split:])
            split_total += prefix[phi] * (suffix[2] + suffix[3])
        assert split_total == p[2] + p[3]


if __name__ == "__main__":
    words, rows, classes, representatives, result = raw_windows(10)
    # Exhaust all true words through length five, plus diverse length-ten samples.
    samples = {()}
    for w in words:
        if w[0] != 0:
            samples.update(w[:n] for n in range(1, 6))
    for i in range(0, len(words), 1000):
        w = words[i]
        if w[0] != 0:
            samples.add(w)
    for w in samples:
        check_phase(w)
    result["phase_identity_and_all_prefix_splits_checked"] = len(samples)
    scale = 2**48
    result["diagonal_ceiling_numerators"] = [
        -(-(scale*t.numerator) // t.denominator)
        for t in (XS/3, XT/3, F(1, 3), F(1, 5))]
    print(json.dumps(result, indent=2))
