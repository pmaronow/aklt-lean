"""Exact finite sanity checks of the read-only Lean definitions; no Lean proofs."""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
import json
import random

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))  # E, N, W, S
REFLECT = (0, 3, 2, 1)
START, CENTRE = (-1, 0), (0, 0)
TARGETS = ((1, 0), (0, 1))  # B, C
H = (Q(1), Q(5404319552844595, 4503599627370496))
X = (Q(200, 187), Q(1000, 961))  # turn, straight
ALPHA = (Q(150000, 10**6), Q(145217, 10**6))
BETA = (Q(357549, 10**6), Q(352782, 10**6))
BETA_PRIME = (Q(344661, 10**6), Q(340008, 10**6))


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def reflect(z):
    return z[0], -z[1]


def dist(a, b):
    return abs(a[0] - b[0]) + abs(a[1] - b[1])


def pair_type(p):
    return 0 if all(a[0] == b[0] or a[1] == b[1] for a in p for b in p) else 1


def pair_shift(t, p):
    return max((min(dist(z, START), dist(z, TARGETS[t])) for z in p), default=0)


def data(word):
    vertices = [START]
    for d in word:
        vertices.append(add(vertices[-1], STEPS[d]))
    counts = Counter()
    straight, revisit, lives, labels = [], [], [], []
    for i, d in enumerate(word):
        x, o = vertices[i:i+2]
        incoming = 2 if i == 0 else word[i-1]
        arrival = add(x, tuple(-c for c in STEPS[incoming]))
        live = {add(x, step) for step in STEPS} - {arrival, o}
        live = {z for z in live if z != CENTRE and counts[z] < 2}
        pairs = [frozenset(p) for p in combinations(sorted(live | {o}), 2)]
        st = d == incoming
        labs = {p: ((BETA_PRIME if len(live) == 1 else BETA)[st]
                    if o in p else ALPHA[st]) for p in pairs}
        straight.append(st)
        revisit.append(counts[x] > 0)
        lives.append(live)
        labels.append(labs)
        counts[x] += 1
    rewards = [sum((c * H[pair_type(p)] for p, c in labs.items()), Q(0))
               for labs in labels]
    first = [i for i in range(len(word)) if not revisit[i]]
    if len(word) <= 12:
        order = sorted(first, key=lambda i: (rewards[i] == 0,
                       (X[straight[i]] - 1) / (X[straight[i]] * rewards[i])
                       if rewards[i] else Q(0), i))
    else:
        order = [i for i in first if straight[i]] + [i for i in first if not straight[i]]
    base = Q(1)
    for r in revisit:
        base *= Q(1, 5) if r else Q(1, 3)
    return dict(vertices=vertices, straight=straight, revisit=revisit,
                lives=lives, labels=labels, rewards=rewards, order=order, base=base)


def exposure(d, rewards):
    result = Q(0)
    for i in reversed(d['order']):
        result = X[d['straight'][i]] * (rewards[i] + result)
    return result


def closed(t, word, d):
    v = d['vertices']
    bonds = [frozenset(v[i:i+2]) for i in range(len(word))]
    return (len(set(bonds)) == len(bonds) and (not word or word[0] != 0)
            and v[-1] == TARGETS[t] and CENTRE not in v
            and TARGETS[t] not in v[:-1])


def check_word(word):
    d = data(word)
    rd = data(tuple(REFLECT[a] for a in word))
    assert rd['vertices'] == list(map(reflect, d['vertices']))
    assert d['straight'] == rd['straight'] and d['revisit'] == rd['revisit']
    assert d['order'] == rd['order'] and d['rewards'] == rd['rewards']
    assert d['base'] == rd['base']
    for i, labs in enumerate(d['labels']):
        assert {reflect(z) for z in d['lives'][i]} == rd['lives'][i]
        assert {frozenset(map(reflect, p)): c for p, c in labs.items()} == rd['labels'][i]
        for p in labs:
            rp = frozenset(map(reflect, p))
            assert pair_type(p) == pair_type(rp)
            assert pair_shift(0, p) == pair_shift(0, rp)
    value = d['base'] * exposure(d, d['rewards'])
    coeffs = []
    for t in range(2):
        ks = [defaultdict(Q) for _ in word]
        keys = set()
        for i, labs in enumerate(d['labels']):
            for p, c in labs.items():
                key = pair_type(p), pair_shift(t, p)
                ks[i][key] += c
                keys.add(key)
        coeff = {key: d['base'] * exposure(d, [k[key] for k in ks]) for key in keys}
        assert sum((c * H[key[0]] for key, c in coeff.items()), Q(0)) == value
        coeffs.append(coeff)
    return d, value, coeffs


def main():
    checked, departures, pair_instances = 0, 0, 0
    summaries = []
    for n in range(7):
        support = [set(), set()]
        rows = [Q(0), Q(0)]
        coefficients = [defaultdict(Q), defaultdict(Q)]
        directional = [defaultdict(Q), defaultdict(Q)]
        counts = [0, 0]
        for word in product(range(4), repeat=n):
            d, value, coeffs = check_word(word)
            checked += 1
            departures += n
            pair_instances += sum(map(len, d['labels']))
            for t in range(2):
                support[t].update(s for _, s in coeffs[t])
                if closed(t, word, d):
                    assert n > 0 and word[0] in (1, 2, 3)
                    rows[t] += value
                    directional[t][word[0]] += value
                    counts[t] += 1
                    for key, c in coeffs[t].items():
                        coefficients[t][key] += c
        for t in range(2):
            assert rows[t] == sum(directional[t].values(), Q(0))
            assert rows[t] == sum((c * H[y] for (y, s), c in coefficients[t].items()), Q(0))
            assert all(s in support[t] for y, s in coefficients[t])
            assert all(c >= 0 for c in coefficients[t].values())
        summaries.append(dict(length=n, closed_word_counts=counts,
                              rows=list(map(str, rows)), supports=list(map(sorted, support))))
    rng = random.Random(20261116)
    for n in (13, 14, 16):
        for _ in range(50):
            check_word(tuple(rng.randrange(4) for _ in range(n)))
    # Non-vacuity witnesses: a B trail and a C trail, with nonzero rewards.
    for t, word in ((0, (1, 0, 0, 3)), (1, (1, 0))):
        d, value, _ = check_word(word)
        assert closed(t, word, d) and value > 0
    print(json.dumps(dict(exhaustive_words=checked, departure_indices=departures,
                          response_pair_instances=pair_instances,
                          sampled_long_words=150, lengths=summaries), indent=2))


if __name__ == '__main__':
    main()
