"""Exact-rational sanity checks of the audited definitions; no Lean proofs."""

from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def compositions(total, size):
    if size == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, size - 1):
                yield (first,) + rest


def probabilities(size):
    return [tuple(F(v, 4) for v in values) for values in compositions(4, size)]


def tv(p, q):
    return sum(abs(a - b) for a, b in zip(p, q)) / 2


def maximal(p, q):
    common = [min(a, b) for a, b in zip(p, q)]
    overlap = sum(common)
    return [
        [
            (common[x] if x == y else F(0))
            + ((p[x] - common[x]) * (q[y] - common[y]) / (1 - overlap)
               if overlap < 1 else F(0))
            for y in range(len(q))
        ]
        for x in range(len(p))
    ]


def independent(p, q):
    return [[a * b for b in q] for a in p]


def verify_coupling(c, p, q):
    assert all(value >= 0 for row in c for value in row)
    assert [sum(row) for row in c] == list(p)
    assert [sum(row[y] for row in c) for y in range(len(q))] == list(q)


def marginal(p, r, target_size):
    return [sum(p[x] for x in range(len(p)) if r[x] == a)
            for a in range(target_size)]


counts = {
    "maximal_probability_pairs": 0,
    "arbitrary_coupling_matrices": 0,
    "marginal_map_cases": 0,
    "marginal_completions": 0,
    "minorization_premise_satisfying_cases": 0,
    "conditional_product_block_function_cases": 0,
    "hamming_pointwise_cases": 0,
    "hamming_integrated_cases": 0,
}

for size in range(1, 4):
    laws = probabilities(size)
    for p, q in product(laws, repeat=2):
        overlap = sum(min(a, b) for a, b in zip(p, q))
        assert tv(p, q) == 1 - overlap
        cmax = maximal(p, q)
        verify_coupling(cmax, p, q)
        assert sum(cmax[x][y] for x in range(size) for y in range(size)
                   if x != y) == tv(p, q)
        counts["maximal_probability_pairs"] += 1

        for target_size in range(1, 4):
            for r in product(range(target_size), repeat=size):
                P, Q = marginal(p, r, target_size), marginal(q, r, target_size)
                assert tv(P, Q) <= tv(p, q)
                counts["marginal_map_cases"] += 1
                c1, c2 = maximal(P, Q), independent(P, Q)
                c3 = [[(a + b) / 2 for a, b in zip(row1, row2)]
                      for row1, row2 in zip(c1, c2)]
                for c in (c1, c2, c3):
                    verify_coupling(c, P, Q)
                    d = [[c[r[x]][r[y]] * p[x] / P[r[x]] * q[y] / Q[r[y]]
                          if P[r[x]] > 0 and Q[r[y]] > 0 else F(0)
                          for y in range(size)] for x in range(size)]
                    verify_coupling(d, p, q)
                    for a, b in product(range(target_size), repeat=2):
                        assert sum(d[x][y] for x in range(size)
                                   for y in range(size)
                                   if r[x] == a and r[y] == b) == c[a][b]
                    counts["marginal_completions"] += 1

        for nu in laws:
            for t in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
                if all(t * n <= a and t * n <= b for a, b, n in zip(p, q, nu)):
                    assert tv(p, q) <= 1 - t
                    counts["minorization_premise_satisfying_cases"] += 1

    for entries in compositions(4, size * size):
        c = [[F(entries[size * x + y], 4) for y in range(size)]
             for x in range(size)]
        p = [sum(row) for row in c]
        q = [sum(row[y] for row in c) for y in range(size)]
        verify_coupling(c, p, q)
        assert tv(p, q) <= sum(c[x][y] for x in range(size)
                               for y in range(size) if x != y)
        counts["arbitrary_coupling_matrices"] += 1


# Complex rational values represented by pairs; every equality below is exact.
def zadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def zsub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def zscale(t, a):
    return (t * a[0], t * a[1])


def zmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def zconj(a):
    return (a[0], -a[1])


def zsum(values):
    result = (F(0), F(0))
    for value in values:
        result = zadd(result, value)
    return result


def norm_sq(a):
    return a[0] ** 2 + a[1] ** 2


def mean(p, f):
    return zsum(zscale(a, value) for a, value in zip(p, f))


def inner(p, f, h):
    return zsum(zscale(a, zmul(zconj(b), c)) for a, b, c in zip(p, f, h))


def variance(p, f):
    m = mean(p, f)
    return sum(a * norm_sq(zsub(b, m)) for a, b in zip(p, f))


shapes = [(), (1,), (2,), (2, 1), (2, 2), (2, 3), (1, 2, 1), (2, 2, 2)]
for shape in shapes:
    states = list(product(*(range(size) for size in shape)))
    n, sites = len(states), range(len(shape))
    blocks = [tuple(x for x in sites if mask & (1 << x))
              for mask in range(1 << len(shape))]
    patterns = [list(range(1, n + 1)), list(range(n, 0, -1)),
                [1 + (5 * x) % 7 for x in range(n)]]
    fs = [[(F(i * i - 2), F((3 * i + 1) % 5 - 2)) for i in range(n)],
          [(F((-1) ** i), F(i - 3)) for i in range(n)],
          [(F(1), F(2)) for _ in range(n)]]
    for weights in patterns:
        p = [F(value, sum(weights)) for value in weights]
        for U in blocks:
            outside = [x for x in sites if x not in U]
            fibres = [[j for j, tau in enumerate(states)
                       if all(sigma[x] == tau[x] for x in outside)]
                      for sigma in states]
            D = [sum(p[j] for j in indices) for indices in fibres]
            assert all(value > 0 for value in D)
            kernel = [[p[j] / D[i] if j in fibres[i] else F(0)
                       for j in range(n)] for i in range(n)]
            for i, row in enumerate(kernel):
                assert all(value >= 0 for value in row) and sum(row) == 1
                for assignment in product(*(range(shape[x]) for x in U)):
                    mass = sum(row[j] for j, tau in enumerate(states)
                               if tuple(tau[x] for x in U) == assignment)
                    assert mass > 0

            def expectation_on_block(f):
                return [mean(row, f) for row in kernel]

            assert expectation_on_block([(F(1), F(0))] * n) == [(F(1), F(0))] * n
            for f in fs:
                Ef = expectation_on_block(f)
                assert expectation_on_block(Ef) == Ef
                assert mean(p, Ef) == mean(p, f)
                h = fs[1]
                assert inner(p, f, expectation_on_block(h)) == inner(p, Ef, h)
                residual = [zsub(a, b) for a, b in zip(f, Ef)]
                block_form = sum(a * norm_sq(b) for a, b in zip(p, residual))
                cv = [sum(p[j] * norm_sq(residual[j]) for j in indices) / D[i]
                      for i, indices in enumerate(fibres)]
                assert inner(p, f, residual)[0] == block_form
                assert sum(a * b for a, b in zip(p, cv)) == block_form
                assert variance(p, f) == block_form + variance(p, Ef)
                counts["conditional_product_block_function_cases"] += 1

    for U in blocks:
        complement_size = len(shape) - len(U)
        for sigma, tau in product(states, repeat=2):
            distance = sum(a != b for a, b in zip(sigma, tau))
            disagree = not all(sigma[x] == tau[x] for x in U)
            assert distance <= complement_size + len(shape) * int(disagree)
            counts["hamming_pointwise_cases"] += 1
        laws = [tuple(F(1, n) for _ in range(n)),
                tuple(F(i == 0) for i in range(n)),
                tuple(F(i == n - 1) for i in range(n))]
        for p, q in product(laws, repeat=2):
            for c in (maximal(p, q), independent(p, q)):
                cost = sum(c[i][j] * sum(a != b for a, b in zip(sigma, tau))
                           for i, sigma in enumerate(states)
                           for j, tau in enumerate(states))
                disagree_mass = sum(c[i][j] for i, sigma in enumerate(states)
                                    for j, tau in enumerate(states)
                                    if not all(sigma[x] == tau[x] for x in U))
                assert cost <= complement_size + len(shape) * disagree_mass
                counts["hamming_integrated_cases"] += 1

assert sum([]) != 1  # An empty state type admits no Probability hypothesis.
assert list(product()) == [()]  # Zero sites give one configuration.
result = {"status": "PASS", "arithmetic": "exact rational", "counts": counts}
Path(__file__).with_name("check_cases.out.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
