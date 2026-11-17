"""Finite sanity checks of the stopped quotient statement; not a Lean proof.

Use actual raw words for memories 1..4, their identity quotients, two phases,
signed rational weights, displayed-state stopping, and deliberately different
quotient arrivals at windows whose admitted departures are all revisits.
"""

from fractions import Fraction
from functools import cache
from itertools import product


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


@cache
def vertices(word):
    result = [(0, 0)]
    for d in word:
        result.append(add(result[-1], STEPS[d]))
    return tuple(result)


@cache
def bonds(word):
    v = vertices(word)
    return tuple(frozenset((x, y)) for x, y in zip(v, v[1:]))


def raw(word):
    return len(set(bonds(word))) == len(word)


@cache
def admitted(word, d):
    x = vertices(word)[-1]
    return d != (word[-1] + 2) % 4 and frozenset((x, add(x, STEPS[d]))) not in bonds(word)


@cache
def kind(word, d):
    if vertices(word)[-1] in vertices(word)[:-1]:
        return 2  # revisit takes precedence over straight/turn
    return 0 if d == word[-1] else 1


def weight(phi, psi, k, d, incoming, x):
    # Arrival dependence is present precisely where Correct guarantees it.
    arrival_term = incoming if k != 2 else 0
    numerator = (11 * phi + 7 * psi + 5 * k + 3 * d + 2 * x[0] - x[1] + arrival_term) % 13 - 6
    return Fraction(numerator, 2 + d + psi)


def check_memory(m):
    words = tuple(w for w in product(range(4), repeat=m) if raw(w))
    index = {w: a for a, w in enumerate(words)}
    arrival = []
    allowed = {}
    edge_kind = {}
    successor = {}
    edges = 0
    changed_arrivals = 0
    for a, word in enumerate(words):
        nonrevisit = any(admitted(word, d) and kind(word, d) != 2 for d in range(4))
        arrival.append(word[-1] if nonrevisit else (word[-1] + 1) % 4)
        changed_arrivals += arrival[-1] != word[-1]
        for d in range(4):
            allowed[a, d] = admitted(word, d)
            edge_kind[a, d] = kind(word, d)
            successor[a, d] = 0
            if admitted(word, d):
                next_word = word[1:] + (d,)
                assert raw(next_word), (m, word, d, 'successor closure')
                successor[a, d] = index[next_word]
                assert edge_kind[a, d] == kind(word, d)
                if kind(word, d) != 2:
                    assert arrival[a] == word[-1]
                edges += 1

    def terminal_quotient(phi, a, x):
        return (x[0] - x[1] + a + 2 * phi) % 7 == 0

    def reward_quotient(phi, a, x):
        return Fraction((phi + 1) * (a % 3 + 1), 2 + a % 2) if terminal_quotient(phi, a, x) else Fraction(0)

    @cache
    def raw_iterate(j, phi, word, x):
        assert word in index
        a = index[word]
        if j == 0:
            return reward_quotient(phi, a, x)
        if terminal_quotient(phi, a, x):
            return Fraction(0)
        return sum((
            weight(phi, psi, kind(word, d), d, word[-1], x)
            * raw_iterate(j - 1, psi, word[1:] + (d,), add(x, STEPS[d]))
            for d in range(4) if admitted(word, d) for psi in range(2)
        ), Fraction(0))

    @cache
    def quotient_iterate(j, phi, a, x):
        if j == 0:
            return reward_quotient(phi, a, x)
        if terminal_quotient(phi, a, x):
            return Fraction(0)
        return sum((
            weight(phi, psi, edge_kind[a, d], d, arrival[a], x)
            * quotient_iterate(j - 1, psi, successor[a, d], add(x, STEPS[d]))
            for d in range(4) if allowed[a, d] for psi in range(2)
        ), Fraction(0))

    comparisons = 0
    for word in words:
        for phi in range(2):
            for x in ((0, 0), (1, 0), (-1, 1)):
                raw_sum = Fraction(0)
                quotient_sum = Fraction(0)
                for horizon in range(4):
                    r = raw_iterate(horizon, phi, word, x)
                    q = quotient_iterate(horizon, phi, index[word], x)
                    assert r == q, (m, word, phi, x, horizon, r, q)
                    raw_sum += r
                    quotient_sum += q
                    assert raw_sum == quotient_sum
                    comparisons += 1
    return {
        'memory': m,
        'raw_windows': len(words),
        'admitted_edges_checked_for_closure': edges,
        'deliberately_changed_revisit_only_arrivals': changed_arrivals,
        'iterate_and_horizon_comparisons': comparisons,
    }


if __name__ == '__main__':
    import json

    for memory in range(1, 5):
        print(json.dumps(check_memory(memory)), flush=True)
    print('All exact rational finite checks passed.', flush=True)
