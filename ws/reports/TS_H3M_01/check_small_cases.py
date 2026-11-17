"""Bounded exact-rational sanity checks; no Lean proofs or repository writes."""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import prod
import json
from pathlib import Path

STEP = ((1, 0), (0, 1), (-1, 0), (0, -1))
XS, XT = F(1000, 961), F(200, 187)
H = F(5404319552844595, 4503599627370496)
INITIAL = (F(1), F(1), F(0), F(0))
TERMINAL = (F(0), F(0), F(1), F(1))
COUNTS = Counter()


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def vertices(w, start=(0, 0)):
    vs = [start]
    for d in w:
        vs.append(add(vs[-1], STEP[d]))
    return vs


def bonds(vs):
    return [frozenset((x, y)) for x, y in zip(vs, vs[1:])]


def diagonal(phase, kind):
    if kind == 2:
        return F(1, 5)
    if phase in (0, 1, 2) and kind == 0:
        return XS / 3
    if phase == 0 and kind == 1:
        return XT / 3
    return F(1, 3)


def transition(kind, reward, phase, target):
    if phase == target:
        return diagonal(phase, kind)
    if (phase, target, kind) == (0, 2, 1):
        return XT * reward / 3
    if (phase, target, kind) == (1, 3, 0):
        return XS * reward / 3
    return F(0)


def matrices(kinds, rewards):
    return [tuple(tuple(transition(k, r, a, b) for b in range(4))
                  for a in range(4)) for k, r in zip(kinds, rewards)]


def run(ms, initial=INITIAL):
    p = initial
    for m in ms:
        p = tuple(sum(p[a] * m[a][b] for a in range(4)) for b in range(4))
    return p


def terminal_value(p):
    return sum(x * y for x, y in zip(p, TERMINAL))


def single_change(kinds, rewards, j, before, after):
    return prod(diagonal(before, k) if i < j else
                transition(k, rewards[i], before, after) if i == j else
                diagonal(after, k) for i, k in enumerate(kinds))


def long_multiplier(straight, revisit, j):
    return prod((XS if s else XT) if not v and
                ((s and i <= j) if straight[j] else (s or i <= j)) else F(1)
                for i, (s, v) in enumerate(zip(straight, revisit)))


def exposure(straight, rewards, order):
    value = F(0)
    for i in reversed(order):
        value = (XS if straight[i] else XT) * (rewards[i] + value)
    return value


def ordered_multiplier(straight, order, j):
    return prod(XS if straight[i] else XT for i in order[:order.index(j) + 1])


def word_data(w):
    vs = vertices(w, (-1, 0))
    kinds, rewards = [], []
    for i, d in enumerate(w):
        incoming = 2 if i == 0 else w[i - 1]
        straight = d == incoming
        counts = Counter(vs[:i])
        kinds.append(2 if counts[vs[i]] > 0 else 0 if straight else 1)
        arrival = add(vs[i], STEP[(incoming + 2) % 4])
        outgoing = vs[i + 1]
        live = {add(vs[i], s) for s in STEP} - {arrival, outgoing}
        live = {z for z in live if z != (0, 0) and counts[z] < 2}
        reward = F(0)
        for pair in combinations(live | {outgoing}, 2):
            if outgoing in pair:
                coeff = F(340008 if straight else 344661, 10**6) if len(live) == 1 else F(352782 if straight else 357549, 10**6)
            else:
                coeff = F(145217 if straight else 150000, 10**6)
            x, y = pair
            reward += coeff * (1 if x[0] == y[0] or x[1] == y[1] else H)
        rewards.append(reward)
    return kinds, rewards


def check_raw_successors():
    for n in range(1, 8):
        for w in product(range(4), repeat=n):
            vs = vertices(w)
            used = bonds(vs)
            if len(set(used)) != n:
                continue
            COUNTS['raw_windows_positive_memory'] += 1
            for d in range(4):
                new_bond = frozenset((vs[-1], add(vs[-1], STEP[d])))
                if d == (w[-1] + 2) % 4 or new_bond in used:
                    continue
                shifted = w[1:] + (d,)
                assert len(set(bonds(vertices(shifted)))) == n, (w, d)
                COUNTS['admissible_raw_successors'] += 1


def check_phase_and_order_algebra():
    for n in range(7):
        for kinds in product(range(3), repeat=n):
            for rewards in (tuple(F(0) for _ in kinds),
                            tuple(F((-1)**i * (i + 1), 7) for i in range(n)),
                            tuple(F(-2) if i % 2 == 0 else F(3, 5) for i in range(n))):
                ms = matrices(kinds, rewards)
                expected = sum(single_change(kinds, rewards, j, 0, 2) +
                               single_change(kinds, rewards, j, 1, 3) for j in range(n))
                assert terminal_value(run(ms)) == expected, (kinds, rewards)
                COUNTS['phase_fold_cases'] += 1
                straight = [k == 0 for k in kinds]
                revisit = [k == 2 for k in kinds]
                base = prod(F(1, 5) if k == 2 else F(1, 3) for k in kinds)
                order = [i for i in range(n) if not revisit[i] and straight[i]]
                order += [i for i in range(n) if not revisit[i] and not straight[i]]
                assert len(order) == len(set(order))
                assert set(order) == {i for i in range(n) if not revisit[i]}
                for j in order:
                    assert ordered_multiplier(straight, order, j) == long_multiplier(straight, revisit, j)
                    COUNTS['long_order_member_cases'] += 1
                for j in range(n):
                    rhs = F(0) if revisit[j] else base * rewards[j] * long_multiplier(straight, revisit, j)
                    assert single_change(kinds, rewards, j, 0, 2) + single_change(kinds, rewards, j, 1, 3) == rhs
                    COUNTS['single_change_factor_cases'] += 1


def check_exposure_lists():
    for n in range(6):
        for straight in product((False, True), repeat=n):
            rewards = tuple(F((-1)**i * (i + 2), 11) if i % 3 else F(0) for i in range(n))
            for length in range(n + 1):
                for order in permutations(range(n), length):
                    rhs = sum(rewards[j] * ordered_multiplier(straight, order, j) for j in set(order))
                    assert exposure(straight, rewards, order) == rhs
                    COUNTS['nodup_exposure_lists'] += 1


def check_true_prefixes():
    for n in range(6):
        for w in product(range(4), repeat=n):
            kinds, rewards = word_data(w)
            ms = matrices(kinds, rewards)
            total = terminal_value(run(ms))
            for length in range(n + 1):
                pk, pr = word_data(w[:length])
                prefix_ms = matrices(pk, pr)
                assert prefix_ms == ms[:length], (w, length)
                COUNTS['prefix_departure_matrices'] += length
                prefix = run(prefix_ms)
                suffix_values = [terminal_value(run(ms[length:], tuple(F(a == b) for b in range(4))))
                                 for a in range(4)]
                assert total == sum(prefix[a] * suffix_values[a] for a in range(4)), (w, length)
                COUNTS['prefix_suffix_splits'] += 1
            COUNTS['lattice_words_including_nontrails'] += 1


if __name__ == '__main__':
    check_raw_successors()
    check_phase_and_order_algebra()
    check_exposure_lists()
    check_true_prefixes()
    result = {'status': 'PASS', 'arithmetic': 'exact fractions.Fraction',
              'bounds': {'raw_memory': [1, 7], 'abstract_phase_length': [0, 6],
                         'exposure_indices': [0, 5], 'all_lattice_word_lengths': [0, 5]},
              'counts': dict(COUNTS),
              'limitation': 'Bounded independent-model sanity checks, not formal proofs; projection realization was inspected by construction.'}
    output = json.dumps(result, indent=2)
    Path(__file__).with_name('small-case-results.json').write_text(output + '\n')
    print(output)
