"""Finite sanity checks of the audited definitions; no Lean proofs are generated."""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
REFLECT_DIRECTION = (0, 3, 2, 1)
START, CENTRE = (-1, 0), (0, 0)
TARGETS = ((1, 0), (0, 1))
TERMINAL = (F(0), F(0), F(1), F(1))
INITIAL = (F(1), F(1), F(0), F(0))


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def subtract(x, y):
    return x[0] - y[0], x[1] - y[1]


def reflect(x):
    return x[0], -x[1]


def vertices(w):
    result = [START]
    for d in w:
        result.append(add(result[-1], STEPS[d]))
    return result


def neighbours(x):
    return {add(x, s) for s in STEPS}


def pairs(s):
    return frozenset(frozenset(p) for p in combinations(s, 2))


def is_trail(w, vs):
    bonds = [frozenset((x, y)) for x, y in zip(vs, vs[1:])]
    return len(set(bonds)) == len(w) and (not w or w[0] != 0)


def closed(w, vs, target):
    return (
        is_trail(w, vs)
        and vs[-1] == target
        and CENTRE not in vs
        and target not in vs[:-1]
    )


def live_pairs(w, vs, i):
    incoming = w[i - 1] if i else 2
    incoming_site = subtract(vs[i], STEPS[incoming])
    counts = Counter(vs[:i])
    live = {
        z
        for z in neighbours(vs[i]) - {incoming_site, vs[i + 1]}
        if z != CENTRE and counts[z] < 2
    }
    return pairs(live | {vs[i + 1]})


def passage(straight):
    return F(1000, 961) if straight else F(200, 187)


def pair_type(p):
    return all(x[0] == y[0] or x[1] == y[1] for x in p for y in p)


def witness(p):
    return F(1) if pair_type(p) else F(5404319552844595, 4503599627370496)


def alpha(straight):
    return F(145217 if straight else 150000, 10**6)


def beta(straight):
    return F(352782 if straight else 357549, 10**6)


def beta_prime(straight):
    return F(340008 if straight else 344661, 10**6)


@lru_cache(None)
def reward(x, incoming, outgoing, dead):
    o = add(x, STEPS[outgoing])
    live = neighbours(x) - {subtract(x, STEPS[incoming]), o} - dead
    total = F(0)
    for p in pairs(live | {o}):
        coefficient = (
            beta_prime(incoming == outgoing) if len(live) == 1 else beta(incoming == outgoing)
        ) if o in p else alpha(incoming == outgoing)
        total += coefficient * witness(p)
    return total


def transition(kind, response, phi, psi):
    # kind: 0 = straight, 1 = turn, 2 = revisit.
    if phi == psi:
        if kind == 2:
            return F(1, 5)
        return (
            passage(kind == 0) / 3
            if (kind == 0 and phi in (0, 1, 2)) or (kind == 1 and phi == 0)
            else F(1, 3)
        )
    if phi == 0 and psi == 2 and kind == 1:
        return passage(False) * response / 3
    if phi == 1 and psi == 3 and kind == 0:
        return passage(True) * response / 3
    return F(0)


def check_reflection():
    words = departures = closed_words = 0
    for n in range(8):
        for w in product(range(4), repeat=n):
            words += 1
            rw = tuple(REFLECT_DIRECTION[d] for d in w)
            vs, rvs = vertices(w), vertices(rw)
            # Includes clamped indices beyond n, as wordVertex is total on Nat.
            for j in range(n + 3):
                assert rvs[min(j, n)] == reflect(vs[min(j, n)])
            assert closed(w, vs, TARGETS[0]) == closed(rw, rvs, TARGETS[0])
            assert (bool(w) and w[0] == 1) == (bool(rw) and rw[0] == 3)
            closed_words += sum(closed(w, vs, target) for target in TARGETS)
            for i in range(n):
                departures += 1
                incoming, rincoming = (w[i - 1], rw[i - 1]) if i else (2, 2)
                assert (w[i] == incoming) == (rw[i] == rincoming)
                assert (vs[i] in vs[:i]) == (rvs[i] in rvs[:i])
                image = frozenset(frozenset(reflect(z) for z in p) for p in live_pairs(w, vs, i))
                assert image == live_pairs(rw, rvs, i)
                for target in TARGETS:
                    if closed(w, vs, target):
                        assert vs[i + 1] == add(vs[i], STEPS[w[i]])
                        assert vs[i] not in (CENTRE, target) and vs[i + 1] != CENTRE
    return {"words_n_0_through_7": words, "departures": departures, "closed_words_B_and_C": closed_words}


def check_free_edges():
    positions = set(product(range(-3, 4), repeat=2)) | {(9, -7)}
    comparisons = 0
    # This also checks arbitrary local quotient labels, including labels that
    # would violate Correct. Only one class's labels occur in this inequality.
    for x, incoming, d in product(positions, range(4), range(4)):
        rfree = reward((0, 0), incoming, d, frozenset())
        assert reward(x, incoming, d, frozenset()) == rfree
        rstationary = reward(x, incoming, d, frozenset({CENTRE}))
        assert F(0) <= rstationary <= rfree
        for target, d0, allowed, kind, phi, psi in product(TARGETS, range(4), (False, True), range(3), range(4), range(4)):
            free = transition(kind, rfree, phi, psi) if allowed else F(0)
            if x in (CENTRE, target) or not allowed:
                stationary = F(0)
            elif x in (START, add(START, STEPS[d0])):
                if frozenset((x, add(x, STEPS[d]))) == frozenset((START, add(START, STEPS[d0]))) or kind == 2:
                    stationary = F(0)
                else:
                    stationary = F(1, 5) if phi == psi else F(0)
            elif add(x, STEPS[d]) == CENTRE:
                stationary = F(0)
            else:
                stationary = transition(kind, rstationary, phi, psi)
            assert F(0) <= stationary <= free
            comparisons += 1
    return {"positions": len(positions), "coefficient_comparisons": comparisons, "arithmetic": "exact Fraction"}


def actual_matrices(w):
    vs = vertices(w)
    matrices = []
    for i, d in enumerate(w):
        incoming = w[i - 1] if i else 2
        straight = d == incoming
        kind = 2 if vs[i] in vs[:i] else (0 if straight else 1)
        counts = Counter(vs[:i])
        live = {
            z for z in neighbours(vs[i]) - {subtract(vs[i], STEPS[incoming]), vs[i + 1]}
            if z != CENTRE and counts[z] < 2
        }
        r = sum(
            ((beta_prime(straight) if len(live) == 1 else beta(straight)) if vs[i + 1] in p else alpha(straight)) * witness(p)
            for p in pairs(live | {vs[i + 1]})
        )
        matrices.append(tuple(tuple(transition(kind, r, phi, psi) for psi in range(4)) for phi in range(4)))
    return matrices


def run_forward(matrices, initial):
    p = initial
    for matrix in matrices:
        p = tuple(sum(p[phi] * matrix[phi][psi] for phi in range(4)) for psi in range(4))
    return p


def check_word_expansion():
    # A deliberately arbitrary quotient whose successors stay in {0,1,2}.
    # These are valid Fin 3741 labels; Correct is not a premise of expansion.
    def successor(a, d):
        return (a + d + 1) % 3

    @lru_cache(None)
    def coefficient(target, d0, phi, a, x, d, psi):
        allowed = (a + d) % 4 != 0
        kind, incoming = (a + d) % 3, (2 * a) % 4
        if x in (CENTRE, target) or not allowed:
            return F(0)
        if x in (START, add(START, STEPS[d0])):
            if frozenset((x, add(x, STEPS[d]))) == frozenset((START, add(START, STEPS[d0]))) or kind == 2:
                return F(0)
            return F(1, 5) if phi == psi else F(0)
        if add(x, STEPS[d]) == CENTRE:
            return F(0)
        return transition(kind, reward(x, incoming, d, frozenset({CENTRE})), phi, psi)

    @lru_cache(None)
    def iterate(target, d0, r, phi, a, x):
        if r == 0:
            return TERMINAL[phi] if x == target else F(0)
        return sum(
            coefficient(target, d0, phi, a, x, d, psi)
            * iterate(target, d0, r - 1, psi, successor(a, d), add(x, STEPS[d]))
            for d, psi in product(range(4), range(4))
        )

    @lru_cache(None)
    def word_value(target, d0, word, phi, a, x):
        if not word:
            return TERMINAL[phi] if x == target else F(0)
        d, rest = word[0], word[1:]
        return sum(
            coefficient(target, d0, phi, a, x, d, psi)
            * word_value(target, d0, rest, psi, successor(a, d), add(x, STEPS[d]))
            for psi in range(4)
        )

    comparisons = 0
    for target, d0, r, phi, a, x in product(TARGETS, (1, 2), range(4), range(4), range(3), (CENTRE, START, (1, 1))):
        direct = iterate(target, d0, r, phi, a, x)
        expanded = sum(word_value(target, d0, w, phi, a, x) for w in product(range(4), repeat=r))
        assert direct == expanded
        comparisons += 1
    return {"lengths_checked": [0, 3], "state_and_length_comparisons": comparisons, "arithmetic": "exact Fraction"}


def check_long_prefix_examples():
    examples = []
    for height in range(5, 10):
        # Simple first-hit detours for B, of lengths 12,14,...,20.
        w = (1,) * height + (0, 0) + (3,) * height
        vs = vertices(w)
        assert closed(w, vs, TARGETS[0])
        if len(w) == 12:
            assert vs[12] == TARGETS[0]  # Intentionally belongs to the short row.
        else:
            prefix = w[:12]
            pvs = vertices(prefix)
            assert is_trail(prefix, pvs) and CENTRE not in pvs and TARGETS[0] not in pvs
        matrices = actual_matrices(w)
        full = sum(p * t for p, t in zip(run_forward(matrices, INITIAL), TERMINAL))
        p = run_forward(actual_matrices(w[:12]), INITIAL)
        split = F(0)
        for phi in range(4):
            delta = tuple(F(psi == phi) for psi in range(4))
            suffix = sum(a * b for a, b in zip(run_forward(matrices[12:], delta), TERMINAL))
            split += p[phi] * suffix
        assert full == split
        # Also compare entrywise larger nonnegative suffix matrices, including r=0.
        larger = [tuple(tuple(entry + F(1, 17) for entry in row) for row in matrix) for matrix in matrices[12:]]
        for phi in range(4):
            delta = tuple(F(psi == phi) for psi in range(4))
            a = sum(x * t for x, t in zip(run_forward(matrices[12:], delta), TERMINAL))
            b = sum(x * t for x, t in zip(run_forward(larger, delta), TERMINAL))
            assert a <= b
        examples.append(len(w))
    # A word with a true revisit: a square loop at the start, followed by a
    # disjoint lower detour to B. Its initial northward square avoids the centre.
    w = (1, 2, 3, 0) + (3,) * 5 + (0, 0) + (1,) * 5
    vs = vertices(w)
    assert closed(w, vs, TARGETS[0])
    assert vs[4] == START and TARGETS[0] not in vs[:12]
    examples.append(len(w))
    # The regrouping's numerical boundary is independent of the coefficients.
    for cutoff in range(13, 35):
        assert [12 + r for r in range(cutoff - 12 + 1) if r > 0] == list(range(13, cutoff + 1))
    return {"closed_example_lengths": examples, "cutoffs_checked": [13, 34], "zero_suffix_checked": True}


def main():
    result = {
        "reflection_and_closed_step_geometry": check_reflection(),
        "stationary_free_edge": check_free_edges(),
        "stationary_word_expansion": check_word_expansion(),
        "long_prefix_and_phase_boundaries": check_long_prefix_examples(),
        "status": "PASS",
        "scope": "Finite checks only; universal verdicts use the definition analysis in report.md.",
    }
    Path(__file__).with_name("small-checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
