"""Finite diagnostics for the truth sweep; not Lean proofs.

Direction order, counts, dead sites, coefficients, and dyadic witness follow
the definitions in the audited repository. All scalar arithmetic is exact.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
import random


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
U, C = (-1, 0), (0, 0)
TARGET = {"B": (1, 0), "C": (0, 1)}
ALPHA = (F(150000, 10**6), F(145217, 10**6))
BETA = (F(357549, 10**6), F(352782, 10**6))
BETA_PRIME = (F(344661, 10**6), F(340008, 10**6))
PASSAGE = (F(200, 187), F(1000, 961))
H = {"B": F(1), "C": F(5404319552844595, 4503599627370496)}


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def sub(x, y):
    return x[0] - y[0], x[1] - y[1]


def vertices(word, start=U):
    result = [start]
    for d in word:
        result.append(add(result[-1], STEPS[d]))
    return result


def bond(x, y):
    return frozenset((x, y))


def suffix_window(word, j):
    # takeWord has length j, padding with east only beyond len(word).
    prefix = tuple(word[k] if k < len(word) else 0 for k in range(j))
    offset = max(j - 10, 0)
    return tuple(prefix[offset + k] if offset + k < j else 0 for k in range(10))


def pair_type(p):
    a, b = tuple(p)
    return "B" if a[0] == b[0] or a[1] == b[1] else "C"


def sum_pairs(out, live, straight):
    result = F(0)
    for p in combinations(sorted(live | {out}), 2):
        coefficient = (BETA_PRIME[straight] if len(live) == 1 else BETA[straight]) \
            if out in p else ALPHA[straight]
        result += coefficient * H[pair_type(p)]
    return result


def relaxed_reward(x, incoming, outgoing, dead):
    out = add(x, STEPS[outgoing])
    live = {add(x, s) for s in STEPS} - {sub(x, STEPS[incoming]), out} - dead
    return sum_pairs(out, live, outgoing == incoming)


def phase_transition(kind, reward, phi, psi):
    if phi == psi:
        if kind == "revisit":
            return F(1, 5)
        if kind == "straight" and phi in "ABC":
            return PASSAGE[True] / 3
        if kind == "turn" and phi == "A":
            return PASSAGE[False] / 3
        return F(1, 3)
    if phi == "A" and psi == "C" and kind == "turn":
        return PASSAGE[False] * reward / 3
    if phi == "B" and psi == "D" and kind == "straight":
        return PASSAGE[True] * reward / 3
    return F(0)


def check_trails(max_length=12):
    counts = [0] * (max_length + 1)
    checks = Counter()
    word, vs, used = [], [U], set()
    dep, arr = Counter(), Counter()

    def visit():
        n = len(word)
        counts[n] += 1
        if n == max_length:
            return
        x = vs[-1]
        if n >= 10:
            window = suffix_window(word, n)
            wv = vertices(window, (0, 0))
            assert window == tuple(word[-10:])
            assert wv == [sub(v, vs[n - 10]) for v in vs[n - 10:]]
            wb = {bond(a, b) for a, b in zip(wv, wv[1:])}
            assert len(wb) == 10
            checks["raw_windows"] += 1
        for d, step in enumerate(STEPS):
            y = add(x, step)
            edge = bond(x, y)
            if edge in used:
                continue
            if n:
                assert d != (word[-1] + 2) % 4
            if n >= 10:
                assert d != (window[-1] + 2) % 4
                assert bond(wv[-1], add(wv[-1], step)) not in wb
                assert window[-1] == word[-1]
                extended = tuple(word) + (d,)
                assert suffix_window(extended, n) == window
                assert window[1:] + (d,) == suffix_window(extended, n + 1)
                remembered = wv[-1] in wv[:-1]
                true_revisit = dep[x] > 0
                assert not remembered or true_revisit
                if not true_revisit:
                    assert not remembered
                    assert (d == window[-1]) == (d == word[-1])
                checks["suffix_steps_including_final_departures"] += 1
            dep[x] += 1
            arr[y] += 1
            for z in (x, y):
                assert dep[z] + arr[z] <= 4
                assert dep[z] <= arr[z] + 1
                assert dep[z] <= 2
            checks["incident_and_balance_extensions"] += 1
            word.append(d)
            vs.append(y)
            used.add(edge)
            visit()
            used.remove(edge)
            vs.pop()
            word.pop()
            dep[x] -= 1
            arr[y] -= 1

    visit()
    assert counts[10] == 60092
    return {"raw_trail_counts_by_length": counts, **checks}


def check_rewards_and_rows():
    checks = Counter()
    for straight in (False, True):
        assert 0 < ALPHA[straight]
        assert 0 < BETA_PRIME[straight] <= BETA[straight]
        assert F(1, 5) <= F(1, 3) <= PASSAGE[straight] / 3
    assert min(H.values()) > 0
    for x in ((0, 0), (-1, 0), (5, -7)):
        ns = [add(x, step) for step in STEPS]
        # Remote dead sites have no effect. Outgoing sites may be declared dead.
        dead_sets = [{ns[k] for k in range(4) if mask >> k & 1} | {add(x, (11, 17))}
                     for mask in range(16)]
        for incoming in range(4):
            for outgoing in range(4):
                if outgoing == (incoming + 2) % 4:
                    continue
                rewards = [relaxed_reward(x, incoming, outgoing, dead) for dead in dead_sets]
                for a, da in enumerate(dead_sets):
                    for b, db in enumerate(dead_sets):
                        if da <= db:
                            assert rewards[b] <= rewards[a]
                            checks["nested_dead_set_comparisons"] += 1
                for reward in rewards:
                    assert reward >= 0
                    for kind in ("straight", "turn", "revisit"):
                        for phi in "ABCD":
                            for psi in "ABCD":
                                value = phase_transition(kind, reward, phi, psi)
                                assert value >= 0
                                if kind != "revisit":
                                    for smaller in (F(0), reward / 2, reward):
                                        assert phase_transition(kind, smaller, phi, psi) <= value
                                    assert phase_transition("revisit", F(0), phi, psi) <= value
                                checks["scalar_phase_entries"] += 1
    return dict(checks)


def check_reward_identity():
    checks = 0
    rng = random.Random(20261116)
    words = [tuple(rng.randrange(4) for _ in range(rng.randrange(1, 25))) for _ in range(1000)]
    # Includes nontrails: the reward equality itself needs no trail premise.
    for word in words:
        vs = vertices(word)
        dep = Counter()
        for i, outgoing in enumerate(word):
            x = vs[i]
            incoming = 2 if i == 0 else word[i - 1]
            ns = {add(x, step) for step in STEPS}
            dead_at = lambda z: z == C or dep[z] >= 2
            response = ns - {sub(x, STEPS[incoming])}
            live_other = {z for z in response - {vs[i + 1]} if not dead_at(z)}
            witness = sum_pairs(vs[i + 1], live_other, incoming == outgoing)
            true_dead_set = {C} | {z for z in ns if dead_at(z)}
            assert witness == relaxed_reward(x, incoming, outgoing, true_dead_set)
            checks += 1
            dep[x] += 1
    return {"random_word_reward_identities": checks, "seed": 20261116}


def check_known_site_examples():
    examples = [
        ("W" * 3 + "N" * 3 + "E" * 3 + "S" * 4 + "E" * 2 + "N", 12, U),
        ("W" * 4 + "N" * 3 + "E" * 3 + "S" * 4 + "E" * 3 + "N", 13, (-2, 0)),
    ]
    result = []
    for text, i, site in examples:
        word = tuple("ENWS".index(d) for d in text)
        vs = vertices(word)
        edges = [bond(a, b) for a, b in zip(vs, vs[1:])]
        assert len(set(edges)) == len(word)
        assert word[0] == 2
        assert vs[-1] == TARGET["B"]
        assert C not in vs and TARGET["B"] not in vs[:-1]
        assert C not in vs[:13] and TARGET["B"] not in vs[:13]
        assert max(Counter(vs[:-1]).values()) <= 2
        assert vs[i] == site and site in vs[:i]
        assert site not in vs[i - 10:i]
        assert edges[i] != edges[0]
        for phi in "ABCD":
            for psi in "ABCD":
                expected = F(1, 5) if phi == psi else F(0)
                assert phase_transition("revisit", F(17), phi, psi) == expected
        result.append({"X": "B", "d0": "west", "L": 12, "word": text,
                       "n": len(word), "suffix_departure_index": i, "site": site})
    return result


if __name__ == "__main__":
    summary = {
        "scope": "Finite diagnostics, not proofs of the universally quantified Lean leaves.",
        "trail_checks": check_trails(),
        "reward_and_phase_checks": check_rewards_and_rows(),
        "reward_identity_checks": check_reward_identity(),
        "nonvacuous_known_site_examples": check_known_site_examples(),
    }
    destination = Path(__file__).with_name("validation.json")
    destination.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
