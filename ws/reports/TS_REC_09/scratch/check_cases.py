"""Finite, exact-arithmetic checks of the definitions; contains no Lean proofs."""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
START, CENTRE = (-1, 0), (0, 0)
TARGET = {"B": (1, 0), "C": (0, 1)}
H = {"B": Q(1), "C": Q(5404319552844595, 4503599627370496)}
RHO0 = Q(993015, 10**6)
C = Q(18094, 100000) + 2 * Q(36751, 100000)
RATE = Q(1119948287353, 1120437614225)
MAX_N = 10
STATS = Counter()


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def dist(x, y):
    return abs(x[0] - y[0]) + abs(x[1] - y[1])


def passage(straight):
    return Q(1000, 961) if straight else Q(200, 187)


def coeff(straight, outgoing_in_pair, other_count):
    if outgoing_in_pair:
        if other_count == 1:
            return Q(340008 if straight else 344661, 10**6)
        return Q(352782 if straight else 357549, 10**6)
    return Q(145217 if straight else 150000, 10**6)


def pair_type(p):
    a, b = p
    return "B" if a[0] == b[0] or a[1] == b[1] else "C"


def trail_data(vertices, directions, X):
    n = len(directions)
    departures = Counter()
    base, weight = Q(1), Q(1)
    first, rewards, kappas, factors = [], {}, {}, {}
    for i, outgoing in enumerate(directions):
        x, o = vertices[i], vertices[i + 1]
        incoming = 2 if i == 0 else directions[i - 1]
        assert outgoing != (incoming + 2) % 4
        straight = outgoing == incoming
        revisit = departures[x] > 0
        base *= Q(1, 5) if revisit else Q(1, 3)
        weight *= Q(1, 5) if revisit else passage(straight) / 3
        arrival = add(x, STEPS[(incoming + 2) % 4])
        response_neighbours = {add(x, step) for step in STEPS} - {arrival}
        assert o in response_neighbours
        assert o != CENTRE and departures[o] < 2
        live_other = {z for z in response_neighbours - {o}
                      if z != CENTRE and departures[z] < 2}
        assert len(live_other) <= 2
        local = defaultdict(Q)
        reward, total = Q(0), Q(0)
        for p in combinations(sorted(live_other | {o}), 2):
            Y = pair_type(p)
            s = max(min(dist(z, START), dist(z, TARGET[X])) for z in p)
            a = coeff(straight, o in p, len(live_other))
            assert a > 0
            assert 2 * s <= n + 2
            assert s <= n + 1
            local[Y, s] += a
            reward += a * H[Y]
            total += a
        assert total <= C
        if not revisit:
            first.append(i)
            kappas[i], rewards[i], factors[i] = local, reward, passage(straight)
            STATS["first_visits"] += 1
            STATS["first_visits_live_other_" + str(len(live_other))] += 1
            STATS["straight_first_visits" if straight else "turn_first_visits"] += 1
        else:
            STATS["revisit_departures"] += 1
        departures[x] += 1
    if n <= 12:
        order = sorted(first, key=lambda i: (rewards[i] == 0,
                       (factors[i] - 1) / (factors[i] * rewards[i])
                       if rewards[i] else Q(0), i))
    else:
        order = ([i for i in first if directions[i] == (2 if i == 0 else directions[i - 1])]
                 + [i for i in first if directions[i] != (2 if i == 0 else directions[i - 1])])
        STATS["long_order_trails"] += 1
    assert sorted(order) == first and len(set(order)) == len(order)
    prefix, weighted, direct_exposure = Q(1), Q(0), Q(0)
    out = defaultdict(Q)
    for i in order:
        prefix *= factors[i]
        direct_exposure += rewards[i] * prefix
        for (Y, s), a in kappas[i].items():
            out[Y, s] += base * prefix * a
    for i in reversed(order):
        weighted = factors[i] * (rewards[i] + weighted)
    assert weighted == direct_exposure
    contribution = base * weighted
    assert sum((a * H[Y] for (Y, _), a in out.items()), Q(0)) == contribution
    if n:
        assert contribution / H[X] <= n * C * max(H.values()) / min(H.values()) * weight
    assert n % 2 == 0
    for theta in [Q(1), Q(9, 16), Q(81, 100), Q(99980001, 10**8)]:
        for Y in TARGET:
            shifted = sum((a * theta**(-s) for (Z, s), a in out.items() if Z == Y), Q(0))
            assert shifted <= n * C * weight * theta**(-n // 2 - 1)
        b = (1 + RATE) / 2
        theta_increment = (1 + b) / 2
        delta = sum((a * H[Y] * (theta_increment**(-s) - 1)
                     for (Y, s), a in out.items()), Q(0)) / H[X]
        assert 0 <= delta <= ((1 - theta_increment) * max(H.values()) / min(H.values())
                              * C * n * (n + 1) * b**(-n - 2) * weight)
    STATS["closed_trails_checked"] += 1
    return out, contribution, weight


def enumerate_open():
    counts = [0] * (MAX_N + 1)
    weights = [Q(0)] * (MAX_N + 1)

    def walk(x, used, departures, last, n, weight):
        counts[n] += 1
        weights[n] += weight
        if n == MAX_N:
            return
        revisit = departures[x] > 0
        departures[x] += 1
        for d, step in enumerate(STEPS):
            if n == 0 and d == 0:
                continue
            o = add(x, step)
            edge = frozenset((x, o))
            if edge in used:
                continue
            factor = Q(1, 5) if revisit else passage(d == last) / 3
            walk(o, used | {edge}, departures, d, n + 1, weight * factor)
        departures[x] -= 1

    walk(START, set(), Counter(), 2, 0, Q(1))
    for n, value in enumerate(weights):
        assert value <= 10 * RATE**n
    return counts, weights


def enumerate_closed(X):
    by_length = [defaultdict(Q) for _ in range(MAX_N + 1)]
    weighted_rows = [Q(0)] * (MAX_N + 1)
    trail_weights = [Q(0)] * (MAX_N + 1)
    counts = [0] * (MAX_N + 1)

    def walk(vertices, directions, used):
        n, x = len(directions), vertices[-1]
        if x == TARGET[X]:
            values, contribution, weight = trail_data(vertices, directions, X)
            counts[n] += 1
            weighted_rows[n] += contribution
            trail_weights[n] += weight
            for k, a in values.items():
                by_length[n][k] += a
            return
        if n == MAX_N:
            return
        for d, step in enumerate(STEPS):
            if n == 0 and d == 0:
                continue
            o = add(x, step)
            edge = frozenset((x, o))
            if o == CENTRE or edge in used:
                continue
            walk(vertices + [o], directions + [d], used | {edge})

    walk([START], [], set())
    return by_length, weighted_rows, trail_weights, counts


def check_numeric_choices():
    samples = 0
    q_values = [Q(1, 10**6), Q(1, 10), Q(1, 2), Q(9, 10), Q(99, 100), RATE, Q(10**6 - 1, 10**6)]
    for CV in [Q(1), Q(10), Q(10**6)]:
        for q in q_values:
            b, Hratio = (1 + q) / 2, max(H.values()) / min(H.values())
            r = q / b
            B = 2 * Hratio * C * CV * b**(-2) * r / (1 - r)**3
            eps = min((1 - b) / 2, (1 - RHO0) / (2 * B))
            theta, rho = 1 - eps, (1 + RHO0) / 2
            assert B > 0 and eps > 0
            assert q*q < theta < 1 and b < theta
            assert RHO0 < rho < 1
            assert RHO0 + (1 - theta) * B <= rho
            samples += 1
    powers = 0
    for b in [Q(1, 1000), Q(1, 20), Q(1, 4), Q(1, 2), Q(9, 10), Q(99, 100), Q(999, 1000)]:
        for theta in [b + (1 - b) / 100, (1 + b) / 2, Q(1)]:
            for n in range(21):
                for s in range(n + 2):
                    inc = theta**(-s) - 1
                    assert 0 <= inc <= (1 - theta) * (n + 1) * b**(-n - 2)
                    powers += 1
    return samples, powers


def main():
    choices, powers = check_numeric_choices()
    open_counts, open_weights = enumerate_open()
    summary = {"max_exhaustive_length": MAX_N, "open_trails_by_length": open_counts,
               "transport_samples": choices, "shift_power_samples": powers, "rows": {}}
    for X in TARGET:
        by_length, rows, closed_weights, counts = enumerate_closed(X)
        aggregated = defaultdict(Q)
        for n in range(MAX_N + 1):
            assert closed_weights[n] <= open_weights[n]
            for k, a in by_length[n].items():
                aggregated[k] += a
            assert sum((a * H[Y] for (Y, _), a in by_length[n].items()), Q(0)) == rows[n]
            for theta in [Q(1), Q(99980001, 10**8)]:
                for Y in TARGET:
                    shifted = sum((a * theta**(-s) for (Z, s), a in by_length[n].items() if Z == Y), Q(0))
                    assert shifted <= n * C * 10 * RATE**n * theta**(-n // 2 - 1)
        assert sum(rows) <= RHO0 * H[X]
        for d in [-5, 0, 3]:
            def F(Y, depth):
                return Q(((0 if Y == "B" else 3) + 5 * depth) % 11, 5)

            regrouped = sum((a * F(Y, d - s) for (Y, s), a in aggregated.items()), Q(0))
            direct = sum((a * F(Y, d - s) for row in by_length for (Y, s), a in row.items()), Q(0))
            assert regrouped == direct
            for N in [0, 1, 2, 4, MAX_N + 1]:
                partial = sum((a * F(Y, d - s) for row in by_length[:N] for (Y, s), a in row.items()), Q(0))
                assert 0 <= partial <= regrouped
        summary["rows"][X] = {"closed_trails_by_length": counts,
                              "cutoff_row_exact": str(sum(rows)),
                              "cutoff_row_decimal": float(sum(rows)),
                              "H3_ceiling_decimal": float(RHO0 * H[X]),
                              "max_nonzero_shift": max((s for _, s in aggregated), default=0)}
    long_words = {"B": [1] * 6 + [0] * 2 + [3] * 6,
                  "C": [1] * 7 + [0] + [3] * 6}
    for X, word in long_words.items():
        vertices = [START]
        for d in word:
            vertices.append(add(vertices[-1], STEPS[d]))
        assert vertices[-1] == TARGET[X]
        assert CENTRE not in vertices and TARGET[X] not in vertices[:-1]
        assert len({frozenset(p) for p in zip(vertices, vertices[1:])}) == len(word)
        trail_data(vertices, word, X)
    summary["statistics"] = dict(STATS)
    summary["status"] = "PASS"
    (ROOT / "case_checks.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
