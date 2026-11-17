"""Finite exact-arithmetic checks for the truth sweep; these are not Lean proofs."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import factorial, isqrt
from random import Random


rng = Random(707)
counts = Counter()


def probability_row(size):
    weights = [rng.randrange(5) for _ in range(size)]
    if not any(weights):
        weights[0] = 1
    return [F(w, sum(weights)) for w in weights]


# Omega = {0,1}; pair states are 00,01,10,11. Rows depend on the
# entire current pair and on time. Zero atoms and delta endpoints occur.
for m in range(4):
    for mask in range(2**m):
        selected = [j for j in range(m) if mask & (1 << j)]
        for delta in [F(0), F(1, 3), F(1, 2), F(1)]:
            for _ in range(2):
                initial = probability_row(4)
                kernels = []
                for j in range(m):
                    rows = []
                    success_states = [v for v in range(4) if v // 2 == j % 2]
                    failure_states = [v for v in range(4) if v not in success_states]
                    for state in range(4):
                        success = delta + (1 - delta) * F(rng.randrange(5), 4)
                        split_success = probability_row(2)
                        split_failure = probability_row(2)
                        row = [F(0)] * 4
                        for k, v in enumerate(success_states):
                            row[v] = success * split_success[k]
                        for k, v in enumerate(failure_states):
                            row[v] = (1 - success) * split_failure[k]
                        assert sum(row) == 1
                        assert sum(row[v] for v in success_states) >= delta
                        rows.append(row)
                    kernels.append(rows)
                total = F(0)
                failure = F(0)
                endpoint = [F(0)] * 4
                endpoint_disagreement = F(0)
                for trace in product(range(4), repeat=m + 1):
                    weight = initial[trace[0]]
                    for j in range(m):
                        weight *= kernels[j][trace[j]][trace[j + 1]]
                    total += weight
                    endpoint[trace[-1]] += weight
                    if trace[-1] in (1, 2):
                        endpoint_disagreement += weight
                    if all(trace[j + 1] // 2 != j % 2 for j in selected):
                        failure += weight
                assert total == 1
                assert failure <= (1 - delta) ** len(selected)
                assert endpoint_disagreement == endpoint[1] + endpoint[2]
                assert endpoint_disagreement <= total
                counts['finite_chain_models'] += 1


# The homogeneous marginal-TV inequality used by TerminalRadiusStatement:
# no normalization of the finite coupling is imposed here.
configurations = list(product(range(2), repeat=2))
for scale in [F(0), F(1, 10), F(1), F(5)]:
    for _ in range(20):
        mass = [[scale * F(rng.randrange(8), 7) for _ in configurations]
                for _ in configurations]
        first = [sum(row) for row in mass]
        second = [sum(mass[i][j] for i in range(4)) for j in range(4)]
        for near_mask in range(4):
            target = [k for k in range(2) if near_mask & (1 << k)]
            first_target = Counter()
            second_target = Counter()
            for i, sigma in enumerate(configurations):
                first_target[tuple(sigma[k] for k in target)] += first[i]
                second_target[tuple(sigma[k] for k in target)] += second[i]
            tv = sum(abs(first_target[v] - second_target[v])
                     for v in set(first_target) | set(second_target)) / 2
            disagreement = sum(mass[i][j] for i, sigma in enumerate(configurations)
                               for j, tau in enumerate(configurations)
                               if any(sigma[k] != tau[k] for k in target))
            assert tv <= disagreement
            counts['unnormalized_coupling_checks'] += 1


# Boundary n=44, several tail sizes, and the real maximizer of
# d^20*(1-d)^(n-3) within the permitted interval.
binomial_constant = 2**20 * factorial(20)
for n in list(range(44, 61)) + [100, 250, 1000]:
    for d in [F(1, 2), F(1, 3), F(1, 10), F(1, 100),
              F(1, 10**6), F(20, n + 17)]:
        r = n - 3
        assert r >= 41 and n - 22 >= F(n, 2)
        tail = (1 - d)**r
        bound = F(binomial_constant, 1) / (d**20 * n**20)
        assert tail <= bound
        counts['binomial_tail_checks'] += 1


def interval_intersection_card(left1, right1, left2, right2):
    return max(0, min(right1, right2) - max(left1, left2) + 1)


# The near set is the intersection of the physical square with a
# sup-ball centered at arbitrary y, including y inside or far outside.
for n in range(1, 6):
    radius, near_radius = n**8, n**3
    for a in [(0, 0), (-3, 4), (7, -9)]:
        for dx, dy in product([0, near_radius, near_radius + 1,
                               radius, radius + near_radius + 1], repeat=2):
            y = (a[0] + dx, a[1] - dy)
            near_card = 1
            for k in range(2):
                near_card *= interval_intersection_card(
                    a[k] - radius, a[k] + radius,
                    y[k] - near_radius, y[k] + near_radius)
            assert near_card <= (2 * near_radius + 1)**2 <= 25 * n**6
            assert (2 * radius + 1)**2 <= 25 * n**16
            counts['cardinality_checks'] += 1
assert (2 * 0**8 + 1)**2 > 25 * 0**16  # n>=1 is necessary.


for l in [0, 64, 10000]:
    for mstar in [0, 10**24]:
        for d in [F(1, 2), F(1, 3), F(1, 10), F(3, 2), F(1, 10**6)]:
            def valid(n):
                return (n >= 44 and mstar <= n**8
                        and max(50000, 6 * (l + 1)) <= n**2
                        and 50000 * binomial_constant <= n**12 * d**20)

            lower, upper = 0, 1
            while not valid(upper):
                upper *= 2
            while upper - lower > 1:
                middle = (lower + upper) // 2
                if valid(middle):
                    upper = middle
                else:
                    lower = middle
            n = upper
            assert valid(n) and not valid(n - 1)
            assert max(mstar, max(16, 6 * (l + 1))**4) <= n**8
            assert n >= 4 and isqrt(isqrt(n**8)) == n**2
            assert n <= n**2 and n * n**2 == n**3 and n**2 >= 16
            counts['scale_checks'] += 1
            if d <= F(1, 2):
                tail_bound = F(binomial_constant, 1) / (d**20 * n**20)
                assert 25 * n**6 <= F(n**8, 2000)
                assert 25 * n**16 * tail_bound <= F(n**8, 2000)
                assert 25 * n**6 + 25 * n**16 * tail_bound <= F(n**8, 1000)
                counts['budget_checks'] += 1


for u in [16**4, 16**4 + 1, 17**4 - 1, 100000, 123456789, 50000**4]:
    h = isqrt(isqrt(u))
    assert h >= 16 and h**4 <= u < (h + 1)**4
    assert h - 3 > 0
    counts['terminal_floor_checks'] += 1

for name, count in sorted(counts.items()):
    print(f'{name}: {count} passed')
print('All finite exact-arithmetic checks passed. These checks supplement the written mathematical audit.')
