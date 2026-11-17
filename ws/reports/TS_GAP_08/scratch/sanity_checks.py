"""Small-case diagnostics for the truth sweep; these are not proofs."""

from fractions import Fraction
from itertools import product


def sup_dist(x, y):
    return max(abs(x[0] - y[0]), abs(x[1] - y[1]))


geometry_cases = 0
for a in ((0, 0), (-2, 3)):
    for u in range(4):
        square = tuple(product(range(a[0] - u, a[0] + u + 1),
                               range(a[1] - u, a[1] + u + 1)))
        for offset in product(range(-u - 3, u + 4), repeat=2):
            y = (a[0] + offset[0], a[1] + offset[1])
            if y in square:
                continue
            distance = min(sup_dist(y, x) for x in square)
            assert distance >= 1
            if distance != 1:
                assert all(sup_dist(y, x) > 1 for x in square)
            geometry_cases += 1

localization_cases = 0
for sizes in ((), (1,), (2,), (1, 2, 3), (2, 3, 2, 1)):
    configs = tuple(product(*(range(size) for size in sizes)))
    for sigma, tau in product(configs, repeat=2):
        distance = sum(s != t for s, t in zip(sigma, tau))
        for selected in product((False, True), repeat=len(sizes)):
            near_count = selected.count(False)
            disagree = any(chosen and s != t
                           for chosen, s, t in zip(selected, sigma, tau))
            assert distance <= near_count + len(sizes) * int(disagree)
            localization_cases += 1

power_cases = 0
grid = tuple(Fraction(k, 8) for k in range(9))
for n in (4, 5, 8, 44):
    for d, delta in product(grid, repeat=2):
        if d <= delta:
            assert (1 - delta) ** (n - 3) <= (1 - d) ** (n - 3)
            power_cases += 1

print(f'Exterior square-distance checks passed: {geometry_cases}')
print(f'Pointwise Hamming localization checks passed: {localization_cases}')
print(f'Exact rational power comparisons passed: {power_cases}')
print('Included u=0, empty site sets, singleton and site-dependent alphabets,')
print('empty/full far sets, n=4, d=0, delta=0, delta=1, and d=1.')
