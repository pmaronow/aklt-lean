"""Exact arithmetic and finite geometry checks; no leaf proofs."""

from fractions import Fraction as F


def crude_log_upper(s):
    t = (1 - s) / (1 + s)
    return 2 / (1 - s) * (t + t**3 / 3 + t**5 / (5 * (1 - t**2)))


beta_enclosure = crude_log_upper(F(41, 50)) / 3
beta_prime_enclosure = crude_log_upper(F(22, 25)) / 3
assert beta_enclosure == F(340634561, 926892330)
assert beta_prime_enclosure == F(24332081, 68523180)
assert beta_enclosure < F(367502, 10**6) < F(36751, 10**5)
assert beta_prime_enclosure < F(35510, 10**5)
alpha_lower = 1 / (3 * F(34, 25)) - 1 / (5 * F(116, 125))
alpha_upper = F(367502, 10**6) - 1 / (5 * F(134, 125))
assert alpha_lower == F(175, 5916) > 0
assert alpha_upper == F(6061317, 33500000)
assert F(18094, 10**5) - alpha_upper == F(173, 33500000) > 0


def neighbours(x):
    a, b = x
    return {(a + 1, b), (a - 1, b), (a, b + 1), (a, b - 1)}


# Explicit nonempty premise examples, one for each neighbour count.
# All sites of the square have U status; outside sites have X status.
# All kept sets are empty except for both flags of the selected centre bonds.
volume = {(a, b) for a in range(-2, 3) for b in range(-2, 3)}
centre = (0, 0)
protected = {x for x in volume if 3 - max(abs(x[0]), abs(x[1])) <= 2}
assert centre not in protected
assert all(not (neighbours(x) - volume) for x in neighbours(centre))
for count, selected in (
    (2, {(1, 0), (0, 1)}),
    (3, {(1, 0), (0, 1), (-1, 0)}),
):
    kept = {x: set() for x in volume}
    kept[centre] = selected
    for endpoint in selected:
        kept[endpoint] = {centre}
    present = {
        x: {z for z in kept[x] if z in volume and x in kept[z]}
        for x in volume
    }
    assert len(present[centre]) == count <= 3
    assert all(kept[x] <= neighbours(x) & volume for x in volume)
    assert all(
        len(present[x]) + len(neighbours(x) - volume) <= 4 for x in volume
    )

print('Exact rational bounds and both nonvacuity geometries passed.')
