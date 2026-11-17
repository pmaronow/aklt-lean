"""Exact finite diagnostics for the sector definitions; this is not a Lean proof."""

from fractions import Fraction
from itertools import product
import json


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def mul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def comm(a, b):
    return add(mul(a, b), scale(-1, mul(b, a)))


def adjoint(a):
    return [[x.conjugate() for x in col] for col in zip(*a)]


def lift(n, j, a):
    coordinates = list(product(range(2), repeat=n))
    return [
        [a[s[j]][t[j]] if all(s[k] == t[k] for k in range(n) if k != j) else 0
         for t in coordinates]
        for s in coordinates
    ]


def total(n, a):
    out = [[0 for _ in range(2**n)] for _ in range(2**n)]
    for j in range(n):
        out = add(out, lift(n, j, a))
    return out


# Derive the ladder matrices from the actual Pauli signs before using rationals.
sigma_x = [[0, 1], [1, 0]]
sigma_y = [[0, -1j], [1j, 0]]
plus_complex = scale(Fraction(1, 2), add(sigma_x, scale(1j, sigma_y)))
minus_complex = scale(Fraction(1, 2), add(sigma_x, scale(-1j, sigma_y)))
assert plus_complex == [[0, 1], [0, 0]]
assert minus_complex == [[0, 0], [1, 0]]
local_z = [[Fraction(1, 2), 0], [0, Fraction(-1, 2)]]
local_plus = [[0, 1], [0, 0]]
local_minus = [[0, 0], [1, 0]]

for n in range(5):
    z, plus, minus = [total(n, a) for a in (local_z, local_plus, local_minus)]
    assert adjoint(z) == z
    assert adjoint(plus) == minus
    assert comm(z, plus) == plus
    assert comm(z, minus) == scale(-1, minus)
    assert comm(plus, minus) == scale(2, z)


# Read off the eight groupLeader values and corner groupSecond values.
# Every raw PatternData yields one of these layouts, or a subset of them.
leaders = [0, 2, 4, 6, 8, 11, 14, 17]
maximal_groups = [(0, 1), (2, 3), (4, 5), (6, 7), (8,), (11,), (14,), (17,)]
all_tokens = [j for group in maximal_groups for j in group]
assert len(all_tokens) == len(set(all_tokens)) == 12
assert all(min(19, leaders[i] + 1) == maximal_groups[i][1] for i in range(4))

# Each local basis item is (twice its rational weight, [(bits, coefficient)]).
local = {
    "absent": [(0, [((), 1)])],
    "single": [(1, [((0,), 1)]), (-1, [((1,), 1)])],
    "symmetric": [
        (2, [((0, 0), 1)]),
        (0, [((0, 1), 1), ((1, 0), 1)]),
        (-2, [((1, 1), 1)]),
    ],
    "exterior": [(0, [((0, 1), 1), ((1, 0), -1)])],
}
layout_options = [("absent", "single", "symmetric", "exterior")] * 4 + [
    ("absent", "single")
] * 4
layouts = vectors = support_coordinates = 0
for layout in product(*layout_options):
    layouts += 1
    single_count = layout.count("single")
    twice_kappa = single_count % 2
    for basis in product(*(local[kind] for kind in layout)):
        vectors += 1
        twice_weight = sum(item[0] for item in basis)
        assert (twice_weight - twice_kappa) % 2 == 0
        nonzero = False
        for tensor_entry in product(*(item[1] for item in basis)):
            support_coordinates += 1
            coefficient = 1
            twice_coordinate_weight = 0
            for bits, value in tensor_entry:
                coefficient *= value
                twice_coordinate_weight += len(bits) - 2 * sum(bits)
            assert coefficient in (-1, 1)
            assert twice_coordinate_weight == twice_weight
            nonzero = True
        assert nonzero


# Integer descent/ascent checks include both kappa choices and every sign of z.
walk_cases = walk_steps = 0
for twice_kappa in (0, 1):
    for displacement in range(-50, 51):
        walk_cases += 1
        twice_m = twice_kappa + 2 * displacement
        step = -2 if displacement > 0 else 2
        for _ in range(abs(displacement)):
            assert twice_m > 0 if step < 0 else twice_m < 0
            twice_m += step
            walk_steps += 1
        assert twice_m == twice_kappa

print(json.dumps({
    "matrix_token_counts": list(range(5)),
    "matrix_identities_per_token_count": 5,
    "maximal_distinct_group_tokens": len(all_tokens),
    "group_layouts": layouts,
    "sector_basis_vectors": vectors,
    "nonzero_support_coordinates": support_coordinates,
    "ladder_walk_cases": walk_cases,
    "ladder_steps": walk_steps,
    "result": "all assertions passed",
}, indent=2))
