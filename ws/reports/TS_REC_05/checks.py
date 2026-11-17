"""Finite and numerical audit checks; these are not formal proofs."""

from fractions import Fraction
from itertools import product
import json
import math
from pathlib import Path
import random


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


phi = (1 + math.sqrt(5)) / 2
radius = math.sqrt(phi + 2)
ico = []
for group, sign_a, sign_b in product(range(3), (-1, 1), (-1, 1)):
    a, b = sign_a, sign_b * phi
    v = ((0, a, b), (a, b, 0), (b, 0, a))[group]
    ico.append(tuple(x / radius for x in v))


def site(status, f):
    avg = sum(f(v) for v in ico) / 12
    return avg if status == "U" else 3 * avg / 5 + 2 * f((0, 0, 0)) / 5


def close(a, b):
    return abs(a - b) <= 2e-10 * max(1, abs(a), abs(b))


rng = random.Random(20261116)
moment_checks = 0
for k in range(4):
    for sample in range(100):
        a = tuple(rng.uniform(-3, 3) for _ in range(3))
        u = [tuple(rng.uniform(-3, 3) for _ in range(3)) for _ in range(k)]
        if sample == 0:
            a = (0, 0, 0)
        if sample == 1:
            u = [(2, -1, 0)] * k
        lhs = site("U", lambda n: dot(a, n) * math.prod(1 + dot(n, v) for v in u))
        rhs = sum(
            dot(a, u[i])
            * site("D", lambda n: math.prod(1 + dot(n, u[j]) for j in range(k) if j != i))
            for i in range(k)
        ) / 3
        assert close(lhs, rhs), ("U", k, a, u, lhs, rhs)
        moment_checks += 1
        if k <= 1:
            lhs_d = site("D", lambda n: dot(a, n) * math.prod(1 + dot(n, v) for v in u))
            rhs_d = sum(dot(a, v) for v in u) / 5
            assert close(lhs_d, rhs_d), ("D", k, a, u, lhs_d, rhs_d)
            moment_checks += 1


def lm(x, y):
    assert x > 0 and y > 0
    return x if x == y else (x - y) / math.log1p((x - y) / y)


a_floor = 116 / 125
analytic_checks = 0
for c, delta_t, delta_0 in product((1e-6, 0.6, 0.935, 0.961, 1, 2, 100), (0, 0.01, 1, 10), (0, 0.01, 1, 10)):
    lhs = 1 / (3 * lm(c + delta_t, 1 + delta_0))
    bound = 1 / (3 * lm(c, 1))
    assert lhs <= bound + 1e-10
    analytic_checks += 1

for c, jt, j0, delta_t, delta_0 in product(
    (0.6, 0.935, 0.961, 1), (a_floor, 1, 2, 100), (1, 2, 100), (0, 0.01, 1, 100), (0, 0.01, 1, 100)
):
    it, i0 = c * jt + delta_t, j0 + delta_0
    beta = 1 / (3 * lm(it, i0))
    beta_bound = 1 / (3 * lm(a_floor * c, 1))
    alpha = beta - 1 / (5 * lm(jt, j0))
    alpha_bound = beta_bound - 1 / (5 * lm(a_floor, 1))
    assert beta <= beta_bound + 1e-10
    assert alpha <= alpha_bound + 1e-10
    analytic_checks += 2

# A lattice square with a tail permits returning to a prior departure and
# taking its final live bond. Place the five vertices strictly inside a larger
# original square; every other vertex may be U with an empty kept set. This
# embeds every configuration below into an auxiliary lattice network with
# protected U sites and no original legs at any departure.
vertices = ((0, 0), (1, 0), (1, 1), (0, 1), (-1, 0))
edge_list = ((0, 1), (1, 2), (2, 3), (0, 3), (0, 4))
edge = lambda x, y: frozenset((x, y))
trace_checks = 0
valid_networks = 0
revisit_checks = 0
zero_length_checks = 0

for status_values in product("UDX", repeat=len(vertices)):
    for edge_flags in product((False, True), repeat=len(edge_list)):
        original_kept = {x: set() for x in range(len(vertices))}
        for (x, y), present in zip(edge_list, edge_flags):
            if present:
                original_kept[x].add(y)
                original_kept[y].add(x)

        def present_bonds(status, kept):
            return {
                edge(x, y)
                for x, y in edge_list
                if status[x] != "X" and status[y] != "X" and y in kept[x] and x in kept[y]
            }

        original_bonds = present_bonds(status_values, original_kept)

        def degree(bonds, x):
            return sum(x in bond for bond in bonds)

        if any(s == "D" and degree(original_bonds, x) > 2 for x, s in enumerate(status_values)):
            continue
        valid_networks += 1

        def visit(path, status, kept, consumed, coefficient, nd):
            global trace_checks, revisit_checks, zero_length_checks
            current_bonds = present_bonds(status, kept)
            assert current_bonds == original_bonds - consumed
            assert all(s != "D" or degree(current_bonds, x) <= 2 for x, s in enumerate(status))
            n = len(path) - 1
            assert coefficient > 0
            assert coefficient == Fraction(1, 3) ** n * Fraction(3, 5) ** nd
            trace_checks += 1
            zero_length_checks += n == 0
            revisit_checks += len(set(path[:-1])) < len(path[:-1])
            y = path[-1]
            # Each prefix can be made stopped by choosing only its endpoint
            # as T when it has not appeared earlier. Longer prefixes are also
            # checked, yielding a stronger check of the trace invariants.
            for bond in original_bonds - consumed:
                if y not in bond:
                    continue
                o = next(iter(bond - {y}))
                assert bond in current_bonds
                assert status[y] in "UD"
                assert degree(current_bonds, y) <= (3 if status[y] == "U" else 1)
                after_status = list(status)
                after_status[y] = "D" if status[y] == "U" else "X"
                after_kept = {x: neighbours.copy() for x, neighbours in kept.items()}
                after_kept[y].discard(o)
                after_kept[o].discard(y)
                visit(
                    path + [o], after_status, after_kept, consumed | {bond},
                    coefficient * (Fraction(1, 3) if status[y] == "U" else Fraction(1, 5)),
                    nd + (status[y] == "D"),
                )

        for start, s in enumerate(status_values):
            if s == "X" or degree(original_bonds, start) > (3 if s == "U" else 1):
                continue
            visit([start], list(status_values), original_kept, set(), Fraction(1), 0)

results = {
    "site_moment_numerical_cases": moment_checks,
    "analytic_numerical_inequalities": analytic_checks,
    "valid_five_vertex_network_configurations": valid_networks,
    "exact_fraction_trace_prefix_checks": trace_checks,
    "prefixes_with_a_repeated_departure": revisit_checks,
    "zero_length_trace_checks": zero_length_checks,
    "limitations": "Numerical moment/analytic samples and exhaustive finite graph checks are supporting evidence, not general proofs. The covered partition integral was audited directly against the paper, without enumerating global spin configurations."
}
Path(__file__).with_name("checks-result.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
