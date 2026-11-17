"""Diagnostic tests only: no Lean proofs and no repository writes."""

import itertools
import json
import math
import random
from fractions import Fraction
from pathlib import Path

rng = random.Random(6006)
phi = (1 + math.sqrt(5)) / 2
radius = math.sqrt(phi + 2)
atoms = [
    tuple(t / radius for t in v)
    for a, b in itertools.product((-1, 1), repeat=2)
    for v in ((0, a, b * phi), (a, b * phi, 0), (b * phi, 0, a))
]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def site(status, f):
    return sum(f(a) for a in atoms) / (12 if status == "U" else 20) + (
        0 if status == "U" else 2 * f((0, 0, 0)) / 5
    )


local_tests = 0
for status, max_degree, coefficient in (("U", 3, 1 / 3), ("D", 1, 1 / 5)):
    for degree in range(max_degree + 1):
        for _ in range(60):
            a = [rng.uniform(-2, 2) for _ in range(3)]
            fields = [[rng.uniform(-2, 2) for _ in range(3)] for _ in range(degree)]
            lhs = site(status, lambda z: dot(a, z) * math.prod(1 + dot(z, u) for u in fields))
            rhs = coefficient * sum(
                dot(a, u) * (site("D", lambda z: math.prod(
                    1 + dot(z, t) for j, t in enumerate(fields) if j != i
                )) if status == "U" else 1)
                for i, u in enumerate(fields)
            )
            assert math.isclose(lhs, rhs, abs_tol=2e-12, rel_tol=2e-12), (status, degree, lhs, rhs)
            local_tests += 1
assert math.isclose(site("U", lambda a: dot(a, a)), 1, abs_tol=1e-14)
assert math.isclose(site("D", lambda a: dot(a, a)), 3 / 5, abs_tol=1e-14)

exposure_tests = 0
for n in range(13):
    for _ in range(200):
        b = [math.exp(rng.uniform(-7, 7)) for _ in range(n)]
        c = [math.exp(rng.uniform(-7, 0)) for _ in range(n)]
        x = [max(1, t) * math.exp(rng.uniform(0, 0.5)) for t in b]
        lhs = abs(math.prod(b) - math.prod(c))
        rhs = sum(abs(math.log(c[i]) - math.log(b[i])) * math.prod(x[: i + 1]) for i in range(n))
        assert lhs <= rhs + 1e-10 * max(1, lhs)
        exposure_tests += 1

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
volume = set(itertools.product(range(-3, 4), repeat=2))
protected = {p for p in volume if max(map(abs, p)) >= 2}


def adjacent(p):
    return {(p[0] + dx, p[1] + dy) for dx, dy in steps}


legs = {p: len(adjacent(p) - volume) for p in volume}


def edge(p, q):
    return tuple(sorted((p, q)))


def neighbours(edges, p):
    return {q if p == r else r for r, q in edges if p in (r, q)}


trail_tests = 0
prefix_tests = 0
terminal_d_tests = 0
for _ in range(250):
    status = {p: ("U" if p in protected else rng.choice(("U", "U", "D", "X"))) for p in volume}
    edges = {edge(p, q) for p in volume for q in adjacent(p) & volume
             if p < q and status[p] != "X" and status[q] != "X"
             and (p not in protected or q not in protected) and rng.random() < 0.5}
    for p in sorted(volume):
        while status[p] == "D" and len(neighbours(edges, p)) > 2:
            edges.remove(edge(p, rng.choice(sorted(neighbours(edges, p)))))
    starts = [p for p in sorted(volume - protected) if status[p] != "X"
              and len(neighbours(edges, p)) <= (3 if status[p] == "U" else 1)]
    targets = [p for p in sorted(volume) if status[p] != "X" and (
        len(neighbours(edges, p)) + legs[p] <= 3 if status[p] == "U"
        else len(neighbours(edges, p)) <= 1)]
    if not starts or len(targets) < 2:
        continue
    for _ in range(24):
        u = rng.choice(starts)
        v = rng.choice([p for p in targets if p != u])
        current, st, remaining = u, status.copy(), edges.copy()
        used, coefficient, nd, n = set(), Fraction(1), 0, 0
        while True:
            prefix_tests += 1
            for p in volume:
                if st[p] == "X":
                    continue
                assert len(neighbours(remaining, p)) + legs[p] + (p == current) + (p == v) <= 4
                assert p not in protected or st[p] == "U"
                assert st[p] != "D" or len(neighbours(remaining, p)) <= 2
            assert coefficient == Fraction(1, 3) ** n * Fraction(3, 5) ** nd
            if current in protected or current == v:
                assert n <= len(edges)
                if current == v:
                    assert st[v] == status[v]
                    if st[v] == "D":
                        assert not neighbours(remaining, v) and legs[v] == 0
                        terminal_d_tests += 1
                trail_tests += 1
                break
            candidates = sorted(q for q in neighbours(edges, current) if edge(current, q) not in used)
            assert st[current] in ("U", "D")
            assert len(neighbours(remaining, current)) <= (3 if st[current] == "U" else 1)
            assert set(candidates) == neighbours(remaining, current)
            if not candidates:
                break
            q = rng.choice(candidates)
            chosen = edge(current, q)
            used.add(chosen)
            remaining.remove(chosen)
            if st[current] == "U":
                st[current] = "D"
                coefficient *= Fraction(1, 3)
            else:
                assert not neighbours(remaining, current)
                st[current] = "X"
                coefficient *= Fraction(1, 5)
                nd += 1
            assert edges - used == remaining
            current = q
            n += 1

result = {
    "seed": 6006,
    "site_identity_numerical_checks": local_tests,
    "terminal_norm_means": {"U": 1, "D": "3/5"},
    "product_exposure_numerical_checks": exposure_tests,
    "random_lattice_networks": 250,
    "sampled_stopped_trails": trail_tests,
    "prefix_invariant_checks": prefix_tests,
    "sampled_D_target_terminal_checks": terminal_d_tests,
    "result": "PASS",
    "limits": "Diagnostic sampling, not formal proofs; no attempt to verify H1 or H2 globally."
}
Path(__file__).with_name("checks.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
