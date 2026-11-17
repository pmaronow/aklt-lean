"""Numerical checks of the paper's single-tip covering construction, not proofs."""
import itertools
import json
import math
import random

RNG = random.Random(20261116)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def norm(v):
    return math.sqrt(dot(v, v))


def unit():
    v = [RNG.gauss(0, 1) for _ in range(3)]
    r = norm(v)
    return [x / r for x in v]


phi = (1 + math.sqrt(5)) / 2
radius = math.sqrt(phi + 2)
ico = []
for a, b in itertools.product((-1, 1), repeat=2):
    ico.extend([[0, a / radius, b * phi / radius],
                [a / radius, b * phi / radius, 0],
                [b * phi / radius, 0, a / radius]])


def mass_and_mean(status, fields):
    atoms = [(v, 1 / 12 if status == 'U' else 1 / 20) for v in ico]
    if status == 'D':
        atoms.append(([0, 0, 0], 2 / 5))
    weights = [p * math.prod(1 + dot(v, b) for b in fields) for v, p in atoms]
    mass = sum(weights)
    mean = [sum(w * v[k] for w, (v, _) in zip(weights, atoms)) / mass for k in range(3)]
    return mass, mean


def fields_for_mean(v):
    r = norm(v)
    e = [z / r for z in v] if r > 1e-15 else [1, 0, 0]
    axis = [1 if i == min(range(3), key=lambda j: abs(e[j])) else 0 for i in range(3)]
    transverse = [a - dot(axis, e) * b for a, b in zip(axis, e)]
    length = norm(transverse)
    transverse = [z / length for z in transverse]
    # The path in sec2-moments.tex:268-288 has axial mean
    # (2*x^2 + 5*x + 2) / (5*(x^2 + x + 1)), for -1/2 <= x <= 1.
    lo, hi = -0.5, 1.0
    for _ in range(100):
        x = (lo + hi) / 2
        mean = (2 * x * x + 5 * x + 2) / (5 * (x * x + x + 1))
        if mean < r:
            lo = x
        else:
            hi = x
    x = (lo + hi) / 2
    s = math.sqrt(1 - x * x)
    return [e, [x * a + s * b for a, b in zip(e, transverse)],
            [x * a - s * b for a, b in zip(e, transverse)]]


def main():
    max_error, cases = 0.0, 0
    min_actual_mass, min_cover_mass = math.inf, math.inf
    max_mean_norm = 0.0
    for status in ('U', 'D'):
        for k in range(4):
            for sample in range(125):
                fields = [[RNG.random() * z for z in unit()] for _ in range(k)]
                if sample == 0:
                    fields = [[1, 0, 0] for _ in range(k)]
                A, b = mass_and_mean(status, fields)
                assert A > 0 and norm(b) <= 3 / 5 + 2e-14
                max_mean_norm = max(max_mean_norm, norm(b))
                min_actual_mass = min(min_actual_mass, A)
                for internal_present in (False, True):
                    desired = b if internal_present else [0, 0, 0]
                    cover_fields = fields_for_mean(desired)
                    assert all(abs(norm(v) - 1) < 1e-13 for v in cover_fields)
                    Aprime, bprime = mass_and_mean('U', cover_fields)
                    min_cover_mass = min(min_cover_mass, Aprime)
                    for _ in range(3):
                        v = unit()
                        actual = A * (1 + dot(b, v)) if internal_present else A
                        cover = Aprime * (1 + dot(bprime, v))
                        max_error = max(max_error, abs(actual - A / Aprime * cover))
                    cases += 1
    assert max_error < 2e-12
    print(json.dumps({'tip_replacements': cases, 'max_absolute_factor_error': max_error,
                      'max_actual_mean_norm': max_mean_norm,
                      'minimum_actual_normalizer': min_actual_mass,
                      'minimum_cover_normalizer': min_cover_mass}, indent=2))


if __name__ == '__main__':
    main()
