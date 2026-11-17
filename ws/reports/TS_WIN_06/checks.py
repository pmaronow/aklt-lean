"""Exact finite spot checks for the truth sweep; these are not Lean proofs."""

from fractions import Fraction
from itertools import product


def neighbours(z):
    x, y = z
    return {(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)}


def sphere(c, r):
    return {
        (c[0] + dx, c[1] + dy)
        for dx in range(-r, r + 1)
        for dy in range(-r, r + 1)
        if max(abs(dx), abs(dy)) == r
    }


intersection_cases = 0
max_intersection = 0
for y in product(range(-5, 6), repeat=2):
    for r, radius in product(range(1, 6), repeat=2):
        if any(
            y[axis] + eps * r == delta * radius
            for axis, eps, delta in product(range(2), (-1, 1), (-1, 1))
        ):
            continue
        count = len(sphere(y, r) & sphere((0, 0), radius))
        assert count <= 8
        intersection_cases += 1
        max_intersection = max(max_intersection, count)

print(f"Square intersections: {intersection_cases} admissible cases; maximum {max_intersection} <= 8.")

sites = tuple(product(range(-1, 2), repeat=2))
degree_cases = 0
for states in product(range(3), repeat=len(sites)):
    original = {z for z, state in zip(sites, states) if state != 0}
    active = {z for z, state in zip(sites, states) if state == 2}
    indices = {z: j for j, z in enumerate(sorted(active))}
    bonds = {
        (z, w)
        for z in active
        for w in ((z[0] + 1, z[1]), (z[0], z[1] + 1))
        if w in active
    }
    reindexed = {tuple(sorted((indices[z], indices[w]))) for z, w in bonds}
    assert len(reindexed) == len(bonds)
    assert all(j < k for j, k in reindexed)
    for z in active:
        incident = sum(z in edge for edge in bonds)
        pins = len(neighbours(z) - original)
        assert incident + pins <= 4
    degree_cases += 1

assert len(tuple(product(range(12), repeat=0))) == 1
print(f"Original/surviving lattice networks: {degree_cases} patterns; ordered bonds and degree <= 4 passed.")
print("Empty spin domain: one configuration, with empty product one.")

signed_cases = 0
signed_inequalities = 0
for spacing in (390, 396, 480):
    u = spacing**4
    for index in (2, 3, spacing):
        k = index * spacing
        values = {0, u, -u}
        for q in (u - k, u + 1 - k, u + 1 - k - spacing // 3, u + 1 - k + spacing // 3):
            values.update((q, -q))
        for other in values:
            if abs(other) > u + 1:
                continue
            y = (u + 1, other)
            clearance = True
            corner_distance = None
            for axis, eps in product(range(2), (-1, 1)):
                fixed = y[axis] + eps * k
                lo = max(-u, y[1 - axis] - k)
                hi = min(u, y[1 - axis] + k)
                if not (-u <= fixed <= u and lo <= hi):
                    continue
                clearance &= Fraction(u + 1 - abs(fixed)) >= Fraction(spacing, 3)
                for corner in product((-u, u), repeat=2):
                    dist = max(abs(corner[axis] - fixed), lo - corner[1 - axis], corner[1 - axis] - hi, 0)
                    corner_distance = dist if corner_distance is None else min(corner_distance, dist)
            nonexceptional = corner_distance is None or Fraction(corner_distance) >= Fraction(spacing, 3)
            if not (clearance and nonexceptional):
                continue
            signed_cases += 1
            for j in range(spacing // 12 + 1):
                for h, r, axis, eps, delta in product((30 + j, 31 + j), (k - j, k + j), range(2), (-1, 1), (-1, 1)):
                    assert y[axis] + eps * r != delta * (u + 1 - h)
                    signed_inequalities += 1

assert signed_cases > 0
print(f"Signed side exclusion: {signed_cases} admissible large-scale examples; {signed_inequalities} exact coordinate inequalities passed.")
