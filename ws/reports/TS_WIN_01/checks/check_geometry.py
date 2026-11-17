"""Finite sanity checks for the truth sweep; no Lean proofs.

All root/floor and s/3 comparisons use integer fourth powers, with s=u^(1/4).
Shells are represented by their four clipped integer side intervals so that
large-volume threshold cases can be checked without enumerating the square.
"""

from collections import defaultdict
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random


def root4(n):
    return isqrt(isqrt(n))


def radius(u, i):
    n = i**4 * u
    k = root4(n)
    return k if i >= 0 else -k - (k**4 != n)


def dist(x, y):
    return max(abs(x[0] - y[0]), abs(x[1] - y[1]))


def corners(a, u):
    return set(product((a[0] - u, a[0] + u), (a[1] - u, a[1] + u)))


def inside(x, a, u):
    return dist(x, a) <= u


def boundary_depth(x, a, u):
    assert inside(x, a, u)
    return min(u + 1 - abs(x[axis] - a[axis]) for axis in (0, 1))


def ring(a, u):
    r = u + 1
    return {
        (a[0] + x, a[1] + y)
        for x, y in (
            [(e * r, t) for e in (-1, 1) for t in range(-r, r + 1)]
            + [(t, e * r) for e in (-1, 1) for t in range(-r, r + 1)]
        )
    }


def side_segments(a, y, u, k):
    if k < 0:
        return []
    out = []
    for axis, sign in product((0, 1), (-1, 1)):
        b = y[axis] + sign * k
        other = 1 - axis
        lo = max(a[other] - u, y[other] - k)
        hi = min(a[other] + u, y[other] + k)
        if a[axis] - u <= b <= a[axis] + u and lo <= hi:
            out.append((axis, b, lo, hi))
    return out


def segment_corner_distance(seg, c):
    axis, b, lo, hi = seg
    return max(abs(b - c[axis]), lo - c[1 - axis], c[1 - axis] - hi, 0)


def exceptional_corners(a, y, u, k):
    segs = side_segments(a, y, u, k)
    return {
        c
        for c in corners(a, u)
        if any((3 * segment_corner_distance(seg, c)) ** 4 < u for seg in segs)
    }


def clearance(a, y, u, k):
    for axis, b, lo, hi in side_segments(a, y, u, k):
        for delta in (-1, 1):
            gap = u + 1 - delta * (b - a[axis])
            assert gap >= 1
            if (3 * gap) ** 4 < u:
                return False
    return True


def merge_segments(segs):
    groups = defaultdict(list)
    for axis, b, lo, hi in segs:
        if lo <= hi:
            groups[axis, b].append((lo, hi))
    merged = []
    for (axis, b), intervals in groups.items():
        active = []
        for lo, hi in sorted(intervals):
            if active and lo <= active[-1][1] + 1:
                active[-1] = (active[-1][0], max(active[-1][1], hi))
            else:
                active.append((lo, hi))
        merged.extend((axis, b, lo, hi) for lo, hi in active)
    return merged


def union_card(segs):
    segs = merge_segments(segs)
    count = sum(hi - lo + 1 for _, _, lo, hi in segs)
    vertical = [s for s in segs if s[0] == 0]
    horizontal = [s for s in segs if s[0] == 1]
    for _, x, ylo, yhi in vertical:
        for _, y, xlo, xhi in horizontal:
            count -= xlo <= x <= xhi and ylo <= y <= yhi
    return count


def near_card(a, y, u, l, k):
    parts = []
    for axis, b, lo, hi in side_segments(a, y, u, k):
        other = 1 - axis
        if u + 1 - abs(b - a[axis]) <= l:
            parts.append((axis, b, lo, hi))
        else:
            parts.append((axis, b, lo, min(hi, a[other] - u + l - 1)))
            parts.append((axis, b, max(lo, a[other] + u - l + 1), hi))
    return union_card(parts)


def points(segs):
    out = set()
    for axis, b, lo, hi in segs:
        out.update((b, t) if axis == 0 else (t, b) for t in range(lo, hi + 1))
    return out


def symmetries(x):
    return [(x[0], x[1]), (x[1], -x[0]), (-x[0], -x[1]), (-x[1], x[0])]


def run():
    counts = defaultdict(int)
    rng = random.Random(20261116)
    # Validate interval and exterior-distance models against explicit finite sets.
    for u in range(5):
        a = (3, -5)
        square = set(product(range(a[0] - u, a[0] + u + 1), range(a[1] - u, a[1] + u + 1)))
        exterior_ring = ring(a, u)
        for x in square:
            assert boundary_depth(x, a, u) == min(dist(x, z) for z in exterior_ring)
            counts['explicit_exterior_distance'] += 1
        for y in product(range(a[0] - u - 2, a[0] + u + 3), range(a[1] - u - 2, a[1] + u + 3)):
            for k in range(-1, 2 * u + 4):
                direct = {x for x in square if dist(x, y) == k}
                segs = side_segments(a, y, u, k)
                assert direct == points(segs)
                assert len(direct) == union_card(segs)
                for l in range(u + 3):
                    assert near_card(a, y, u, l, k) == sum(boundary_depth(x, a, u) <= l for x in direct)
                    counts['explicit_shell_and_near_count'] += 1

    # Every exterior-ring seed for these small squares, including u=0.
    for a in ((0, 0), (3, -5)):
        for u in range(41):
            for y in ring(a, u):
                assert sum(dist(c, y) < u for c in corners(a, u)) <= 1
                counts['close_corner'] += 1

    # Localization has no exterior-seed assumption: test arbitrary interior and
    # exterior y at u>=16, where its numerical premise holds.
    for u in (16, 17, 18, 24, 31, 32):
        a = (2, -3)
        ycoords = [(a[0] + x, a[1] + y) for x, y in product(range(-u - 7, u + 8), repeat=2)]
        for y in ycoords:
            for i in range(2, root4(u) + 2):
                k = radius(u, i)
                for c in exceptional_corners(a, y, u, k):
                    assert dist(c, y) < u
                    assert (3 * abs(dist(c, y) - k)) ** 4 < u
                    counts['localization_corner_witness'] += 1
                counts['localization_configurations'] += 1

    # Exact fourth powers, their immediate integer neighbors, and l=64.
    volumes = [16**4, 16**4 + 1, 17**4 - 1, 17**4, 18**4 - 1,
               18**4, 18**4 + 1, 20**4 - 1, 20**4 + 1, 24**4,
               64**4, 390**4, 390**4 + 1, 391**4 - 1, 1000**4 + 1]
    nonvacuity_witness = None
    maximum_near_ratio = (0, 1)
    for u in volumes:
        n = root4(u)
        lmax = n // 6 - 1
        ls = sorted({1, lmax, max(1, lmax // 2)} | ({64} if lmax >= 64 else set()))
        for l in ls:
            assert max(16, 6 * (l + 1)) ** 4 <= u
        assert (3 * n) ** 4 > 16 * u
        counts['scale_floor_bound'] += 1
        for i in range(-100, 101):
            gap = radius(u, i + 1) - radius(u, i)
            assert gap > 0 and (3 * gap) ** 4 > 16 * u
            counts['radius_gap_negative_and_positive_indices'] += 1
        indices = list(range(2, n + 2)) if n <= 24 else sorted({2, 3, n // 2, n, n + 1} | {rng.randint(2, n + 1) for _ in range(12)})
        for i in indices:
            k = radius(u, i)
            assert k**4 > (i - 1) ** 4 * u
            counts['shell_inclusion_radius_bound'] += 1
            q = n // 3
            offsets = {-q - 2, -q, -1, 0, 1, q - 1, q, q + 1, q + 2}
            betas = {0, -u - 1, -u, u, u + 1, rng.randint(-u - 1, u + 1)}
            betas.update(t for edge, side, off in product((-u, u), (-1, 1), offsets)
                         if -u - 1 <= (t := edge + side * k + off) <= u + 1)
            for beta in betas:
                for j, y0 in enumerate(symmetries((beta, -u - 1))):
                    a = (7, -11) if j % 2 else (0, 0)
                    y = (y0[0] + a[0], y0[1] + a[1])
                    assert y in ring_for_seed(a, u, y)
                    exc = exceptional_corners(a, y, u, k)
                    pc = clearance(a, y, u, k)
                    assert pc or exc
                    counts['side_corner_witness'] += 1
                    for l in ls:
                        if pc:
                            near = near_card(a, y, u, l, k)
                            assert near <= 8 * l
                            if near * maximum_near_ratio[1] > maximum_near_ratio[0] * l:
                                maximum_near_ratio = (near, l)
                            counts['near_shell_count_with_clearance'] += 1
                    if u == 16**4 and i == 2 and beta == 2 * 16 - u and j == 0:
                        nonvacuity_witness = {'l': 1, 'a': a, 'y': y, 'u': u, 'i': i, 'clearance': pc, 'exceptional': bool(exc)}

        # Test the assembled exceptional count over the complete trial index set
        # for a few seeds on and near a corner.
        for beta in (0, -u - 1, -u, -u + 2 * n, u - 2 * n, u + 1):
            y = (beta, -u - 1)
            exceptional = [i for i in range(2, n + 2) if exceptional_corners((0, 0), y, u, radius(u, i))]
            assert len(exceptional) <= 1
            counts['exceptional_count_complete_trial_range'] += 1

    # The inclusion leaf permits much smaller u and arbitrarily large i.
    for u in (16, 17, 31, 81, 255, 256, 65535):
        for i in (2, 3, 4, 100, 10**6):
            assert radius(u, i) ** 4 > (i - 1) ** 4 * u
            counts['shell_inclusion_radius_bound'] += 1

    assert nonvacuity_witness and not nonvacuity_witness['clearance'] and nonvacuity_witness['exceptional']
    return {
        'result': 'PASS',
        'arithmetic': 'integer fourth roots and integer fourth-power comparisons; no floating point',
        'counts': dict(counts),
        'side_corner_nonvacuity_witness': nonvacuity_witness,
        'largest_observed_near_card_over_l': list(maximum_near_ratio),
        'scope': 'Finite sanity checks support the mathematical audit and are not proofs of universal statements.'
    }


def ring_for_seed(a, u, y):
    """Singleton membership check without constructing a huge exterior ring."""
    dx = max(abs(y[0] - a[0]) - u, 0)
    dy = max(abs(y[1] - a[1]) - u, 0)
    return {y} if max(dx, dy) == 1 else set()


if __name__ == '__main__':
    result = run()
    output = Path(__file__).with_name('geometry-results.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
