"""Finite sanity checks of the mathematical models; no Lean proofs."""
import json
from fractions import Fraction as Q
from itertools import product
from math import isqrt
from pathlib import Path


def fourth_root(n):
    return isqrt(isqrt(n))


counts = {"real_arithmetic_samples": 0, "admissible_geometries": 0,
          "taper_sites": 0, "raw_sites": 0, "near_raw_sites": 0,
          "far_raw_sites": 0, "window_sites": 0}

# Set b to the smallest value allowed by the obstruction hypothesis.
# Fractional t and h are intentional: this leaf quantifies over reals.
for s in map(Q, [390, Q(2731, 7), 391, 396, 1000]):
    T = s / 12
    offsets = {Q(0), Q(15), Q(16), Q(33, 2), Q(17), T-1, T,
               T+Q(1, 7), T+Q(1, 2), T+1}
    for t in offsets:
        if not 0 <= t <= T+1:
            continue
        heights = ([30+t, 31+t, 32+t-Q(1, 1000)] if t <= T
                   else [30+t, 31+t, 1000+t])
        for h in heights:
            b = min(max(t, 65-h), h, s-1-t)
            assert 14 <= b
            assert t > T or max(t, 16)-2 <= b
            assert t <= T or T-1 <= b
            counts["real_arithmetic_samples"] += 1


def sup_dist(x, y):
    return max(abs(x[0]-y[0]), abs(x[1]-y[1]))


def depth(a, u, x):
    return max(0, u+1-sup_dist(x, a))


def segments(a, m, y, r):
    """Four shell sides clipped to the closed square of radius m."""
    result = []
    for axis, sign in product(range(2), [-1, 1]):
        other = 1-axis
        fixed = y[axis]+sign*r
        lo = max(y[other]-r, a[other]-m)
        hi = min(y[other]+r, a[other]+m)
        if a[axis]-m <= fixed <= a[axis]+m and lo <= hi:
            result.append((axis, fixed, lo, hi))
    return result


def segment_samples(segs):
    result = set()
    for axis, fixed, lo, hi in segs:
        for v in {lo, hi, (lo+hi)//2}:
            point = [0, 0]
            point[axis], point[1-axis] = fixed, v
            result.add(tuple(point))
    return result


def segment_distance(x, seg, metric):
    axis, fixed, lo, hi = seg
    d1 = abs(x[axis]-fixed)
    d2 = max(lo-x[1-axis], 0, x[1-axis]-hi)
    return max(d1, d2) if metric == "sup" else d1+d2


nn = [(1, 0), (-1, 0), (0, 1), (0, -1)]
star = list(product([-1, 0, 1], repeat=2))
a = (17, -23)
for u in [390**4, 390**4+1, 391**4-1, 396**4]:
    floor_s = fourth_root(u)
    floor_T = floor_s//12
    for i in [2, 3, floor_s]:
        k = fourth_root(i**4*u)
        q = fourth_root((i-1)**4*u)
        betas = {-u-1, -u, -u+k//2, -u+k, -u+2*k, 0,
                 u-2*k, u-k, u, u+1}
        for beta in betas:
            y = (a[0]+beta, a[1]-u-1)
            shell = segments(a, u, y, k)
            corners = product([a[0]-u, a[0]+u], [a[1]-u, a[1]+u])
            corner_gap = min(segment_distance(c, seg, "sup")
                             for c in corners for seg in shell)
            # Strict exception test without evaluating the real fourth root.
            if (3*corner_gap)**4 < u:
                continue
            counts["admissible_geometries"] += 1

            def offset(x):
                return abs(sup_dist(x, y)-k)

            def in_taper(x):
                return offset(x) <= floor_T and offset(x)+32 <= depth(a, u, x)

            def in_far(x):
                return sup_dist(x, a) <= u and q < sup_dist(x, y)

            def in_window(x):
                return sup_dist(x, y) == k and depth(a, u, x) >= 65

            B = segments(a, u-64, y, k)
            assert B

            def exact_boundary_depth(x):
                # G^c is the union of the square exterior, the inner closed
                # rho-ball (intersecting C is unnecessary after taking union),
                # and the four clipped window segments. All distances are l1.
                inner = sum(max(abs(x[j]-y[j])-q, 0) for j in range(2))
                window = min(segment_distance(x, seg, "l1") for seg in B)
                return min(depth(a, u, x), inner, window)

            V = set()
            deltas = {-floor_T, -floor_T+1, -17, -1, 0, 1, 17,
                      floor_T-1, floor_T}
            for delta in deltas:
                if abs(delta) <= floor_T:
                    V.update(segment_samples(segments(a, u-31-abs(delta), y, k+delta)))
            raw = set()
            for v in V:
                assert in_taper(v)
                assert in_far(v)
                counts["taper_sites"] += 1
                for d in nn:
                    assert in_far((v[0]+d[0], v[1]+d[1]))
                if offset(v):
                    rho = sup_dist(v, y)
                    w = list(v)
                    axes = [j for j in range(2) if abs(v[j]-y[j]) == rho]
                    if rho > k:
                        for j in axes:
                            w[j] -= 1 if v[j] > y[j] else -1
                    else:
                        j = axes[0]
                        w[j] += 1 if v[j] >= y[j] else -1
                    w = tuple(w)
                    assert sup_dist(v, w) == 1 and in_taper(w)
                    assert offset(w) == offset(v)-1
                for d in star:
                    x = (v[0]+d[0], v[1]+d[1])
                    if not in_taper(x):
                        raw.add(x)
            for x in raw:
                t, h = offset(x), depth(a, u, x)
                assert t <= floor_T+1 and h >= 30+t
                assert in_far(x) and not in_window(x)
                b = exact_boundary_depth(x)
                assert min(max(t, 65-h), h) <= b or u <= (b+1+t)**4
                assert 14 <= b
                if t <= floor_T:
                    assert h < 32+t and max(t, 16)-2 <= b
                    counts["near_raw_sites"] += 1
                else:
                    assert u <= (12*(b+1))**4
                    counts["far_raw_sites"] += 1
                counts["raw_sites"] += 1
            for v in segment_samples(B):
                assert in_window(v) and in_taper(v)
                for d in nn:
                    assert in_taper((v[0]+d[0], v[1]+d[1]))
                counts["window_sites"] += 1

assert counts["near_raw_sites"] and counts["far_raw_sites"]
result = {"result": "PASS", "counts": counts,
          "scope": "Exact rational samples and exact lattice samples, not exhaustive or kernel-checked proofs."}
Path(__file__).with_name("checks.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
