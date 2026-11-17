"""Independent finite checks for REF-SA-B. Standard library, one process.

These checks supplement the universal arguments in report.md. They do not
replay the retained computer-assisted certificates.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, isqrt
import hashlib
import json
from pathlib import Path


class Q5:
    """Exact a + b sqrt(5), including exact order comparisons."""
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    @staticmethod
    def cast(x):
        return x if isinstance(x, Q5) else Q5(x)

    def __add__(self, x):
        x = self.cast(x)
        return Q5(self.a + x.a, self.b + x.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, x):
        return self + -self.cast(x)

    def __rsub__(self, x):
        return self.cast(x) + -self

    def __mul__(self, x):
        x = self.cast(x)
        return Q5(self.a * x.a + 5 * self.b * x.b,
                  self.a * x.b + self.b * x.a)

    __rmul__ = __mul__

    def __truediv__(self, x):
        x = self.cast(x)
        den = x.a * x.a - 5 * x.b * x.b
        return self * Q5(x.a / den, -x.b / den)

    def __pow__(self, n):
        ans = Q5(1)
        for _ in range(n):
            ans = ans * self
        return ans

    def sign(self):
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0 or (a > 0) == (b > 0):
            return (b > 0) - (b < 0)
        t = a * a - 5 * b * b
        return ((a > 0) - (a < 0)) * ((t > 0) - (t < 0))

    def __eq__(self, x):
        x = self.cast(x)
        return (self.a, self.b) == (x.a, x.b)

    def __lt__(self, x):
        return (self - x).sign() < 0

    def pair(self):
        return [str(self.a), str(self.b)]


def frames():
    phi = Q5(F(1, 2), F(1, 2))
    r2 = phi + 2
    vertices = []
    for p, q in product((-1, 1), repeat=2):
        vertices.extend([(Q5(0), Q5(p), q * phi),
                         (Q5(p), q * phi, Q5(0)),
                         (q * phi, Q5(0), Q5(p))])

    def rot(v):
        x, y, z = v
        return ((99 * x - 20 * y) / 101,
                (20 * x + 99 * y) / 101, z)

    ds = [vertices]
    ds.append([rot(v) for v in ds[-1]])
    ds.append([rot(v) for v in ds[-1]])
    b = Q5(F(5, 505), F(-1, 505))
    mins = []
    for i, j in ((0, 1), (0, 2), (1, 2)):
        weights = []
        for a, c in product(ds[i], ds[j]):
            dot = sum(x * y for x, y in zip(a, c)) / r2
            weights.extend((1 - dot, 1 + dot))
        assert not min(weights) < b
        mins.append(min(weights).pair())
    assert min(Q5(F(a), F(c)) for a, c in mins) == b
    moments = 0
    for degree in range(6):
        for p in range(degree + 1):
            for q in range(degree - p + 1):
                e = (p, q, degree - p - q)
                if any(t % 2 for t in e):
                    assert sum(a[0] ** e[0] * a[1] ** e[1] * a[2] ** e[2]
                               for a in vertices) == 0
                else:
                    num = 1
                    for t in e:
                        for odd in range(1, t, 2):
                            num *= odd
                    den = 1
                    for odd in range(1, degree + 2, 2):
                        den *= odd
                    value = sum(a[0] ** e[0] * a[1] ** e[1] * a[2] ** e[2]
                                for a in vertices) / (12 * r2 ** (degree // 2))
                    assert value == F(num, den)
                moments += 1
    return {"base_design_monomials_through_degree_5": moments,
            "cross_frame_pair_counts": [144, 144, 144],
            "cross_frame_minimum_weights_as_a_plus_b_sqrt5": mins}


def finite_size():
    count = 0
    for ell in range(2, 41):
        for u in ([1] * ell, [j * (ell + 1 - j) for j in range(1, ell + 1)]):
            r0 = sum(t * t for t in u)
            r1 = sum(u[j] * u[j + 1] for j in range(ell - 1))
            for period in range(ell + 1, 2 * ell + 4):
                a = u + [0] * (period - ell)
                r = [sum(a[j] * a[(j + k) % period] for j in range(period))
                     for k in range(period)]
                assert r[0] == r0 and r[1] == r[-1] == r1
                assert all(t <= r1 for t in r[1:])
                count += 1
        u = [j * (ell + 1 - j) for j in range(1, ell + 1)]
        s = sum(u)
        r0 = sum(t * t for t in u)
        r1 = sum(u[j] * u[j + 1] for j in range(ell - 1))
        assert F(ell * ell * r0 * (r0 - r1), s ** 4) == (
            F(36, 5) * F(ell * ell + 2 * ell + 2, (ell + 1) ** 2 * (ell + 2) ** 2))
        assert F(s ** 4, ell * ell * r0 * r1) == (
            F(25, 36) * F((ell + 1) ** 2 * (ell + 2) ** 2,
                         (ell - 1) * (ell + 3) * (ell * ell + 2 * ell + 2)))
    return {"circular_autocorrelations_checked": count,
            "ell_range_inclusive": [2, 40], "weighted_constants_checked": 39}


def edge(a, b):
    return tuple(sorted((a, b)))


def lifts():
    count = repeated = opposite = 0
    for ell in (2, 4, 6, 8):
        for L, N in product(range(ell + 1, ell + 4), repeat=2):
            sites = set(product(range(L), range(N)))
            p = lambda z: (z[0] % L, z[1] % N)
            eps = lambda z: (-1) ** ((z[0] + z[1]) % 2)
            cycle = lambda m, x: 2 if m % 2 and x == m - 1 else x % 2
            colour = lambda z: (cycle(L, z[0] % L) + cycle(N, z[1] % N)) % 3
            E = {edge(z, p((z[0] + dx, z[1] + dy)))
                 for z in sites for dx, dy in ((1, 0), (0, 1))}
            assert len(E) == 2 * L * N
            assert all(colour(a) != colour(b) for a, b in E)
            for start in sites:
                Q = {(start[0] + x, start[1] + y) for x, y in product(range(ell), repeat=2)}
                images = {p(z) for z in Q}
                assert len(images) == ell * ell
                internal, boundary, pins = Counter(), Counter(), {}
                for z in Q:
                    for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                        zz = (z[0] + dx, z[1] + dy)
                        assert eps(z) * eps(zz) == -1
                        assert colour(z) != colour(zz)
                        if zz in Q:
                            if z < zz:
                                internal[edge(p(z), p(zz))] += 1
                        else:
                            assert p(zz) not in images
                            boundary[edge(p(z), p(zz))] += 1
                            pins[zz] = eps(zz)
                assert internal == Counter({e: 1 for e in E if set(e) <= images})
                assert boundary == Counter({e: 1 for e in E if len(set(e) & images) == 1})
                by_image = {}
                for z, sign in pins.items():
                    by_image.setdefault(p(z), []).append(sign)
                if any(len(ss) > 1 for ss in by_image.values()):
                    repeated += 1
                if any(len(set(ss)) > 1 for ss in by_image.values()):
                    opposite += 1
                count += 1
    return {"translated_box_lifts_checked": count,
            "cases_with_repeated_exterior_images": repeated,
            "cases_with_oppositely_signed_repeated_pins": opposite,
            "ell_values": [2, 4, 6, 8], "periods": "ell+1 through ell+3, independently"}


def clamped_counts():
    count = 0
    min_t_ratio, max_t_ratio, max_s_ratio = None, F(0), F(0)
    for M in range(1, 9):
        L = 4 * M + 1
        lengths = (L, L + 1, L + 2, 2 * L, 2 * L + 3)
        counts = {}
        for N in lengths:
            for u in range(M, 2 * M + 1):
                l = 2 * u + 1
                starts = Counter(min(max(a, 1), N - l + 1) for a in range(1 - L, N + 1))
                for x in range(1, N + 1):
                    t = sum(w for b, w in starts.items() if b <= x <= b + l - 1)
                    h = sum(w for b, w in starts.items() if b - 1 <= x <= b + l)
                    counts[N, u, x] = (t, h)
        for N1, N2 in product(lengths, repeat=2):
            for x1, x2 in product(range(1, N1 + 1), range(1, N2 + 1)):
                T = S = 0
                for u in range(M, 2 * M + 1):
                    t1, h1 = counts[N1, u, x1]
                    t2, h2 = counts[N2, u, x2]
                    T += t1 * t2
                    S += h1 * h2 - t1 * t2
                assert 4 * M ** 3 <= T <= 1000 * M ** 3
                assert S <= 1000 * M ** 2
                rt, rs = F(T, M ** 3), F(S, M ** 2)
                min_t_ratio = rt if min_t_ratio is None else min(min_t_ratio, rt)
                max_t_ratio, max_s_ratio = max(max_t_ratio, rt), max(max_s_ratio, rs)
                count += 1
    return {"rectangle_site_cases": count, "M_range_inclusive": [1, 8],
            "min_T_over_M3": str(min_t_ratio), "max_T_over_M3": str(max_t_ratio),
            "max_S_over_M2": str(max_s_ratio)}


def scalar_bounds():
    lower4 = 1 - F(4, 6) * F(9, 25) - F(3, 15) * F(9, 25) ** 2
    assert lower4 >= F(734, 1000)
    assert 1 / F(82, 100) <= F(122, 100)
    assert 2 / F(734, 1000) <= F(273, 100)
    assert F(7776, 10000) / 15 / F(734, 1000) <= F(707, 10000)
    for n in range(44, 201):
        assert F(comb(n - 3, 20)) >= F(n, 2) ** 20 / factorial(20)
        for d in (F(1, 2), F(1, 3), F(1, 10), F(1, 100)):
            assert (1 - d) ** (n - 3) <= F(2 ** 20 * factorial(20), 1) / (d ** 20 * n ** 20)
    return {"four_neighbour_integral_lower_bound": str(lower4),
            "removal_decimal_upper_bounds": "all exact rational comparisons passed",
            "binomial_n_range_inclusive": [44, 200], "rational_tail_cases": 628}


def root4(n):
    return isqrt(isqrt(n))


def connected(points, diagonals=False):
    if not points:
        return False
    todo = set(points)
    q = [todo.pop()]
    offsets = [(a, b) for a, b in product((-1, 0, 1), repeat=2)
               if (a or b) and (diagonals or abs(a) + abs(b) == 1)]
    while q:
        x, y = q.pop()
        for dx, dy in offsets:
            p = (x + dx, y + dy)
            if p in todo:
                todo.remove(p)
                q.append(p)
    return not todo


def rect_distance(p, rect):
    l, r, b, t = rect
    return max(l - p[0], 0, p[0] - r) + max(b - p[1], 0, p[1] - t)


def shell_segments(k, rect):
    l, r, b, t = rect
    ans = []
    for x in (-k, k):
        if l <= x <= r and max(b, -k) <= min(t, k):
            ans.append((x, x, max(b, -k), min(t, k)))
    for y in (-k, k):
        if b <= y <= t and max(l, -k) <= min(r, k):
            ans.append((max(l, -k), min(r, k), y, y))
    return ans


def cut_geometry():
    tested = skipped = noninteger = 0
    max_ring_count, min_depth = 0, None
    # u is very large, but the cut occupies a thin annulus near y.
    for u in (132 ** 4 - 1, 132 ** 4, 132 ** 4 + 1):
        s_floor = root4(u)
        for i in (2, 3, 4):
            k = root4(i ** 4 * u)
            q = root4(u) // 12
            for offset in (None, -1, k - 46, k - 44, k - 43, k + 43, k + 44, k + 46):
                yyx = 0 if offset is None else -u + offset
                # Cell coordinates here are relative to the exterior site y.
                rect = (-u - yyx, u - yyx, 1, 2 * u + 1)
                corners = [(x, y) for x in (rect[0], rect[1]) for y in (rect[2], rect[3])]
                I0 = []
                for j in range(2, s_floor + 2):
                    segs = shell_segments(root4(j ** 4 * u), rect)
                    dist = min(max(max(seg[0] - z[0], 0, z[0] - seg[1]),
                                   max(seg[2] - z[1], 0, z[1] - seg[3]))
                               for seg in segs for z in corners)
                    if (3 * dist) ** 4 < u:
                        I0.append(j)
                assert len(I0) <= 1
                if i in I0:
                    skipped += 1
                    continue

                def h(c):
                    x, y = c
                    return max(0, u + 1 - max(abs(yyx + x), abs(-u - 1 + y)))

                U = set()
                R, r = k + q, k - q
                for y in range(max(1, rect[2]), min(R, rect[3]) + 1):
                    intervals = [(-R, R)] if y >= r else [(-R, -r), (r, R)]
                    for lo, hi in intervals:
                        for x in range(max(lo, rect[0]), min(hi, rect[1]) + 1):
                            t = abs(max(abs(x), abs(y)) - k)
                            if (12 * t) ** 4 <= u and h((x, y)) >= 10 + t:
                                U.add((x, y))
                assert connected(U, diagonals=True)
                assert all(not ((x + 1, y + 1) in U and (x + 1, y) not in U and (x, y + 1) not in U)
                           for x, y in U)
                assert all(not ((x + 1, y - 1) in U and (x + 1, y) not in U and (x, y - 1) not in U)
                           for x, y in U)
                bd = set()
                for x, y in U:
                    for dx, dy in product((-1, 0, 1), repeat=2):
                        z = (x + dx, y + dy)
                        if z not in U:
                            bd.add(z)
                X = set()
                for x, y in bd:
                    for dx, dy in product((0, 1), repeat=2):
                        p = (2 * x + dx, 2 * y + dy)
                        if any(((p[0] + ex) // 2, (p[1] + ey) // 2) in U
                               for ex, ey in product((-1, 0, 1), repeat=2)):
                            X.add(p)
                assert connected(X)
                Bsegs = shell_segments(k, (rect[0] + 20, rect[1] - 20,
                                           rect[2] + 20, rect[3] - 20))
                Bphys = [(2 * l, 2 * r + 1, 2 * b, 2 * t + 1) for l, r, b, t in Bsegs]
                notch = root4((i - 1) ** 4 * u)
                small = (max(rect[0], -notch), min(rect[1], notch),
                         max(rect[2], -notch), min(rect[3], notch))
                notch_phys = (2 * small[0], 2 * small[1] + 1,
                              2 * small[2], 2 * small[3] + 1)
                cell_ring = Counter()
                for c in {(p[0] // 2, p[1] // 2) for p in X}:
                    t = abs(max(abs(c[0]), abs(c[1])) - k)
                    if (12 * t) ** 4 <= u:
                        cell_ring[t] += 1
                assert all(number <= 48 for number in cell_ring.values())
                max_ring_count = max(max_ring_count, max(cell_ring.values(), default=0))
                for p in X:
                    outside = min(p[0] - 2 * rect[0] + 1, 2 * rect[1] + 2 - p[0],
                                  p[1] - 2 * rect[2] + 1, 2 * rect[3] + 2 - p[1])
                    b = min(outside, rect_distance(p, notch_phys),
                            *(rect_distance(p, seg) for seg in Bphys))
                    assert b >= 3
                    min_depth = b if min_depth is None else min(min_depth, b)
                    c = (p[0] // 2, p[1] // 2)
                    t = abs(max(abs(c[0]), abs(c[1])) - k)
                    if (12 * t) ** 4 <= u:
                        assert b >= 2 * max(t, 5) - 5
                    else:
                        assert (6 * (b + 3)) ** 4 >= u
                tested += 1
                noninteger += u != 132 ** 4
    return {"cuts_checked": tested, "exceptional_shells_skipped": skipped,
            "cuts_with_noninteger_fourth_root": noninteger,
            "largest_cells_per_short_ring": max_ring_count,
            "minimum_physical_graph_depth_on_X": min_depth,
            "u_values": [132 ** 4 - 1, 132 ** 4, 132 ** 4 + 1],
            "shell_indices": [2, 3, 4]}


if __name__ == "__main__":
    results = {}
    for name, fn in (("frames", frames), ("finite_size", finite_size),
                     ("lifts", lifts), ("clamped_counts", clamped_counts),
                     ("scalar_bounds", scalar_bounds), ("cut_geometry", cut_geometry)):
        results[name] = fn()
        print(name + ": PASS", flush=True)
    paths = [Path("/home/ubuntu/aklt/review/REF-SA/proof.tex"),
             Path("/home/ubuntu/aklt/review/REF-SA/mosproof.tex")]
    results["source_sha256"] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    Path(__file__).with_name("audit_results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
