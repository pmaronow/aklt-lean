"""Exact finite sanity checks for Lane B; these do not replace the proofs.

Uses one Python process, integer fourth roots and rational arithmetic only.
The geometry samples use actual admissible scales, not a rescaled lattice.
"""

from collections import Counter, defaultdict, deque
from fractions import Fraction
from math import isqrt
from pathlib import Path
import re


NN = ((1, 0), (-1, 0), (0, 1), (0, -1))
STAR = tuple((x, y) for x in (-1, 0, 1) for y in (-1, 0, 1) if x or y)


def root4(n):
    return isqrt(isqrt(n))


def connected(points, steps):
    if not points:
        return False
    seen = {next(iter(points))}
    todo = deque(seen)
    while todo:
        x, y = todo.popleft()
        for dx, dy in steps:
            q = (x + dx, y + dy)
            if q in points and q not in seen:
                seen.add(q)
                todo.append(q)
    return len(seen) == len(points)


def complement_connected(points):
    """Exact NN connectivity in a padded rectangle, compressed into row runs.

    The padding is entirely outside the set. Its connected outer frame
    identifies all connections through the infinite exterior.
    """
    left = min(x for x, _ in points) - 1
    right = max(x for x, _ in points) + 1
    bottom = min(y for _, y in points) - 1
    top = max(y for _, y in points) + 1
    rows = defaultdict(list)
    for x, y in points:
        rows[y].append(x)
    parents = []

    def find(i):
        while parents[i] != i:
            parents[i] = parents[parents[i]]
            i = parents[i]
        return i

    prev = []
    for y in range(bottom, top + 1):
        intervals = []
        start = left
        for x in sorted(rows[y]):
            if start < x:
                intervals.append((start, x - 1))
            start = x + 1
        if start <= right:
            intervals.append((start, right))
        current = []
        for lo, hi in intervals:
            index = len(parents)
            parents.append(index)
            current.append((lo, hi, index))
            for old_lo, old_hi, old_index in prev:
                if max(lo, old_lo) <= min(hi, old_hi):
                    parents[find(index)] = find(old_index)
        prev = current
    return len({find(i) for i in range(len(parents))}) == 1


def topology_checks():
    box = [(x, y) for x in range(3) for y in range(3)]
    frame = {(x, y) for x in range(-1, 4) for y in range(-1, 4)}
    accepted = 0
    all_star = 0
    for mask in range(1, 1 << len(box)):
        a = {box[i] for i in range(len(box)) if mask >> i & 1}
        if not connected(a, STAR):
            continue
        all_star += 1
        thick_a = {(x + dx, y + dy) for x, y in a for dx, dy in ((0, 0),) + NN}
        assert connected(thick_a, NN)
        if not connected(frame - a, STAR):
            continue
        raw = {(x + dx, y + dy) for x, y in a for dx, dy in STAR} - a
        thick = {(x + dx, y + dy) for x, y in raw for dx, dy in ((0, 0),) + NN}
        assert raw and connected(raw, STAR)
        assert connected(thick, NN)
        accepted += 1
    print(f"Topology: all 511 nonempty subsets of 3x3; {accepted} satisfy both hypotheses.")
    print(f"Crosses: all {all_star} star-connected subsets of 3x3 checked.")


def segments(y, radius, clip):
    """Boundary of the square centred at y, intersected with [-clip,clip]^2.

    Segment tuple: varying coordinate index, fixed coordinate, low, high.
    """
    result = []
    for varying in (0, 1):
        fixed = 1 - varying
        lo = max(-clip, y[varying] - radius)
        hi = min(clip, y[varying] + radius)
        if lo > hi:
            continue
        for q in (y[fixed] - radius, y[fixed] + radius):
            if -clip <= q <= clip:
                result.append((varying, q, lo, hi))
    return result


def seg_points(segs):
    for varying, fixed, lo, hi in segs:
        for v in range(lo, hi + 1):
            yield (v, fixed) if varying == 0 else (fixed, v)


def interval_gap(x, lo, hi):
    return max(lo - x, 0, x - hi)


def distance_to_segments(p, segs, metric):
    result = []
    for varying, fixed, lo, hi in segs:
        gaps = (abs(p[1 - varying] - fixed), interval_gap(p[varying], lo, hi))
        result.append(sum(gaps) if metric == 1 else max(gaps))
    return min(result) if result else 10**100


def shell_checks(u, y):
    s_floor = root4(u)
    corners = [(x * u, z * u) for x in (-1, 1) for z in (-1, 1)]
    exceptional = set()
    for i in range(2, s_floor + 2):
        k = root4(i**4 * u)
        d_segs = segments(y, k, u)
        dist = min(distance_to_segments(c, d_segs, 0) for c in corners)
        if (3 * dist)**4 < u:
            exceptional.add(i)
        assert k > root4((i - 1)**4 * u)
        if i in exceptional:
            continue
        near = set()
        for varying, fixed, lo, hi in d_segs:
            assert (3 * (u + 1 - abs(fixed)))**4 >= u
            assert u + 1 - abs(fixed) > 64
            for v in range(lo, min(hi, -u + 63) + 1):
                near.add((v, fixed) if varying == 0 else (fixed, v))
            for v in range(max(lo, u - 63), hi + 1):
                near.add((v, fixed) if varying == 0 else (fixed, v))
        assert len(near) <= 8 * 64
    assert len(exceptional) <= 1
    return exceptional


def geometry_check(u, i, offset, orientation=0):
    k = root4(i**4 * u)
    y = (-u + offset, -u - 1)
    if orientation:
        y = (y[1], y[0])
    exceptional = shell_checks(u, y)
    assert i not in exceptional
    assert i**4 <= u
    cap = root4(u) // 12
    inner_radius = root4((i - 1)**4 * u)

    def rho(p):
        return max(abs(p[0] - y[0]), abs(p[1] - y[1]))

    def height(p):
        return max(0, u + 1 - max(abs(p[0]), abs(p[1])))

    def in_u(p):
        t = abs(rho(p) - k)
        return (12 * t)**4 <= u and height(p) >= 32 + t

    tapered = set()
    for j in range(cap + 1):
        for radius in {k - j, k + j}:
            tapered.update(seg_points(segments(y, radius, u - 31 - j)))
    assert tapered and all(in_u(p) for p in tapered)
    assert connected(tapered, STAR)
    assert complement_connected(tapered)
    raw = {(x + dx, z + dz) for x, z in tapered for dx, dz in STAR} - tapered
    assert raw and connected(raw, STAR)
    thick = {(x + dx, z + dz) for x, z in raw for dx, dz in ((0, 0),) + NN}
    assert connected(thick, NN)

    b_segs = segments(y, k, u - 64)
    window = set(seg_points(b_segs))
    assert window <= tapered
    assert all((x + dx, z + dz) in tapered for x, z in window for dx, dz in NN)
    assert all(height(p) >= 32 and rho(p) >= inner_radius + 2 for p in tapered)

    inner_intervals = [(max(-u, y[j] - inner_radius), min(u, y[j] + inner_radius)) for j in (0, 1)]

    def depth(p):
        d_inner = sum(interval_gap(p[j], *inner_intervals[j]) for j in (0, 1))
        return min(height(p), d_inner, distance_to_segments(p, b_segs, 1))

    levels = Counter()
    raw_depths = Counter()
    thick_depths = Counter()
    for p in raw:
        t = abs(rho(p) - k)
        b = depth(p)
        assert b >= 14
        assert p not in window and height(p) > 0 and rho(p) > inner_radius
        if (12 * t)**4 <= u:
            assert 30 + t <= height(p) < 32 + t
            assert b >= max(t, 16) - 2
            levels[t] += 1
        else:
            assert (12 * (b + 1))**4 >= u
        raw_depths[b] += 1
    assert max(levels.values(), default=0) <= 48
    for p in thick:
        b = depth(p)
        assert b >= 13
        assert p not in window and height(p) > 0 and rho(p) > inner_radius
        thick_depths[b] += 1
    for q in (Fraction(1, 2), Fraction(9, 10)):
        raw_sum = sum(count * q**b for b, count in raw_depths.items())
        thick_sum = sum(count * q**b for b, count in thick_depths.items())
        assert thick_sum <= 5 / q * raw_sum
        if root4(u)**4 == u and root4(u) % 12 == 0:
            near = 48 * q**14 * (17 + 1 / (1 - q))
            assert raw_sum <= near + 4 * (2 * u + 1)**2 * q**(root4(u) // 12 - 1)
    assert all((x + dx, z + dz) in tapered or (x + dx, z + dz) in thick
               for x, z in tapered - window - thick for dx, dz in NN)
    print(f"Geometry: u={u}, i={i}, offset={offset}, axis={orientation}; "
          f"|U|={len(tapered)}, |X0|={len(raw)}, |X|={len(thick)}, "
          f"max near level={max(levels.values(), default=0)}, "
          f"min raw/thick depth={min(raw_depths)}/{min(thick_depths)}.")


def contract_checks():
    base = Path(__file__).resolve().parent
    plan = (base.parent / 'REV-PLAN' / 'PLAN.md').read_text()
    labels = ('l:shellgeom', 'l:cut', 'l:removal', 'd:thickcut', 'l:cutgeom',
              'l:Xconn', 't:cutMOS', 'l:boundaryconn', 'l:thicken')
    for label in labels:
        expected = plan.split('### ' + label + ' ', 1)[1].split('```latex\n', 1)[1].split('```', 1)[0].strip()
        path = base / ('app-topology.tex' if label in labels[-2:] else 'sec5-window.tex')
        text = path.read_text()
        match = re.search(r'\\begin\{(lemma|definition|theorem)\}\\label\{' + re.escape(label) + r'\}', text)
        end_tag = r'\end{' + match.group(1) + '}'
        actual = text[match.start():text.index(end_tag, match.start()) + len(end_tag)]
        if label == 'l:shellgeom':
            actual = actual.replace(r'For the same indices \(2\le i\le i_1\) outside \(I_0\), every side of' + '\n', 'Every side of ')
        assert re.sub(r'\s+', ' ', actual) == re.sub(r'\s+', ' ', expected), label
    all_text = '\n'.join((base / name).read_text() for name in ('sec5-window.tex', 'app-topology.tex'))
    defined = set(re.findall(r'\\label\{([^}]+)\}', all_text))
    references = set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', all_text))
    external = references - defined
    allowed = {'d:shells', 'd:framemodel', 'd:pinmodel', 'h:P', 'l:threeframes',
               'l:exact', 'l:finitefacts', 'l:moments', 'l:35', 'd:W'}
    assert external == allowed
    print('Contract: all 9 statements match, allowing only the recorded clearance-scope clarification.')
    print('External references:', ', '.join(sorted(external)))
    assert Fraction(1) - Fraction(6, 25) - Fraction(3, 15) == Fraction(14, 25) > Fraction(1, 2)
    assert Fraction(1) - Fraction(9, 50) == Fraction(41, 50) > Fraction(1, 2)
    assert 2 * Fraction(6, 15) == Fraction(4, 5) <= 1
    print('Removal: exact rational checks of 14/25, 41/50, and seed cost 4/5 passed.')


if __name__ == '__main__':
    contract_checks()
    topology_checks()
    u0 = 390**4
    k = root4(2**4 * u0)
    for offset in (-1, k - 31, k - 1, k + 130, 2 * k):
        geometry_check(u0, 2, offset)
    geometry_check(u0 + 1, 2, root4(2**4 * (u0 + 1)) + 132, orientation=1)
    u1 = 391**4 - 1
    geometry_check(u1, 3, 2 * root4(3**4 * u1))
    u2 = 396**4
    geometry_check(u2, 2, u2)  # middle of a side; exact rational far exponent
    print('PASS: all finite checks completed using one process.')
