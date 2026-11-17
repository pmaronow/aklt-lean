"""Finite sanity checks for TS_WIN_03; these are not Lean proofs.

Translation sources: AKLT/Blueprint/Win/Defs.lean:20-34,215-263 and
AKLT/Defs/Geometry.lean:8-14,39. Only Python's standard library is used.
Unordered pairs are normalized tuples; chains are sets with addition by XOR.
All generated edges have distinct endpoints, matching ChainNN/ChainStar.
"""

from collections import Counter, deque
from itertools import combinations, product
import json
from pathlib import Path


def edge(x, y):
    return tuple(sorted((x, y)))


def star(x, y):
    return max(abs(x[0] - y[0]), abs(x[1] - y[1])) == 1


def star_ball(x):
    return {(x[0] + dx, x[1] + dy) for dx, dy in product((-1, 0, 1), repeat=2)}


def triangle(x, y, z):
    return {edge(x, y), edge(y, z), edge(z, x)}


def plaquette(p):
    x, y = p
    a, b, c, d = p, (x + 1, y), (x + 1, y + 1), (x, y + 1)
    return {edge(a, b), edge(b, c), edge(c, d), edge(d, a)}


def even(c):
    degrees = Counter(x for e in c for x in e)
    return all(n % 2 == 0 for n in degrees.values())


def horizontal(c, i, j):
    return int(edge((i, j), (i + 1, j)) in c)


def tail(c, radius, i, j):
    return sum(horizontal(c, i, r) for r in range(-radius, radius + 1) if j < r) % 2


def components(vertices, adjacency):
    remaining = set(vertices)
    result = []
    while remaining:
        root = min(remaining)
        seen = {root}
        queue = deque([root])
        while queue:
            for y in adjacency[queue.popleft()]:
                if y not in seen:
                    seen.add(y)
                    queue.append(y)
        result.append(seen)
        remaining -= seen
    return result


def star_graph(vertices):
    return {x: (star_ball(x) - {x}) & vertices for x in vertices}


def path_chains(roots, adjacency):
    """Finite BFS paths, including a zero-edge path from a root to itself."""
    result = {}
    for root in roots:
        paths = {root: set()}
        queue = deque([root])
        while queue:
            x = queue.popleft()
            for y in adjacency[x]:
                if y not in paths:
                    paths[y] = paths[x] ^ {edge(x, y)}
                    queue.append(y)
        for y, chain in paths.items():
            result[root, y] = chain
    return result


def reconstruction_checks():
    count = 0
    zero_cases = 0
    translated_cases = 0
    for dx, dy in ((-5, -4), (-2, -1), (0, 0), (3, -2)):
        bases = [(dx + i, dy + j) for i, j in product(range(3), repeat=2)]
        # The nine plaquettes generate the entire cycle space of a 4x4 NN grid.
        for mask in range(1 << len(bases)):
            c = set()
            for bit, p in enumerate(bases):
                if mask & (1 << bit):
                    c ^= plaquette(p)
            assert even(c)
            assert all(sum(abs(x[k] - y[k]) for k in (0, 1)) == 1 for x, y in c)
            bound = max(1, abs(dx), abs(dx + 3), abs(dy), abs(dy + 3))
            for radius in (bound, bound + 2):
                assert all(abs(z[k]) <= radius for e in c for z in e for k in (0, 1))
                for i in range(-radius - 2, radius + 3):
                    assert sum(horizontal(c, i, r) for r in range(-radius, radius + 1)) % 2 == 0
                n = {
                    (i, j): tail(c, radius, i, j)
                    for i, j in product(range(-radius - 2, radius + 3), repeat=2)
                }
                # Outside this finite range the column is absent or the tail is
                # empty/the full zero column flux. Include two extra rows each side.
                assert all(
                    a == 0 or (-radius <= i <= radius and -radius <= j <= radius)
                    for (i, j), a in n.items()
                )
                minimal_p = {p for p, a in n.items() if a}
                rectangular_p = set(product(range(-radius, radius + 1), repeat=2))
                extra_p = minimal_p | {(radius + 5, -radius - 8), (-radius - 6, radius + 7)}
                for pset in (minimal_p, rectangular_p, extra_p):
                    reconstructed = set()
                    for p in pset:
                        if n.get(p, 0):
                            reconstructed ^= plaquette(p)
                    assert reconstructed == c, (dx, dy, mask, radius, pset)
                count += 1
                zero_cases += int(not c)
                translated_cases += int((dx, dy) != (0, 0))
    return {
        "cases": count,
        "zero_chain_cases": zero_cases,
        "translated_cases": translated_cases,
        "P_variants_per_case": 3,
        "failed_assertions": 0,
    }


def triangle_checks():
    count = 0
    for p in product(range(-3, 4), repeat=2):
        x, y = p
        a, b, c, d = p, (x + 1, y), (x + 1, y + 1), (x, y + 1)
        for t in ((a, b, c), (a, c, d)):
            assert all(star(v, w) for v, w in combinations(t, 2))
        assert triangle(a, b, c) ^ triangle(a, c, d) == plaquette(p)
        count += 1
    return {"translated_plaquettes": count, "failed_assertions": 0}


def boundary_checks():
    sites = list(product(range(3), repeat=2))
    collar = set(product(range(-1, 4), repeat=2))
    triangles = []
    for x, y in product(range(-1, 3), repeat=2):
        square = ((x, y), (x + 1, y), (x + 1, y + 1), (x, y + 1))
        triangles.extend(triangle(*t) for t in combinations(square, 3))
    counts = Counter()
    for mask in range(1 << len(sites)):
        a = {z for bit, z in enumerate(sites) if mask & (1 << bit)}
        balls = set().union(*(star_ball(z) for z in a)) if a else set()
        raw = balls - a
        cut = {edge(x, y) for x in a for y in star_ball(x) - a}
        assert bool(cut) == bool(a)
        outer = {e: next(z for z in e if z not in a) for e in cut}
        assert set(outer.values()) == raw
        assert all(sum(z in a for z in e) == 1 and star(*e) for e in cut)

        linked = {e: set() for e in cut}
        tri_cut = []
        for t in triangles:
            crossed = t & cut
            assert len(crossed) in (0, 2)
            tri_cut.append(crossed)
            if crossed:
                e, f = tuple(crossed)
                linked[e].add(f)
                linked[f].add(e)
                assert outer[e] == outer[f] or star(outer[e], outer[f])
                counts["linked_endpoint_checks"] += 1
        parts = components(cut, linked)
        for selected in parts:
            assert selected and selected <= cut
            assert all(linked[e] <= selected for e in selected)
            for crossed in tri_cut:
                assert len(crossed & selected) % 2 == 0
                counts["triangle_component_parity_checks"] += 1
        if len(parts) > 1:
            assert parts[0] and cut - parts[0]
            counts["nontrivial_separation_cases"] += 1
        if len(parts) == 1:
            assert raw and len(components(raw, star_graph(raw))) == 1
            counts["outer_endpoint_transfer_cases"] += 1

        interior_graph = star_graph(a)
        exterior = collar - a
        exterior_graph = star_graph(exterior)
        # The outside collar is connected and attaches to its full boundary.
        # Thus connectivity of this finite complement is equivalent to that
        # of the infinite complement for A contained in {0,1,2}^2.
        if a and len(components(a, interior_graph)) == 1 and len(components(exterior, exterior_graph)) == 1:
            inside_paths = path_chains(a, interior_graph)
            outside_paths = path_chains(raw, exterior_graph)
            for e, f in combinations(sorted(cut), 2):
                b1, b2 = outer[e], outer[f]
                a1 = next(z for z in e if z in a)
                a2 = next(z for z in f if z in a)
                c = inside_paths[a1, a2] ^ {f} ^ outside_paths[b2, b1] ^ {e}
                assert all(star(*g) for g in c)
                assert even(c)
                assert c & cut == {e, f}
                # Repeating an edge twice adds a backtrack and changes no chain.
                assert (c ^ {e} ^ {e}) == c
                counts["two_crossing_cycle_pairs"] += 1
                counts["shared_inside_endpoint_pairs"] += int(a1 == a2)
                counts["shared_outside_endpoint_pairs"] += int(b1 == b2)
            counts["two_connected_sides_cases"] += 1
        counts["A_subsets_checked"] += 1
    counts["failed_assertions"] = 0
    return dict(counts)


def single_summand_checks():
    universe = set(range(8))
    count = 0
    for mask in range(1 << len(universe)):
        selected = {e for e in universe if mask & (1 << e)}
        for e, f in product(selected, universe - selected):
            c = {g: int(g == e or g == f) for g in universe}
            assert sum(c[g] for g in selected) % 2 == 1
            count += 1
    return {"subset_and_distinct_crossing_choices": count, "failed_assertions": 0}


if __name__ == "__main__":
    checks = (
        ("plaquette_reconstruction", reconstruction_checks),
        ("plaquette_triangles", triangle_checks),
        ("cuts_links_and_paths", boundary_checks),
        ("two_crossing_parity", single_summand_checks),
    )
    result = {}
    for name, check in checks:
        result[name] = check()
        print(json.dumps({name: result[name]}, sort_keys=True), flush=True)
    Path(__file__).with_name("checks-results.json").write_text(json.dumps(result, indent=2) + "\n")
