"""Finite counterexample searches for the eight leaves; this file contains no Lean proofs.

All shell cutoffs and radii are calculated with integer fourth powers, avoiding
floating-point approximations of sqrt(sqrt(u)). Chains are finite unordered edge
sets, with symmetric difference modelling their ZMod 2 coefficients.
"""

from collections import Counter, deque
from itertools import combinations, product
import json
from math import inf, isqrt
from pathlib import Path


HERE = Path(__file__).resolve().parent
COUNTS = Counter()
OFFSETS = tuple(product(range(-1, 2), repeat=2))


def sup_dist(x, y):
    return max(abs(x[0] - y[0]), abs(x[1] - y[1]))


def l1_dist(x, y):
    return abs(x[0] - y[0]) + abs(x[1] - y[1])


def rectangle(lo, hi):
    return set(product(range(lo, hi + 1), repeat=2))


def edge(x, y):
    # The two entries coincide for a Sym2 loop; endpoint membership counts it once.
    return tuple(sorted((x, y)))


def even(chain):
    degrees = Counter()
    for e in chain:
        degrees.update(set(e))
    return all(n % 2 == 0 for n in degrees.values())


def boxed(chain, radius):
    return all(abs(x) <= radius and abs(y) <= radius
               for e in chain for x, y in e)


def horizontal(chain, i, j):
    return int(edge((i, j), (i + 1, j)) in chain)


def flux(chain, radius, i):
    return sum(horizontal(chain, i, r)
               for r in range(-radius, radius + 1)) % 2


def tail(chain, radius, i, j):
    return sum(horizontal(chain, i, r)
               for r in range(-radius, radius + 1) if j < r) % 2


def check_shells():
    for a in ((0, 0), (3, -2)):
        for u in (*range(7), 16, 17):
            square = {(a[0] + x, a[1] + y)
                      for x, y in product(range(-u, u + 1), repeat=2)}
            offsets = (range(-u - 1, u + 2) if u < 7 else
                       (-u - 2, -u - 1, -u, 0, u, u + 1, u + 2))
            for dx, dy in product(offsets, repeat=2):
                y = (a[0] + dx, a[1] + dy)
                radii = {x: sup_dist(x, y) for x in square}
                for i in range(2, 9):
                    # r > (i-1) u^(1/4) iff r^4 > (i-1)^4 u, since r>=0, i>=2.
                    cutoff_fourth = (i - 1) ** 4 * u
                    far = {x for x in square if radii[x] ** 4 > cutoff_fourth}
                    shell_radius = isqrt(isqrt(cutoff_fourth))
                    for x in square - far:
                        if any((x[0] + ox, x[1] + oy) in far for ox, oy in OFFSETS):
                            assert radii[x] == shell_radius, (a, y, u, i, x)
                            COUNTS['predecessor_nontrivial_points'] += 1
                    COUNTS['shell_configurations'] += 1
                    if u >= 16:  # shellSpacing u >= 2, exactly.
                        distance = min((sup_dist(y, z) for z in far), default=inf)
                        assert distance > 1, (a, y, u, i)
                        COUNTS['seed_configurations'] += 1
                        COUNTS['seed_nonempty_far_volumes'] += bool(far)
                    COUNTS['empty_far_volumes'] += not far


def exact_depth(volume, x):
    # Enumerate complete l1 spheres, stopping at the first exterior site.
    for radius in range(len(volume) + 1):
        for dx in range(-radius, radius + 1):
            dy = radius - abs(dx)
            if (x[0] + dx, x[1] + dy) not in volume:
                return radius
            if (x[0] + dx, x[1] - dy) not in volume:
                return radius
    raise AssertionError('No exterior site found')


def check_depth_and_boundary():
    sites = sorted(rectangle(-1, 1))
    queries = sorted(rectangle(-2, 2))
    boundary_queries = sorted(rectangle(-3, 3))
    for mask in range(1 << len(sites)):
        volume = {x for k, x in enumerate(sites) if mask >> k & 1}
        depths = {x: exact_depth(volume, x) for x in queries}
        for x, depth in depths.items():
            assert isinstance(depth, int) and 0 <= depth < inf
            assert (depth == 0) == (x not in volume)
            for y in queries:
                assert depth <= l1_dist(x, y) + depths[y], (volume, x, y)
                COUNTS['depth_lipschitz_pairs'] += 1
        raw_boundary = {(x[0] + dx, x[1] + dy)
                        for x in volume for dx, dy in OFFSETS} - volume
        for z in boundary_queries:
            distance = min((sup_dist(z, x) for x in volume), default=inf)
            assert (z in raw_boundary) == (z not in volume and distance == 1)
            COUNTS['boundary_membership_queries'] += 1
        COUNTS['finite_volumes'] += 1


def all_even_chains(vertices, graph_edges):
    """Enumerate the whole cycle space of a finite connected graph."""
    adjacency = {x: [] for x in vertices}
    for x, y in graph_edges:
        adjacency[x].append(y)
        adjacency[y].append(x)
    root = min(vertices)
    parent = {root: None}
    tree = set()
    todo = deque((root,))
    while todo:
        x = todo.popleft()
        for y in adjacency[x]:
            if y not in parent:
                parent[y] = x
                tree.add(edge(x, y))
                todo.append(y)
    assert len(parent) == len(vertices)
    root_paths = {}
    for x in vertices:
        path = set()
        current = x
        while parent[current] is not None:
            path.add(edge(current, parent[current]))
            current = parent[current]
        root_paths[x] = path
    basis = [{e} ^ root_paths[e[0]] ^ root_paths[e[1]]
             for e in sorted(graph_edges - tree)]
    chains = [set()]
    for cycle in basis:
        chains.extend([c ^ cycle for c in chains])
    assert len(chains) == 1 << (len(graph_edges) - len(vertices) + 1)
    assert len({frozenset(c) for c in chains}) == len(chains)
    return chains


def check_chain_box(chain):
    radius = max([1] + [abs(coordinate) for e in chain for x in e for coordinate in x])
    assert radius >= 1 and boxed(chain, radius)
    COUNTS['chain_box_instances'] += 1


def check_diagonal_elimination():
    vertices = rectangle(-1, 1)
    graph_edges = {edge(x, y) for x, y in combinations(vertices, 2)
                   if sup_dist(x, y) == 1}
    for chain in all_even_chains(vertices, graph_edges):
        assert even(chain)
        correction = set()
        for p, q in chain:
            if l1_dist(p, q) == 2:
                middle = (q[0], p[1])
                assert all(sup_dist(x, y) == 1
                           for x, y in combinations((p, middle, q), 2))
                triangle = {edge(p, middle), edge(middle, q), edge(q, p)}
                assert sum(l1_dist(x, y) == 2 for x, y in triangle) == 1
                correction ^= triangle
        result = chain ^ correction
        assert all(l1_dist(x, y) == 1 for x, y in result)
        assert even(result)
        assert chain ^ result == correction
        check_chain_box(chain)
        check_chain_box(result)
        COUNTS['even_star_chains_eliminated'] += 1


def check_column_flux():
    vertices = rectangle(-2, 1)
    graph_edges = {edge(x, y) for x, y in combinations(vertices, 2)
                   if l1_dist(x, y) == 1}
    for chain in all_even_chains(vertices, graph_edges):
        assert even(chain)
        for radius in (2, 3):
            assert boxed(chain, radius)
            for i in range(-radius - 2, radius + 3):
                assert flux(chain, radius, i) == 0, (chain, radius, i)
                COUNTS['column_flux_queries'] += 1
        COUNTS['even_nn_chains'] += 1


def check_tail_support():
    radius = 1
    # Every even-cardinality row selection in each of the two horizontal columns.
    row_choices = [set(rows) for n in (0, 2)
                   for rows in combinations(range(-1, 2), n)]
    # These additional edges exercise the absence of NN/even premises in this leaf.
    extras = (
        edge((-1, -1), (-1, -1)),
        edge((1, 1), (1, 1)),
        edge((-1, -1), (0, 0)),
        edge((0, -1), (-1, 0)),
        edge((-1, 0), (1, 0)),
        edge((0, 0), (0, 1)),
    )
    support_box = rectangle(-radius, radius)
    for left_rows, right_rows in product(row_choices, repeat=2):
        base = {edge((i, r), (i + 1, r))
                for i, rows in ((-1, left_rows), (0, right_rows)) for r in rows}
        for mask in range(1 << len(extras)):
            chain = base | {e for k, e in enumerate(extras) if mask >> k & 1}
            assert boxed(chain, radius)
            assert all(flux(chain, radius, i) == 0 for i in range(-4, 5))
            for i, j in rectangle(-4, 4) - support_box:
                assert tail(chain, radius, i, j) == 0, (chain, i, j)
                COUNTS['tail_outside_box_queries'] += 1
            COUNTS['tail_chains_without_even_or_nn_assumption'] += 1
    check_chain_box(set())
    check_chain_box({edge((-100, 37), (400, -800)), edge((4, 4), (4, 4))})


def check_negative_controls():
    one_edge = {edge((0, 0), (1, 0))}
    assert not even(one_edge)
    assert flux(one_edge, 1, 0) == 1  # ColumnFlux needs its even premise.
    assert all(tail(one_edge, 1, 0, j) == 1 for j in (-2, -10, -100))
    # TailSupport needs zero column flux: otherwise it persists arbitrarily far down.
    assert sup_dist((1, 0), (0, 0)) == 1
    # With u=0,i=2,y=(1,0), farVolume((0,0),y,0,2)={(0,0)}.
    # Its seed distance is one; SeedSeparation's scale premise cannot simply be omitted.
    COUNTS['negative_controls'] += 3


if __name__ == '__main__':
    check_shells()
    check_depth_and_boundary()
    check_diagonal_elimination()
    check_column_flux()
    check_tail_support()
    check_negative_controls()
    result = {
        'status': 'PASS',
        'scope': 'Finite exact-arithmetic counterexample searches, not formal proofs.',
        'counts': dict(sorted(COUNTS.items())),
    }
    (HERE / 'small_case_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
