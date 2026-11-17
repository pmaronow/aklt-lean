"""Bounded numerical/combinatorial checks; no Lean proofs are generated."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations, product
import json
import math
import random

rng = random.Random(1016)
DIRS = ((1, 0), (0, 1), (-1, 0), (0, -1))
C = (0, 0)
U = (-1, 0)
TARGET = {'B': (1, 0), 'C': (0, 1)}

def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def dist(a, b): return abs(a[0]-b[0]) + abs(a[1]-b[1])
def neigh(a): return {add(a, b) for b in DIRS}
def bond(a, b): return frozenset((a, b))
def pairtype(p):
    a, b = tuple(p)
    assert dist(a, b) == 2
    return 'B' if a[0] == b[0] or a[1] == b[1] else 'C'
def protected(g):
    return {a for a in g if any(add(a, b) not in g for b in product(range(-2, 3), repeat=2) if abs(b[0])+abs(b[1]) <= 2)}

def geometry_checks():
    triple_count = 0
    for centre in ((0, 0), (7, -9)):
        for du, dv in permutations(DIRS, 2):
            a, b = add(centre, du), add(centre, dv)
            t = pairtype(frozenset((a, b)))
            found = False
            for swap, sx, sy in product((False, True), (-1, 1), (-1, 1)):
                def phi(x):
                    z = sub(x, centre)
                    if swap: z = (z[1], z[0])
                    return (sx*z[0], sy*z[1])
                if phi(a) == U and phi(b) == TARGET[t]:
                    assert phi(centre) == C
                    assert all(dist(phi(x), phi(y)) == dist(x, y) for x, y in product((centre, a, b, (3, -4)), repeat=2))
                    found = True
                    break
            assert found
            triple_count += 1
    sites = list(product(range(-1, 2), repeat=2))
    finite_volumes = 0
    for mask in range(1, 1 << len(sites)):
        g = {x for i, x in enumerate(sites) if mask >> i & 1}
        witness = max(g)
        assert add(witness, (1, 0)) not in g
        s = protected(g)
        assert witness in s
        assert all(min(dist(x, y) for y in s) < math.inf for x in sites)
        finite_volumes += 1
    shifts = 0
    for _ in range(20000):
        s = {tuple(rng.randrange(-5, 6) for _ in range(2)) for _ in range(rng.randrange(1, 8))}
        a, b, u, v = [tuple(rng.randrange(-7, 8) for _ in range(2)) for _ in range(4)]
        depth = min(min(dist(u, z), dist(v, z)) for z in s)
        d = rng.randrange(depth + 1)
        shift = max(min(dist(a, u), dist(a, v)), min(dist(b, u), dist(b, v)))
        assert max(d-shift, 0) <= min(min(dist(a, z), dist(b, z)) for z in s)
        shifts += 1
    return dict(ordered_triples=triple_count, nonempty_volumes=finite_volumes, shift_cases=shifts)

def exposure_checks():
    count = 0
    for n in range(8):
        for _ in range(300):
            b = [rng.uniform(0.01, 3) for _ in range(n)]
            c = [rng.uniform(0.01, 1) for _ in range(n)]
            x = [max(1, bi) + rng.random() for bi in b]
            sigma = list(range(n))
            rng.shuffle(sigma)
            prefix, rhs = 1.0, 0.0
            for i in sigma:
                prefix *= x[i]
                rhs += abs(math.log(c[i])-math.log(b[i]))*prefix
            assert abs(math.prod(b)-math.prod(c)) <= rhs + 1e-9
            count += 1
    return dict(permuted_product_cases=count)

ALPHA = {True: Q(145217, 10**6), False: Q(150000, 10**6)}
BETA = {True: Q(352782, 10**6), False: Q(357549, 10**6)}
BPRIME = {True: Q(340008, 10**6), False: Q(344661, 10**6)}
PASSAGE = {True: Q(1000, 961), False: Q(200, 187)}
WITNESS = {'B': Q(1), 'C': Q(5404319552844595, 4503599627370496)}

def canonical_closed(max_n):
    out = []
    for t, v in TARGET.items():
        def visit(vertices, used):
            y = vertices[-1]
            if y == v:
                out.append((t, tuple(vertices)))
                return
            if len(vertices) == max_n+1: return
            for z in neigh(y):
                e = bond(y, z)
                if z == C or e in used: continue
                visit(vertices+[z], used | {e})
        visit([U], set())
    return out

def kernel_data(t, vertices, i):
    y, o = vertices[i:i+2]
    incoming = (-1, 0) if i == 0 else sub(y, vertices[i-1])
    straight = sub(o, y) == incoming
    counts = Counter(vertices[:i])
    assert o != C and counts[o] < 2
    arrival = sub(y, incoming)
    other = neigh(y) - {arrival, o}
    live = {z for z in other if z != C and counts[z] < 2}
    pairs = {}
    for a, b in combinations(live | {o}, 2):
        p = frozenset((a, b))
        coef = (BPRIME[straight] if len(live) == 1 else BETA[straight]) if o in p else ALPHA[straight]
        shift = max(min(dist(z, U), dist(z, TARGET[t])) for z in p)
        assert 2*shift <= (len(vertices)-1)+2
        pairs[p] = (pairtype(p), shift, coef)
    return incoming, straight, pairs

def kernel_checks(closed):
    index_count, pair_count = 0, 0
    length_counts = Counter()
    for t, vertices in closed:
        n = len(vertices)-1
        assert n >= 2 and n % 2 == 0
        length_counts[f'{t}:{n}'] += 1
        visited = set()
        first = []
        data = []
        for i, y in enumerate(vertices[:-1]):
            incoming, straight, pairs = kernel_data(t, vertices, i)
            index_count += 1
            pair_count += len(pairs)
            if y not in visited: first.append(i)
            visited.add(y)
            reward = sum((c*WITNESS[typ] for typ, _, c in pairs.values()), Q(0))
            data.append((straight, reward))
        def key(i):
            straight, reward = data[i]
            x = PASSAGE[straight]
            return (reward == 0, (x-1)/(x*reward) if reward else 0, i)
        order = sorted(first, key=key)
        recursive = Q(0)
        for i in reversed(order):
            straight, reward = data[i]
            recursive = PASSAGE[straight]*(reward+recursive)
        prefix, explicit = Q(1), Q(0)
        for i in order:
            straight, reward = data[i]
            prefix *= PASSAGE[straight]
            explicit += prefix*reward
        assert recursive == explicit
    return dict(closed_trails=len(closed), departures=index_count, response_pairs=pair_count, length_counts=dict(sorted(length_counts.items())))

def is_consistent(g, s, status, kept):
    active = {x for x in g if status[x] != 'X'}
    for x in g:
        assert kept[x] <= neigh(x) & g
        if x in s: assert status[x] == 'U' and kept[x] == neigh(x)&g
        if status[x] == 'U': assert kept[x] == neigh(x)&g
        if status[x] == 'D': assert len(kept[x]) == 2
        for y in neigh(x)&active:
            if x in active: assert (y in kept[x]) == (x in kept[y])
    return active

def actual_neighbours(g, status, kept, x):
    if x not in g or status[x] == 'X': return set()
    return {y for y in neigh(x)&g if status[y] != 'X' and y in kept[x] and x in kept[y]}

def trace_step(status, kept, y, o):
    assert o in actual_neighbours(set(status), status, kept, y)
    status = dict(status)
    kept = {x: set(k) for x, k in kept.items()}
    status[y] = 'D' if status[y] == 'U' else 'X'
    kept[y].discard(o)
    kept[o].discard(y)
    return status, kept

def actual_checks(closed):
    g = set(product(range(-5, 6), repeat=2))
    s = protected(g)
    counts = Counter()
    for trial in range(50):
        t = 'B' if trial % 2 == 0 else 'C'
        v = TARGET[t]
        status = {x: ('X' if x not in s and x not in (U, v) and (x == C or rng.random() < 0.2) else 'U') for x in g}
        kept = {x: neigh(x)&g for x in g}
        for x in sorted(g-s):
            ns = {y for y in neigh(x)&g if status[y] != 'X'}
            if status[x] == 'U' and len(ns) <= (1 if x in (U, v) else 2) and rng.random() < 0.7:
                status[x] = 'D'
                kept[x] = ns | set(sorted((neigh(x)&g)-ns)[:2-len(ns)])
        active = is_consistent(g, s, status, kept)
        assert C not in active and U in active and v in active
        if status[U] == 'U': kept[U].discard(C)
        for typ, vertices in closed:
            if typ != t or any(x not in active for x in vertices): continue
            if any(vertices[i+1] not in actual_neighbours(g, status, kept, vertices[i]) for i in range(len(vertices)-1)): continue
            if any(x in s for x in vertices[:-1]): continue
            st, kp = dict(status), {x: set(k) for x, k in kept.items()}
            actual_base, lattice_base = Q(1), Q(1)
            for i, y in enumerate(vertices[:-1]):
                o = vertices[i+1]
                ns = actual_neighbours(g, st, kp, y)
                assert o in ns and y not in s
                incoming, straight, kernel_pairs = kernel_data(t, vertices, i)
                revisit = y in vertices[:i]
                if st[y] == 'D':
                    assert len(ns) <= 1
                    actual_base *= Q(1, 5)
                else:
                    assert st[y] == 'U' and not revisit and len(ns) <= 3
                    actual_base *= Q(1, 3)
                    assert sub(y, incoming) not in ns
                    for a, b in combinations(ns, 2):
                        p = frozenset((a, b))
                        assert p in kernel_pairs
                        actual_coef = (BPRIME[straight] if len(ns) == 2 else BETA[straight]) if o in p else ALPHA[straight]
                        assert actual_coef <= kernel_pairs[p][2]
                        counts['actual_response_pairs'] += 1
                    removed = dict(st)
                    removed[y] = 'X'
                    is_consistent(g, s, removed, kp)
                lattice_base *= Q(1, 5) if revisit else Q(1, 3)
                counts['actual_departures'] += 1
                st, kp = trace_step(st, kp, y, o)
            assert actual_base <= lattice_base
            assert st[v] == status[v]
            counts['actual_closed_trails'] += 1
        # Sample first trails ending in S, then check terminal target and second start.
        first_trails = []
        def stopped(vertices, used):
            y = vertices[-1]
            if y == v: return
            if y in s:
                first_trails.append(tuple(vertices))
                return
            if len(vertices) >= 8 or len(first_trails) >= 20: return
            for z in sorted(actual_neighbours(g, status, kept, y)):
                e = bond(y, z)
                if e not in used: stopped(vertices+[z], used|{e})
        stopped([U], set())
        for vertices in first_trails:
            st, kp = dict(status), {x: set(k) for x, k in kept.items()}
            for y, o in zip(vertices, vertices[1:]): st, kp = trace_step(st, kp, y, o)
            e = vertices[-1]
            assert st[e] == 'U' and e in s
            assert len(actual_neighbours(g, st, kp, e)) + len(neigh(e)-g) <= 3
            assert st[v] == status[v] and kp[v] == kept[v]
            assert len(actual_neighbours(g, st, kp, v)) <= (3 if st[v] == 'U' else 1)
            before = {bond(x, y) for x in g for y in actual_neighbours(g, st, kp, x)}
            if st[v] == 'U': kp[v].discard(C)
            after = {bond(x, y) for x in g for y in actual_neighbours(g, st, kp, x)}
            assert before == after
            assert C not in actual_neighbours(g, st, kp, v)
            counts['terminal_auxiliary_cases'] += 1
        counts['ordinary_domains'] += 1
    return dict(counts)

if __name__ == '__main__':
    closed = canonical_closed(8)
    results = dict(geometry=geometry_checks(), exposure=exposure_checks(), kernel=kernel_checks(closed), actual_domains=actual_checks(closed))
    print(json.dumps(results, indent=2))
