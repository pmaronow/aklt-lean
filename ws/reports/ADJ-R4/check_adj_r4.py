"""Independent exact checks for ADJ-R4; Python standard library only.

No source or referee module is imported.  The transfer tensors below are
derived directly from the second and fourth spherical moments.
"""
from ast import literal_eval
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json


def matrix_product(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(4)), Q(0))
             for j in range(4)] for i in range(4)]


def ring_trace(tensors):
    a = [[Q(i == j) for j in range(4)] for i in range(4)]
    for tensor in tensors:
        a = matrix_product(a, tensor)
    return sum(a[i][i] for i in range(4))


def vertex_tensor(h, insertion=0):
    """Integral phi_a phi_b (1+h*n_3) [n_insertion] dn.

    phi=(1,n_1,n_2,n_3).  A nonzero insertion uses E[n_i*n_j]
    and E[n_i*n_j*n_k*n_l]=(delta_ij delta_kl+...)/15.
    """
    a = [[Q(0) for _ in range(4)] for _ in range(4)]
    if not insertion:
        a[0][0] = Q(1)
        for i in range(1, 4):
            a[i][i] = Q(1, 3)
        a[0][3] = a[3][0] = h / 3
    else:
        k = insertion
        a[0][0] = h * Q(k == 3, 3)
        a[0][k] = a[k][0] = Q(1, 3)
        for i, j in product(range(1, 4), repeat=2):
            a[i][j] = h * Q((i == j) * (k == 3)
                            + (i == k) * (j == 3)
                            + (i == 3) * (j == k), 15)
    return a


def exact_diamond():
    for pinned in (False, True):
        # Integrating a radius-three connector with two equal pins gives B.
        if pinned:
            b = [[Q(4, 3), Q(0), Q(0), Q(2, 3)],
                 [Q(0), Q(2, 5), Q(0), Q(0)],
                 [Q(0), Q(0), Q(2, 5), Q(0)],
                 [Q(2, 3), Q(0), Q(0), Q(8, 15)]]
        else:
            b = [[Q(0) for _ in range(4)] for _ in range(4)]
            b[0][0] = Q(1)
            for i in range(1, 4):
                b[i][i] = Q(1, 3)
        # A radius-three axial tip with three equal pins gives 2*(1+3*n_3/5).
        # Its common factor 2 cancels. Radius-two sites alternate axial/corner.
        fields = [Q(3, 5) if pinned and i % 2 == 0 else Q(0)
                  for i in range(8)]
        tensors = [matrix_product(vertex_tensor(h), b) for h in fields]
        den = ring_trace(tensors)
        num = Q(0)
        for k in range(1, 4):
            marked = [matrix_product(vertex_tensor(h, k if i in (0, 4) else 0), b)
                      for i, h in enumerate(fields)]
            num += ring_trace(marked)
        p = num / (9 * den)  # the two interior leaves each give n_axis/3
        rho = Q(3, 5) / (1 + p / 5)
        if not pinned:
            free_p, free_rho = p, rho
            # Independent free high-temperature expansion on the 16-edge ring.
            assert p == (2 * Q(1, 3) ** 8) / (1 + 3 * Q(1, 3) ** 16) / 9
        print(f"diamond {'pinned' if pinned else 'free'} P_fo = {p}")
        print(f"diamond {'pinned' if pinned else 'free'} R = {rho}")
    assert p == Q(162376940888609, 7284251314603125)
    assert free_p == Q(243, 7174454)
    assert rho != free_rho
    print(f"nonzero R_free - R_pinned = {free_rho - rho}")
    print("initial D two-bond bound: rho/3 <= 1/4 < 1/3 <= omega_1")
    assert Q(3, 5) / (1 - Q(1, 5)) / 3 == Q(1, 4)


DIRS = ((1, 0), (-1, 0), (0, 1), (0, -1))


def neighbours(x):
    return {(x[0] + a, x[1] + b) for a, b in DIRS}


def edge(a, b):
    return tuple(sorted((a, b)))


def closure_checks():
    g = set(product(range(-4, 5), repeat=2))
    s = {p for p in g if max(map(abs, p)) >= 3}
    c, u, v = (0, 0), (-1, 0), (1, 0)

    def consistent(st, keep):
        return (all(st[p] == 'U' and keep[p] == neighbours(p) & g for p in s)
                and all(st[p] != 'U' or keep[p] == neighbours(p) & g for p in g)
                and all(st[p] != 'D' or len(keep[p]) == 2 for p in g)
                and all(st[p] == 'X' or st[q] == 'X' or
                        ((q in keep[p]) == (p in keep[q]))
                        for p in g for q in neighbours(p) & g))

    def trace(w):
        st = {p: ('X' if p == c else 'U') for p in g}
        keep = {p: neighbours(p) & g for p in g}
        assert consistent(st, keep)
        print("j=0 printed arrival-bond assertion:", c not in keep[u])
        keep[u].remove(c)  # normalized initial U kept set
        mass = Q(1)
        used = set()
        for j, (a, b) in enumerate(zip(w, w[1:]), 1):
            assert st[a] != 'X' and st[b] != 'X'
            assert b in keep[a] and a in keep[b]
            assert edge(a, b) not in used
            used.add(edge(a, b))
            keep[a].remove(b)
            keep[b].remove(a)
            if st[a] == 'D':
                st[a] = 'X'
                mass *= Q(3, 5)
            else:
                st[a] = 'D'
            assert all(p == b or st[p] != 'D' or len(keep[p]) == 2 for p in g)
            assert all(p == b or st[p] != 'U' or keep[p] == neighbours(p) & g for p in g)
            assert all(st[p] == 'X' or st[q] == 'X' or
                       ((q in keep[p]) == (p in keep[q]))
                       for p in g for q in neighbours(p) & g)
            if b not in s:
                removed = dict(st)
                removed[b] = 'X'
                assert consistent(removed, keep)
            if b == u:
                print(f"j={j} live u: status={st[b]}, kept={sorted(keep[b])}")
        return st, keep, mass

    w = [u, (-1, 1), (-2, 1), (-2, 0), u, (-1, -1), (0, -1), (1, -1), v]
    assert not set(w[:-1]) & (s | {v})
    st, keep, mass = trace(w)
    print("eight-step trace mass =", mass)
    assert mass == Q(3, 5)
    st, keep, mass = trace([u, (-2, 0), (-3, 0)])
    e = (-3, 0)
    print("terminal e in S =", e in s)
    print("terminal e keeps all bonds =", keep[e] == neighbours(e) & g)
    st[e] = 'X'
    print("removing terminal e is consistent =", consistent(st, keep))
    nearby = sorted((a, b) for a in range(-2, 3) for b in range(-2, 3)
                    if 0 < abs(a) + abs(b) <= 2)
    assert len(nearby) == 12
    print("radius-two sites other than e =", len(nearby))


def canonical(out, kinds, bonds):
    keys = []
    for reflect in (False, True):
        def f(p):
            return (-p[0], p[1]) if reflect else p
        keys.append((f(out), tuple(sorted((f(x), k) for x, k in kinds.items())),
                     tuple(sorted(edge(f(a), f(b)) for a, b in bonds))))
    return min(keys)


def pattern_checks():
    """Independent enumeration with corner choices constrained before products.

    Actual corner kept sets are projected to their two internal bonds;
    after slot enlargement their external choices have identical functions.
    """
    y, arrival = (0, 0), (0, -1)
    east, north, west = (1, 0), (0, 1), (-1, 0)
    d1 = [arrival, east, north, west]
    corners = list(product((-1, 1), repeat=2))
    tips = {(2, 0), (-2, 0), (0, 2), (0, -2)}
    options = {}
    for p in d1:
        n = neighbours(p)
        if p == arrival:
            options[p] = [('X', set())] + [('D', set(k)) for k in combinations(sorted(n - {y}), 2)]
        else:
            options[p] = [('U', n), ('X', set())] + [('D', {y, q}) for q in sorted(n - {y})]
    reps = set()
    raw = 0
    for choices in product(*(options[p] for p in d1)):
        chosen = dict(zip(d1, choices))
        corner_options = []
        for p in corners:
            adjacent = neighbours(p) & set(d1)
            opts = [('U', adjacent), ('X', set())]
            opts += [('D', set(k)) for r in range(3) for k in combinations(sorted(adjacent), r)]
            opts = [(k, keep) for k, keep in opts
                    if k == 'X' or all(chosen[q][0] == 'X' or
                                       ((q in keep) == (p in chosen[q][1])) for q in adjacent)]
            corner_options.append(opts)
        for cs in product(*corner_options):
            all_choices = dict(chosen)
            all_choices.update(zip(corners, cs))
            bonds = set()
            for p in (east, north, west):
                if chosen[p][0] != 'X':
                    bonds.add(edge(y, p))
            for p in d1:
                k, keep = chosen[p]
                if k == 'X':
                    continue
                for q in keep - {y}:
                    if q in tips or (all_choices[q][0] != 'X' and p in all_choices[q][1]):
                        bonds.add(edge(p, q))
            relevant = {p for b in bonds for p in b}
            kinds = {p: k.lower() for p, (k, _) in all_choices.items() if p in relevant}
            for out in (north, east):
                if edge(y, out) in bonds:
                    raw += 1
                    reps.add(canonical(out, kinds, bonds))
    straight = sum(k[0] == north for k in reps)
    print(f"clarified pattern enumeration: raw={raw}, classes={len(reps)}, straight={straight}, turns={len(reps)-straight}")
    data_path = Path('/home/ubuntu/aklt/manuscript/bundle/programs/data/pext/pext7962.json')
    data = json.loads(data_path.read_text())
    stored = {canonical(tuple(a['out']), {literal_eval(p): k for p, k in a['kinds'].items()},
                        {edge(tuple(b[0]), tuple(b[1])) for b in a['present']}) for a in data}
    print("classes equal supplied pext7962.json =", reps == stored)
    print("independent-only classes =", len(reps - stored), "; data-only classes =", len(stored - reps))
    assert len(reps) == 7962 and straight == 2696 and reps == stored


def terminal_d_check():
    # Fix the remaining neighbour spin to a=(0,0,1). The atom at zero
    # contributes 2/5 to the denominator, and zero to both observables.
    den = Q(3, 5) * vertex_tensor(Q(0))[0][0] + Q(2, 5)
    mean_z = Q(3, 5) * vertex_tensor(Q(0))[3][3] / den
    norm_sq = Q(3, 5) * vertex_tensor(Q(0))[0][0] / den
    assert den == 1 and mean_z == Q(1, 5) and norm_sq == Q(3, 5)
    print("terminal D, remaining unit bond a: E[n|a]=a/5, E[|n|^2|a]=3/5")


if __name__ == '__main__':
    exact_diamond()
    closure_checks()
    terminal_d_check()
    pattern_checks()
