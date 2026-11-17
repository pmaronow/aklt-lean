"""Selected edge-case checks; these are not proofs of the audited leaves."""
from fractions import Fraction as Q
from itertools import combinations, product
from math import prod, sqrt
from random import Random
import json

summary = {}
phi = (1 + sqrt(5)) / 2
radius = sqrt(phi + 2)
atoms = [tuple(z / radius for z in ((0, a, b), (a, b, 0), (b, 0, a))[g])
         for g in range(3) for a in (1, -1) for b in (phi, -phi)]
dot = lambda a, b: sum(x * y for x, y in zip(a, b))
neg = lambda a: tuple(-x for x in a)
zero = (0., 0., 0.)
assert len(set(atoms)) == 12
assert all(abs(dot(a, a) - 1) < 1e-14 for a in atoms)

# A nontrivial rational orthogonal matrix, and its reflection.
identity = [[Q(i == j) for j in range(3)] for i in range(3)]
rotation = [[Q(-2, 3), Q(2, 15), Q(11, 15)],
            [Q(2, 3), Q(-1, 3), Q(2, 3)],
            [Q(1, 3), Q(14, 15), Q(2, 15)]]
reflection = [[(-1 if i == 0 else 1) * r for r in row] for i, row in enumerate(rotation)]
tensor_error = 0.
tensor_checks = 0
for R in (identity, rotation, reflection):
    assert all(sum(R[k][i] * R[k][j] for k in range(3)) == (i == j)
               for i in range(3) for j in range(3))
    transformed = [tuple(dot(row, a) for row in R) for a in atoms] + [zero]
    for c in (-2., 0., 3/5, 1., 2.5):
        weights = [c / 12] * 12 + [1-c]
        for d in range(5):
            for indices in product(range(3), repeat=d):
                value = sum(w * prod(a[i] for i in indices) for w, a in zip(weights, transformed))
                expected = 1. if d == 0 else 0.
                if d == 2:
                    expected = c / 3 if indices[0] == indices[1] else 0.
                if d == 4:
                    i, j, k, l = indices
                    expected = c * ((i == j and k == l) + (i == k and j == l) + (i == l and j == k)) / 15
                tensor_error = max(tensor_error, abs(value - expected))
                tensor_checks += 1
assert tensor_error < 1e-13
summary['tensor_moments'] = {'moments': tensor_checks, 'max_abs_error': tensor_error}

# Exact rational finite quadratures, including zero sites, empty alphabets,
# a zero polynomial, signed weights, zero coordinates, and degree above four.
def check_expansion(n, alphabets, weights, vectors, polynomial):
    configurations = list(product(*alphabets))
    def moment(exponent):
        return sum(prod(weights[x][a[x]] for x in range(n)) *
                   prod(vectors[x][a[x]][i] ** exponent[3*x+i]
                        for x in range(n) for i in range(3)) for a in configurations)
    lhs = sum(prod(weights[x][a[x]] for x in range(n)) *
              sum(c * prod(vectors[x][a[x]][i] ** m[3*x+i]
                           for x in range(n) for i in range(3)) for m, c in polynomial.items())
              for a in configurations)
    rhs = sum(c * moment(m) for m, c in polynomial.items())
    assert lhs == rhs

check_expansion(0, [], [], [], {(): Q(7, 3)})
check_expansion(0, [], [], [], {})
check_expansion(1, [[]], [{}], [{}], {(0, 0, 0): Q(4)})
check_expansion(2, [[0], []], [{0: Q(-3)}, {}], [{0: (Q(0), Q(2), Q(3))}, {}], {(0,)*6: Q(2)})
check_expansion(1, [[0, 1]], [{0: Q(-2), 1: Q(3, 4)}],
                [{0: (Q(0), Q(-2), Q(3)), 1: (Q(2), Q(1, 3), Q(-1))}],
                {(0, 0, 0): Q(-4), (5, 2, 1): Q(2, 7), (0, 1, 0): Q(3)})
summary['exact_polynomial_expansions'] = 5

ball_points = atoms + [zero] + [tuple(x / 3 for x in a) for a in atoms]
assert all(-1e-13 <= 1 + dot(a, b) <= 2 + 1e-13 for a, b in product(ball_points, repeat=2))
summary['ball_pairs'] = len(ball_points) ** 2

avoidance_cases = 0
for k in range(5):
    for forbidden in combinations(range(12), k):
        good = [a for a in atoms if all(1 + dot(a, neg(atoms[i])) > 1e-10 for i in forbidden)]
        assert len(good) == 12 - k
        avoidance_cases += 1
summary['antipodal_field_sets_up_to_four'] = avoidance_cases

# All simple graphs with at most five sites. Fill each site's unused degree
# budget with pins, and run the stated greedy choice.
greedy_cases = 0
for n in range(6):
    edges = list(combinations(range(n), 2))
    for mask in range(1 << len(edges)):
        bonds = [e for t, e in enumerate(edges) if mask & (1 << t)]
        degree = [sum(x in e for e in bonds) for x in range(n)]
        pins = [[neg(atoms[(3*x+j) % 12]) for j in range(4-degree[x])] for x in range(n)]
        assigned = []
        for x in range(n):
            fields = pins[x] + [assigned[z] for z in range(x) if (z, x) in bonds]
            assert len(fields) <= 4
            assigned.append(next(a for a in atoms if all(1 + dot(a, b) > 1e-10 for b in fields)))
        assert all(1 + dot(assigned[x], assigned[y]) > 1e-10 for x, y in bonds)
        assert all(1 + dot(a, assigned[x]) > 1e-10 for x in range(n) for a in pins[x])
        greedy_cases += 1
summary['greedy_graphs'] = greedy_cases

# Sparse integer polynomial expansions keep the full observable List.
def mul(p, q):
    out = {}
    for m, a in p.items():
        for k, b in q.items():
            exponent = tuple(x + y for x, y in zip(m, k))
            out[exponent] = out.get(exponent, 0) + a*b
    return out

def free_polynomial(n, bonds, pairs):
    constant = (0,) * (3*n)
    def dot_poly(e):
        terms = {}
        for i in range(3):
            m = [0] * (3*n)
            m[3*e[0]+i] += 1
            m[3*e[1]+i] += 1
            terms[tuple(m)] = 1
        return terms
    p = {constant: 1}
    for e in bonds:
        factor = dot_poly(e)
        factor[constant] = 1
        p = mul(p, factor)
    for e in pairs:
        p = mul(p, dot_poly(e))
    return p

rng = Random(20261116)
cases = [(0, [], []), (1, [], [(0, 0)] * 2), (1, [], [(0, 0)] * 3),
         (2, [(0, 1)], [(0, 1)] * 3), (1, [(0, 0)], [(0, 0)]),
         (2, [(0, 1), (1, 0)], [(0, 0), (1, 1)])]
for _ in range(100):
    n = rng.randint(1, 3)
    bonds = [e for e in combinations(range(n), 2) if rng.randrange(2)]
    pairs = [(rng.randrange(n), rng.randrange(n)) for _ in range(rng.randrange(5))]
    cases.append((n, bonds, pairs))
admissible = 0
for n, bonds, pairs in cases:
    p = free_polynomial(n, bonds, pairs)
    assert all(c >= 0 for c in p.values())
    budget = [sum(x in e for e in bonds) + sum((a == x) + (b == x) for a, b in pairs) for x in range(n)]
    if all(a < b for a, b in bonds) and all(d <= 4 for d in budget):
        assert all(sum(m[3*x:3*x+3]) <= budget[x] for m in p for x in range(n))
        admissible += 1
assert max(sum(m) for m in free_polynomial(1, [], [(0, 0)] * 2)) == 4
assert max(sum(m) for m in free_polynomial(1, [], [(0, 0)] * 3)) == 6
summary['coefficient_and_degree_cases'] = {'polynomials': len(cases), 'degree_admissible': admissible}

# Factor all 13 by 13 free-letter choices, including zero-mass U letters
# and fibres where off-site masses, bonds, or pins make C zero.
spin = atoms + [zero]
statuses = ['U', 'D', 'U', 'D']
bonds = [(0, 2), (1, 2), (2, 3)]
pins = [[neg(atoms[0])], [atoms[1], atoms[4]], [neg(atoms[0])], [atoms[2]]]
def mass(x, a):
    return (0. if statuses[x] == 'U' else 2/5) if a == 12 else (1/12 if statuses[x] == 'U' else 1/20)

factor_error = 0.
for pinned in (False, True):
    def site(x, a):
        return mass(x, a) * prod(1 + dot(b, spin[a]) for b in pins[x] if pinned)
    for a2, a3 in ((0, 0), (0, 3), (12, 0), (1, 12), (1, 2)):
        C = site(2, a2) * site(3, a3) * (1 + dot(spin[a2], spin[a3]))
        for a, b in product(range(13), repeat=2):
            cfg = [a, b, a2, a3]
            weight = prod(site(x, cfg[x]) for x in range(4)) * prod(1 + dot(spin[cfg[x]], spin[cfg[y]]) for x, y in bonds)
            u = site(0, a) * (1 + dot(spin[a], spin[a2]))
            v = site(1, b) * (1 + dot(spin[b], spin[a2]))
            assert min(C, u, v) >= -1e-13
            factor_error = max(factor_error, abs(weight - C*u*v))
assert factor_error < 1e-13
summary['two_site_factorizations'] = {'letter_choices': 1690, 'max_abs_error': factor_error}
print(json.dumps(summary, indent=2, sort_keys=True))
