"""Exact finite checks for the truth sweep; no Lean proofs or repository writes."""
from fractions import Fraction as Q
from itertools import product
from math import comb, isqrt
import json


def rank(rows):
    a = [[Q(x) for x in row] for row in rows]
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        v = a[r][c]
        a[r] = [x/v for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                v = a[i][c]
                a[i] = [x-v*y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


# These are ordinary monomial coefficient coordinates. The frozen sqrt(choose)
# factors give an invertible diagonal change of coordinates, since choose(4,j)>0.
pair_labels = list(product(range(5), repeat=2))
quotient_labels = list(product(range(4), repeat=2))
diagonal = [[int(j+k == t) for j,k in pair_labels] for t in range(9)]
mult = [[0]*16 for _ in range(25)]
for c, (a,b) in enumerate(quotient_labels):
    mult[pair_labels.index((a,b+1))][c] += 1
    mult[pair_labels.index((a+1,b))][c] -= 1
composition = [[sum(diagonal[i][k]*mult[k][j] for k in range(25))
                for j in range(16)] for i in range(9)]
assert rank(diagonal) == 9
assert rank(mult) == 16
assert all(x == 0 for row in composition for x in row)


# Check all possible local exponents used by monomialDegree and reconstruction.
local_exponents = [(a,b) for a in range(5) for b in range(5) if a+b == 4]
encoded = [(4-j,j) for j in range(5)]
assert set(local_exponents) == set(encoded) and len(set(encoded)) == 5
assert all(comb(4,j)>0 for j in range(5))


# Literal sparse action of the frozen five-factor spin matrices, restricted to
# the two-step actions needed by the extremal-coordinate witness. All square
# roots encountered in these actions are exact integers.
def add(*vectors):
    out = {}
    for vec in vectors:
        for key, value in vec.items():
            out[key] = out.get(key,Q(0)) + value
    return {k:v for k,v in out.items() if v}


def scale(c, vector):
    return {k:c*v for k,v in vector.items() if c*v}


def at(op, site, vector):
    out = {}
    for state, amp in vector.items():
        j = state[site]
        new = list(state)
        if op == 'Z':
            coefficient = 2-j
        elif op == '+':
            if j == 0:
                continue
            radicand = j*(5-j)
            coefficient = isqrt(radicand)
            assert coefficient**2 == radicand
            new[site] -= 1
        else:
            if j == 4:
                continue
            radicand = (j+1)*(4-j)
            coefficient = isqrt(radicand)
            assert coefficient**2 == radicand
            new[site] += 1
        key = tuple(new)
        out[key] = out.get(key,Q(0)) + coefficient*amp
    return {k:v for k,v in out.items() if v}


def total(op, leaf, vec):
    return add(at(op,0,vec),at(op,leaf,vec))


def casimir(leaf, vec):
    return add(total('Z',leaf,total('Z',leaf,vec)),
               scale(Q(1,2),add(total('+',leaf,total('-',leaf,vec)),
                                total('-',leaf,total('+',leaf,vec)))))


extremal_results = []
for label in (0,4):
    vector = {(label,)*5: Q(1)}
    actions = [casimir(leaf,vector) for leaf in range(1,5)]
    assert all(action == scale(20,vector) for action in actions)
    extremal_results.append({'constant_label':label, 'casimir_eigenvalues':[20]*4})


# Small tori include period three in either or both directions. Count actual
# indexed bonds, unique unordered edges, distinct neighbours, and site degrees.
tori = []
for L,N in product(range(3,9),repeat=2):
    sites = list(product(range(L),range(N)))
    edges = []
    for x,y in sites:
        edges.extend([((x,y),((x+1)%L,y)),((x,y),(x,(y+1)%N))])
    unordered = [frozenset(e) for e in edges]
    assert all(len(e) == 2 for e in unordered)
    assert len(set(unordered)) == len(edges)
    for x in sites:
        incident = [e for e in unordered if x in e]
        neighbours = set().union(*incident)-{x}
        assert len(incident) == len(neighbours) == 4
    tori.append([L,N])


result = {
    'pair_diagonal_rank':rank(diagonal),
    'determinant_multiplication_rank':rank(mult),
    'diagonal_after_multiplication_is_zero':True,
    'local_degree_four_exponents':local_exponents,
    'choose_4_values':[comb(4,j) for j in range(5)],
    'extremal_star_casimir_checks':extremal_results,
    'tori_checked':tori,
    'all_checks_passed':True,
    'scope':'Finite checks support the audit; the universal verdicts also use the mathematical arguments described in report.md.'
}
print(json.dumps(result,indent=2))
