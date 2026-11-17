"""Finite diagnostics for exponent indexing and double inversion; no Lean proofs."""
from fractions import Fraction
from itertools import combinations, product
from math import prod


def subsets(n):
    return [set(s) for k in range(n + 1) for s in combinations(range(n), k)]


def monomial_value(exponent, vectors):
    return prod(vectors[j][k] ** exponent[3 * j + k]
                for j in range(len(vectors)) for k in range(3))


families = labels_checked = inversion_checks = norm_checks = 0
triples = [t for t in product(range(2), repeat=3) if sum(t) <= 1]
for n in range(5):
    vectors = [tuple(Fraction(x, d) for x, d in
                     [(j - 1, 2), (-j - 2, 3), (2 * j + 1, 5)]) for j in range(n)]
    for inverted in subsets(n):
        changed = [tuple(-x for x in v) if j in inverted else v
                   for j, v in enumerate(vectors)]
        for before, after in zip(vectors, changed):
            assert sum(x * x for x in before) == sum(x * x for x in after)
            norm_checks += 1
    for active in subsets(n):
        families += 1
        tokens = sorted(active)
        # Independently enumerate whole-vector degree constraints, including
        # inactive tokens and all-zero monomials.
        admissible = {tuple(x for t in blocks for x in t)
                      for blocks in product(*[triples if j in active else [(0, 0, 0)]
                                               for j in range(n)])}
        encoded = []
        for label in product(range(4), repeat=len(tokens)):
            assignment = dict(zip(tokens, label))
            exponent = tuple(int(j in active and assignment[j] == k + 1)
                             for j in range(n) for k in range(3))
            encoded.append(exponent)
            labels_checked += 1
            coordinate_value = prod(Fraction(1) if a == 0 else vectors[j][a - 1]
                                    for j, a in assignment.items())
            original = monomial_value(exponent, vectors)
            assert original == coordinate_value
            for inverted in subsets(n):
                changed = [tuple(-x for x in v) if j in inverted else v
                           for j, v in enumerate(vectors)]
                sign = (-1) ** sum(exponent[3 * j + k]
                                   for j in inverted for k in range(3))
                assert sign * monomial_value(exponent, changed) == original
                inversion_checks += 1
        assert len(encoded) == len(set(encoded)) == 4 ** len(active)
        assert set(encoded) == admissible

print('PASS: n=0..4; token subsets:', families)
print('PASS: distinct Pauli exponents and coordinate monomial values:', labels_checked)
print('PASS: polynomial/vector double-sign cancellation cases:', inversion_checks)
print('PASS: vector squared-norm sign cases:', norm_checks)
print('Empty token sets retain one zero exponent and one label function.')
