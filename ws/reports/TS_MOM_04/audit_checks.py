"""Exact finite-algebra checks for the truth sweep; no Lean proofs."""

import itertools
import json
from pathlib import Path

import sympy as S


def zero(expr):
    return S.simplify(S.expand(expr)) == 0


phi = (1 + S.sqrt(5)) / 2
radius = S.sqrt(phi + 2)
atoms = []
for group, sign_a, sign_b in itertools.product(range(3), (1, -1), (1, -1)):
    a, b = S.Integer(sign_a), sign_b * phi
    raw = ((0, a, b), (a, b, 0), (b, 0, a))[group]
    atoms.append(S.Matrix([c / radius for c in raw]))
assert len(atoms) == 12
assert all(zero(v.dot(v) - 1) for v in atoms)

moments = {}
for m in itertools.product(range(5), repeat=3):
    if sum(m) > 4:
        continue
    value = S.simplify(sum(S.prod(v[i] ** m[i] for i in range(3)) for v in atoms) / 12)
    if sum(m) == 0:
        expected = S.Integer(1)
    elif any(e % 2 for e in m):
        expected = S.Integer(0)
    elif sum(m) == 2:
        expected = S.Rational(1, 3)
    elif 4 in m:
        expected = S.Rational(1, 5)
    else:
        expected = S.Rational(1, 15)
    assert zero(value - expected), (m, value, expected)
    moments[m] = value

x = S.symbols("x0:3")
fields = [S.Matrix(S.symbols(f"a{j}_0:3")) for j in range(3)]
W = S.prod(1 + sum(x[i] * a[i] for i in range(3)) for a in fields)


def quadrature(poly):
    return S.expand(sum(coeff * moments[m] for m, coeff in S.Poly(poly, *x).terms()))


A = quadrature(W)
B = S.Matrix([quadrature(x[i] * W) for i in range(3)])
p = sum(fields[i].dot(fields[j]) for i, j in ((0, 1), (0, 2), (1, 2)))
V = 5 * sum(fields, S.zeros(3, 1))
for i, j, k in ((0, 1, 2), (1, 0, 2), (2, 0, 1)):
    V += fields[i] * fields[j].dot(fields[k])
assert zero(A - (1 + p / 3))
assert all(zero(v) for v in 15 * B - V)

c, s = S.symbols("c s", real=True)
path_fields = [S.Matrix([1, 0, 0]), S.Matrix([c, s, 0]), S.Matrix([c, -s, 0])]
substitution = {a[i]: path_fields[j][i] for j, a in enumerate(fields) for i in range(3)}
A_path = S.expand(A.subs(substitution)).subs(s**2, 1 - c**2).expand()
B_path = B.subs(substitution).applyfunc(lambda v: S.expand(v).subs(s**2, 1 - c**2).expand())
mean_path = B_path.applyfunc(lambda b: S.factor(b / A_path))
assert zero(A_path - (S.Rational(1, 2) + S.Rational(2, 3) * (c + S.Rational(1, 2)) ** 2))
assert mean_path.subs(c, 1) == S.Matrix([S.Rational(3, 5), 0, 0])
assert mean_path.subs(c, -S.Rational(1, 2)) == S.zeros(3, 1)

# Signed products retain loop and repeated-factor multiplicities. Each case
# below is checked by expanding the actual polynomial over exact rationals.
degree_cases = [
    (0, [], [], S.Integer(7)),
    (1, [(0, 0, -1), (0, 0, 2)], [], S.Integer(1)),
    (1, [(0, 0, 0)] * 5, [], S.Integer(0)),
    (1, [], [(0, (1, 0, 0), 1)] * 4, S.Integer(1)),
    (2, [(0, 1, 1), (0, 1, -1)], [(0, (2, -3, 4), -2)], "insert"),
    (2, [(0, 0, -3)], [(0, (0, 0, 0), 9), (1, (1, -1, 2), 0)], S.Integer(1)),
]
degree_results = []
for n, bonds, pins, inserted in degree_cases:
    variables = S.symbols(f"z0:{3*n}")
    get = lambda site, coordinate: variables[3 * site + coordinate]
    if inserted == "insert":
        inserted = get(0, 2) + get(1, 1) ** 2
    occurrences = [sum(u == site for u, v, q in bonds) + sum(v == site for u, v, q in bonds)
                   + sum(u == site for u, a, q in pins) for site in range(n)]
    if variables:
        inserted_monomials = [m for m, coeff in S.Poly(inserted, *variables).terms() if coeff]
    else:
        inserted_monomials = [()] if inserted else []
    assert all(sum(m[3*site:3*site+3]) + occurrences[site] <= 4
               for m in inserted_monomials for site in range(n))
    product = inserted
    for u, v, q in bonds:
        product *= 1 + q * sum(get(u, i) * get(v, i) for i in range(3))
    for u, a, q in pins:
        product *= 1 + q * sum(a[i] * get(u, i) for i in range(3))
    expanded = S.Poly(S.expand(product), *variables) if variables else None
    support = [m for m, coeff in expanded.terms() if coeff] if expanded is not None else [()]
    assert all(sum(m[3*site:3*site+3]) <= 4 for m in support for site in range(n))
    degree_results.append({"n": n, "bonds": len(bonds), "pins": len(pins),
                           "occurrences": occurrences, "nonzero_monomials": len(support)})

# Exact rational checks of the Householder formula, including equal/zero and
# opposite vectors. The general argument is recorded only as a proof route.
transport_cases = [([0, 0, 0], [0, 0, 0]), ([1, 0, 0], [1, 0, 0]),
                   ([1, 0, 0], [-1, 0, 0]), ([1, 2, 3], [3, -1, 2]),
                   ([S.Rational(3, 5), S.Rational(4, 5), 0], [0, 0, 1])]
for v0, w0 in transport_cases:
    v, w = S.Matrix(v0), S.Matrix(w0)
    assert v.dot(v) == w.dot(w)
    u = v - w
    R = S.eye(3) if u == S.zeros(3, 1) else S.eye(3) - 2 * u * u.T / u.dot(u)
    assert R.T * R == S.eye(3)
    assert R * v == w


def finite_mean(field_list, depleted=False):
    weights = [S.prod(1 + v.dot(a) for a in field_list) for v in atoms]
    normalizer = S.simplify(S.Add(*weights) / S.Integer(12))
    numerator = S.Matrix([S.simplify(sum(v[i] * w for v, w in zip(atoms, weights)) / 12)
                          for i in range(3)])
    if depleted:
        normalizer = S.Rational(3, 5) * normalizer + S.Rational(2, 5)
        numerator *= S.Rational(3, 5)
    return normalizer, numerator.applyfunc(lambda b: S.simplify(b / normalizer))


contraction_results = []
for k in (0, 1, 7):
    field_list = [S.Matrix([2, 0, 0])] * k
    Au, mu = finite_mean(field_list)
    Ad, md = finite_mean(field_list, depleted=True)
    assert Au > 0 and Ad > 0
    q = 3 * Au / (3 * Au + 2)
    assert 0 < q < 1
    assert all(zero(v) for v in md - q * mu)
    assert S.simplify(mu.dot(mu) - md.dot(md)) >= 0
    contraction_results.append({"k": k, "U_normalizer": str(Au), "D_normalizer": str(Ad)})

# This orthogonal matrix is not a symmetry of the finite icosahedral support.
R = S.Matrix([[S.Rational(3, 5), -S.Rational(4, 5), 0],
              [S.Rational(4, 5), S.Rational(3, 5), 0], [0, 0, -1]])
covariance_fields = [S.Matrix([1, 0, 0]), S.Matrix([0, 1, 0]),
                     S.Matrix([S.Rational(2, 3), S.Rational(1, 3), S.Rational(2, 3)])]
assert R.T * R == S.eye(3)
assert all(entry != 0 for entry in R * atoms[0])
_, mu = finite_mean(covariance_fields)
_, mr = finite_mean([R * a for a in covariance_fields])
assert all(zero(v) for v in mr - R * mu)

# Repeated atoms with strictly positive weights still give the same moments,
# including the constant monomial at the optional zero atom.
repeated_atoms = atoms * 2
for m, expected in moments.items():
    base = S.simplify(sum(S.prod(v[i] ** m[i] for i in range(3)) for v in repeated_atoms) / 24)
    at_zero = S.prod(S.Integer(0) ** m[i] for i in range(3))
    assert zero(base - expected)
    assert zero(S.Rational(3, 5) * base + S.Rational(2, 5) * at_zero
                - (S.Rational(3, 5) * expected + S.Rational(2, 5) * at_zero))

summary = {
    "method": "SymPy exact arithmetic; corroborating checks, not Lean proofs",
    "explicit_unit_atoms": len(atoms),
    "degree_le_four_monomials_checked": len(moments),
    "generic_triple_normalizer_identity": True,
    "generic_triple_numerator_identity": True,
    "path_normalizer": str(S.factor(A_path)),
    "path_normalizer_lower_bound_identity": str(S.Rational(1, 2) + S.Rational(2, 3) * (c + S.Rational(1, 2)) ** 2),
    "path_mean": [str(v) for v in mean_path],
    "path_endpoint_means": [["3/5", "0", "0"], ["0", "0", "0"]],
    "interaction_degree_cases": degree_results,
    "householder_cases_checked": len(transport_cases),
    "depleted_contraction_cases": contraction_results,
    "covariance_with_non_alphabet_symmetry": True,
    "repeated_atom_quadrature_monomials_checked": len(moments),
}
Path(__file__).with_name("audit_checks.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
