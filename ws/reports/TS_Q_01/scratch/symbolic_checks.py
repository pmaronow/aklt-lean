"""Exact symbolic diagnostics for the truth sweep; no Lean proofs."""
from collections import Counter
from itertools import product
import json

import sympy as s

Q = s.Rational
sqrt5 = s.sqrt(5)
phi = (1 + sqrt5) / 2
r2 = phi + 2
bound = (5 - sqrt5) / 505
T = s.Matrix([[Q(99, 101), Q(-20, 101), 0],
              [Q(20, 101), Q(99, 101), 0], [0, 0, 1]])
labels = list(product(range(3), range(2), range(2)))


def reduce(expr):
    return s.simplify(s.expand(expr))


def raw_vertex(label):
    family, first, second = label
    a = 1 if first == 0 else -1
    b = (1 if second == 0 else -1) * phi
    return s.Matrix(([0, a, b], [a, b, 0], [b, 0, a])[family])


raw = {a: raw_vertex(a) for a in labels}
assert all(reduce(u.dot(u) / r2 - 1) == 0 for u in raw.values())
distances = Counter()
for a, b in product(labels, repeat=2):
    if a != b:
        d = reduce((raw[a] - raw[b]).dot(raw[a] - raw[b]) / r2)
        assert (d - 1).is_positive
        distances[str(d)] += 1

assert T.T * T == s.eye(3)
assert T.det() == 1
displacement = {}
self_values = {}
for k in (1, 2):
    delta = T ** k - s.eye(3)
    gram = s.simplify(delta.T * delta)
    expected = Q(4, 101) if k == 1 else Q(1600, 10201)
    assert gram == s.diag(expected, expected, 0)
    assert expected <= Q(40, 101) ** 2
    displacement[str(k)] = str(expected)
    values = Counter()
    for a in labels:
        d = reduce(1 - raw[a].dot(T ** k * raw[a]) / r2)
        assert reduce(d - bound).is_nonnegative
        values[str(d)] += 1
    self_values[str(k)] = dict(values)
assert reduce(1 - raw[(0, 0, 0)].dot(T * raw[(0, 0, 0)]) / r2 - bound) == 0
assert reduce(bound - 2 / (101 * r2)) == 0

relative_cases = []
for i, j in product(range(3), repeat=2):
    if i == j:
        continue
    k = abs(j - i)
    assert 1 <= k <= 2
    # The bilinear matrix identity checks every real pair of vectors.
    lhs = (T ** i).T * T ** j
    rhs = T ** k if i < j else (T ** k).T
    assert lhs == rhs
    relative_cases.append({"i": i, "j": j, "k": k,
                           "labels": "a,b" if i < j else "b,a"})

# Strict triangle argument: distance > 1 and displacement <= 40/101.
triangle_distance = 1 - Q(40, 101)
triangle_loss = triangle_distance ** 2 / 2
assert triangle_distance == Q(61, 101)
assert triangle_loss > Q(9, 50)
assert Q(40, 101) < Q(2, 5)

# Spinor north chart. t is the positive square root of 2(1+z).
x, y, t = s.symbols("x y t", real=True)
z = s.symbols("z", real=True)
unit_remainder = x*x + y*y - (1-z*z)
t_remainder = t*t - 2*(1+z)
relations = s.groebner([unit_remainder, t_remainder], x, y, t, z)
spinor = s.Matrix([t/2, (x+s.I*y)/t])
density = s.Matrix([[1+z, x-s.I*y], [x+s.I*y, 1-z]]) / 2
matrix_error = spinor * spinor.conjugate().T - density
for expr in matrix_error:
    numerator = s.together(expr).as_numer_denom()[0]
    assert relations.reduce(s.expand(numerator))[1] == 0
norm_error = s.together((spinor.conjugate().T * spinor)[0] - 1)
assert relations.reduce(s.expand(norm_error.as_numer_denom()[0]))[1] == 0
south_spinor = s.Matrix([0, 1])
assert south_spinor * south_spinor.conjugate().T == density.subs({x: 0, y: 0, z: -1})

print(json.dumps({
    "icosahedron_labels": len(labels),
    "ordered_distinct_pairs": sum(distances.values()),
    "squared_distance_counts": dict(distances),
    "T_squared": str(T**2),
    "displacement_coefficients": displacement,
    "self_rotation_loss_counts": self_values,
    "frame_bound": str(bound),
    "relative_rotation_cases": relative_cases,
    "triangle_loss_lower_bound_strict": str(triangle_loss),
    "triangle_loss_margin_over_9_50": str(triangle_loss - Q(9, 50)),
    "spinor": "all four density entries and norm exact modulo the unit and square-root equations; south pole checked",
    "result": "all checks passed"
}, indent=2))
