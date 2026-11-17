"""Finite consistency checks for the audit; no Lean proofs or numerical rounding."""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


@dataclass(frozen=True)
class G:
    re: F = F(0)
    im: F = F(0)

    def __add__(self, other):
        other = gauss(other)
        return G(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.re, -self.im)

    def __sub__(self, other):
        return self + -gauss(other)

    def __mul__(self, other):
        other = gauss(other)
        return G(self.re * other.re - self.im * other.im,
                 self.re * other.im + self.im * other.re)

    __rmul__ = __mul__

    def conj(self):
        return G(self.re, -self.im)


def gauss(x):
    return x if isinstance(x, G) else G(F(x))


def ident(n):
    return [[gauss(int(i == j)) for j in range(n)] for i in range(n)]


def scale(c, a):
    return [[gauss(c) * x for x in row] for row in a]


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), G())
             for j in range(len(b[0]))] for i in range(len(a))]


def dagger(a):
    return [[a[j][i].conj() for j in range(len(a))] for i in range(len(a[0]))]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), G())


def det2(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def tensor(factors):
    states = list(product(range(2), repeat=len(factors)))
    result = []
    for s in states:
        row = []
        for t in states:
            value = gauss(1)
            for j, factor in enumerate(factors):
                value = value * factor[s[j]][t[j]]
            row.append(value)
        result.append(row)
    return result


I = G(F(0), F(1))
pauli = [ident(2),
         [[gauss(0), gauss(1)], [gauss(1), gauss(0)]],
         [[gauss(0), -I], [I, gauss(0)]],
         [[gauss(1), gauss(0)], [gauss(0), gauss(-1)]]]


def operator(k, coefficients):
    result = scale(0, ident(2 ** k))
    for word, c in coefficients.items():
        result = add(result, scale(c, tensor([pauli[a] for a in word])))
    return result


def invariant_coefficients(k):
    result = {(0,) * k: F(2, 3)}
    for i in range(k):
        for j in range(i + 1, k):
            for a in range(1, 4):
                word = [0] * k
                word[i] = word[j] = a
                result[tuple(word)] = F(2 * i - j + 3, 2 * j + i + 5)
    return result


def evaluate(coefficients, vectors):
    result = F(0)
    for word, c in coefficients.items():
        for a, v in zip(word, vectors):
            if a:
                c *= v[a - 1]
        result += c
    return result


def act(r, vectors):
    return [[sum(r[i][j] * v[j] for j in range(3)) for i in range(3)]
            for v in vectors]


def transpose(r):
    return list(map(list, zip(*r)))


def quaternion_unitary(a, b, c, d):
    return [[G(a, b), G(c, d)], [G(-c, d), G(a, -b)]]


summary = {}
for a in pauli:
    assert dagger(a) == a
for i in range(1, 4):
    assert mul(pauli[i], pauli[i]) == ident(2)
    assert trace(pauli[i]) == G()
    for j in range(1, 4):
        assert trace(mul(pauli[i], pauli[j])) == gauss(2 * int(i == j))
summary['single_slot_pauli_algebra'] = 'PASS'

word_count = 0
for k in range(4):
    coefficients = {}
    even_coefficients = {}
    for n, word in enumerate(product(range(4), repeat=k)):
        a = tensor([pauli[x] for x in word])
        sign = (-1) ** word.count(2)
        assert dagger(a) == a
        assert [[x.conj() for x in row] for row in a] == scale(sign, a)
        coefficients[word] = F((-1) ** n * (n % 7 + 1), n % 5 + 1)
        if sign == 1:
            even_coefficients[word] = coefficients[word]
        word_count += 1
    general = operator(k, coefficients)
    assert dagger(general) == general
    real = operator(k, even_coefficients)
    assert all(x.im == 0 for row in real for x in row)
summary['tensor_words_exhausted'] = word_count

tokens = [2, 7, 19]
exponents = set()
for word in product(range(4), repeat=len(tokens)):
    exponent = tuple(int(j in tokens and word[tokens.index(j)] == q + 1)
                     for j in range(20) for q in range(3))
    assert all(sum(exponent[3*j:3*j+3]) <= 1 for j in range(20))
    assert sum(exponent[3*j+1] for j in range(20)) == word.count(2)
    exponents.add(exponent)
assert len(exponents) == 4 ** len(tokens)
summary['noncontiguous_token_exponents'] = len(exponents)

unitaries = [ident(2),
             quaternion_unitary(F(3, 5), F(0), F(4, 5), F(0)),
             quaternion_unitary(F(1, 2), F(1, 2), F(1, 2), F(1, 2)),
             quaternion_unitary(F(1, 3), F(2, 3), F(2, 3), F(0))]
# Also test a unitary with determinant -1, allowed in the orthogonality and
# rotation-transfer leaves and showing that determinant one is redundant there.
unitaries.append(scale(I, unitaries[1]))
rotations = []
for gi, g in enumerate(unitaries):
    assert mul(dagger(g), g) == ident(2)
    assert det2(g) == gauss(-1 if gi == 4 else 1)
    columns = []
    for j in range(1, 4):
        a = mul(mul(g, pauli[j]), dagger(g))
        column = [a[0][1].re, -a[0][1].im, a[0][0].re]
        expanded = scale(0, ident(2))
        for l in range(3):
            expanded = add(expanded, scale(column[l], pauli[l + 1]))
        assert a == expanded
        columns.append(column)
    r = transpose(columns)
    for i in range(3):
        for j in range(3):
            assert sum(r[l][i] * r[l][j] for l in range(3)) == int(i == j)
    rotations.append(r)
    for k in range(4):
        a = operator(k, invariant_coefficients(k))
        t = tensor([g] * k)
        assert mul(t, a) == mul(a, t)
summary['adjoint_coordinate_and_orthogonality_unitaries'] = len(unitaries)
summary['invariant_tensor_commutators'] = 4 * len(unitaries)

# Check the transpose convention on an arbitrary noninvariant polynomial.
g, r = unitaries[1], rotations[1]
words = list(product(range(4), repeat=2))
coefficients = {word: F(n + 1, n % 5 + 1) for n, word in enumerate(words)}
extended = [[F(int(i == 0 and j == 0)) if i == 0 or j == 0
             else r[i-1][j-1] for j in range(4)] for i in range(4)]
transformed = {b: sum(c * extended[b[0]][a[0]] * extended[b[1]][a[1]]
                      for a, c in coefficients.items()) for b in words}
t = tensor([g, g])
assert mul(mul(t, operator(2, coefficients)), dagger(t)) == operator(2, transformed)
v = [[F(2, 3), F(-5, 7), F(3, 11)], [F(5, 2), F(7, 3), F(-11, 5)]]
assert evaluate(transformed, v) == evaluate(coefficients, act(transpose(r), v))
assert evaluate(transformed, v) != evaluate(coefficients, act(r, v))
summary['rotation_substitution_is_transpose'] = 'PASS (opposite convention differs)'

reflection = [[F(1), F(0), F(0)], [F(0), F(-1), F(0)], [F(0), F(0), F(1)]]
for k in range(4):
    p = invariant_coefficients(k)
    v = [[F(j+1, 3), F(j*j+2, 5), F(2*j-1, 7)] for j in range(k)]
    assert all(word.count(2) % 2 == 0 for word in p)
    for r in rotations + [reflection]:
        assert evaluate(p, act(r, v)) == evaluate(p, v)
        for signs in product([-1, 1], repeat=k):
            pv = [[signs[j] * x for x in row] for j, row in enumerate(v)]
            pr = act(r, pv)
            rp = [[signs[j] * x for x in row] for j, row in enumerate(act(r, v))]
            assert pr == rp
            assert evaluate(p, pr) == evaluate(p, pv)
summary['reflection_and_tokenwise_inversion_examples'] = 'PASS (0 through 3 slots)'

cayley_checks = 0
parameters = [(F(0), F(1)), (F(3, 4), F(5, 4)), (F(-3, 4), F(5, 4)),
              (F(4, 3), F(5, 3)), (F(-4, 3), F(5, 3))]
for j in range(1, 4):
    for value, root in parameters:
        a = add(ident(2), scale(-I * value, pauli[j]))
        assert root * root == 1 + value * value
        assert mul(dagger(a), a) == scale(1 + value * value, ident(2))
        assert det2(a) == gauss(1 + value * value)
        g = scale(1 / root, a)
        assert mul(dagger(g), g) == ident(2)
        assert det2(g) == gauss(1)
        for k in range(4):
            ta = tensor([a] * k)
            assert ta == scale(root ** k, tensor([g] * k))
            m = operator(k, invariant_coefficients(k))
            assert mul(m, ta) == mul(ta, m)
            cayley_checks += 1
summary['cayley_tensor_scaling_and_commutators'] = cayley_checks
summary['arithmetic'] = 'exact Gaussian rationals (fractions.Fraction); no floating point'
summary['scope'] = 'Finite consistency checks, not proofs of the universally quantified leaves.'

output = json.dumps(summary, indent=2) + '\n'
Path(__file__).with_name('exact-checks.json').write_text(output)
print(output)
