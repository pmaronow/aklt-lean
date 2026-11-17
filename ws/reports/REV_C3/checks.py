#!/usr/bin/env python3
"""Small, independent exact checks for the Appendix D proof.

No certificate search, floating arithmetic, external packages, or input writes.
Run from this directory with python3 checks.py.  This checks formulas and
examples, not the full H1 certificate family (whose theorem is outside scope).
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import re


@dataclass(frozen=True)
class Q5:
    """The exact field Q(sqrt(5))."""
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))

    @staticmethod
    def coerce(other):
        return other if isinstance(other, Q5) else Q5(other)

    def __add__(self, other):
        other = self.coerce(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        den = other.a ** 2 - 5 * other.b ** 2
        assert den != 0
        return self * Q5(other.a / den, -other.b / den)

    def __pow__(self, exponent):
        assert exponent >= 0
        answer = Q5(1)
        for _ in range(exponent):
            answer = answer * self
        return answer


def prod(values, start=1):
    for value in values:
        start *= value
    return start


def moment(word, status):
    if len(word) == 0:
        return F(1)
    if len(word) % 2:
        return F(0)
    if len(word) == 2:
        return F(int(word[0] == word[1]), 3 if status == 'U' else 5)
    assert len(word) == 4
    i, j, k, l = word
    numerator = ((i == j and k == l) + (i == k and j == l)
                 + (i == l and j == k))
    return F(numerator, 15 if status == 'U' else 25)


phi = Q5(F(1, 2), F(1, 2))
norm2 = phi + 2
raw = []
for s, t in product((-1, 1), repeat=2):
    raw.extend([(Q5(0), Q5(s), t * phi),
                (Q5(s), t * phi, Q5(0)),
                (t * phi, Q5(0), Q5(s))])
assert len(set(raw)) == 12
assert all(sum(v * v for v in n) == norm2 for n in raw)
gram = [[sum(a * b for a, b in zip(n, m)) / norm2
         for m in raw] + [Q5(0)] for n in raw]
gram.append([Q5(0)] * 13)


def check_statements():
    plan = Path('/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md').read_text()
    interfaces = Path('/home/ubuntu/aklt/reports/REV-PLAN/interfaces.tex').read_text()
    text = Path('app-local-operator.tex').read_text()
    appendix = plan.split('## Appendix D. Operator-only verification of (H1)\n', 1)[1]
    appendix = appendix.split('# Exhaustive baseline statement audit', 1)[0]
    blocks = re.findall(r'```latex\n(.*?)```', appendix, re.S)
    labels = []
    for block in blocks:
        label = re.search(r'\\label\{([^}]+)\}', block).group(1)
        assert block.rstrip() in text, label
        exported = re.search(
            r'\\begin\{(lemma|definition|corollary|proposition)\}\\label\{'
            + re.escape(label) + r'\}.*?\\end\{\1\}', interfaces, re.S)
        assert exported and exported.group(0) == block.rstrip(), label
        labels.append(label)
    actual = re.findall(
        r'\\begin\{(?:lemma|definition|corollary|proposition)\}\\label\{([^}]+)\}',
        text)
    assert actual == labels and len(labels) == 12
    assert text.count(r'\begin{proof}') == text.count(r'\end{proof}') == 9
    assert '% PROOF ' not in text
    external = sorted(set(re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', text)) - set(labels))
    assert external == ['d:moment', 'd:pattern', 'h:H1', 'l:35',
                        'l:finitefacts', 'l:moments']
    print('PASS: 12 verbatim statements matching PLAN.md and interfaces.tex, in order;')
    print('      9 proofs and 6 external labels.')


def check_moments_and_leaves():
    count = 0
    for length in range(5):
        for word in product(range(3), repeat=length):
            value = sum(prod((n[j] for j in word), Q5(1)) for n in raw) / 12
            if length % 2:
                assert value == Q5(0)
            else:
                value /= norm2 ** (length // 2)
                assert value == Q5(moment(word, 'U'))
                diluted = Q5(1) if not word else value * F(3, 5)
                assert diluted == Q5(moment(word, 'D'))
            count += 1

    def add(p, q):
        return [
            (p[i] if i < len(p) else F(0)) + (q[i] if i < len(q) else F(0))
            for i in range(max(len(p), len(q)))]

    def mul(p, q):
        result = [F(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                result[i + j] += a * b
        return result

    u = add(mul([F(1), F(1, 3)], [F(1), F(1, 3)]),
            [F(-8, 9), F(-8, 9)])
    d = add(mul([F(1), F(1, 5)], [F(1), F(1, 5)]),
            [F(-18, 25), F(-18, 25)])
    assert u == [F(1, 9), F(-2, 9), F(1, 9)]
    assert d == [F(7, 25), F(-8, 25), F(1, 25)]
    print(f'PASS: {count} exact icosahedral moments through degree 4; both corner identities.')


def coefficients(status, bonds, fields, pairs):
    """The proof's explicit sum of local moments, with no quadrature."""
    k = len(fields)
    result = {}
    insertions = [(None, F(1))] + [((x, y, j), F(1, 3))
                                 for x, y in pairs for j in range(3)]
    for a in product(range(4), repeat=k):
        for b in product(range(4), repeat=len(bonds)):
            for h, weight in insertions:
                words = {x: [] for x in status}
                term = weight
                for index, (x, radius, _) in zip(a, fields):
                    if index:
                        term *= radius
                        words[x].append(index - 1)
                for index, (x, y) in zip(b, bonds):
                    if index:
                        words[x].append(index - 1)
                        words[y].append(index - 1)
                if h:
                    x, y, j = h
                    words[x].append(j)
                    words[y].append(j)
                assert all(len(w) <= 4 for w in words.values())
                for x in status:
                    term *= moment(words[x], status[x])
                if term:
                    result[a] = result.get(a, F(0)) + term
    return {a: x for a, x in result.items() if x}


def polynomial_at_ico(coeffs, pins):
    result = Q5(0)
    for a, coefficient in coeffs.items():
        degree = sum(index != 0 for index in a)
        assert degree % 2 == 0
        numerator = prod((raw[pin][index - 1]
                          for pin, index in zip(pins, a) if index), Q5(coefficient))
        result += numerator / norm2 ** (degree // 2)
    return result


def finite_sum(status, bonds, fields, pairs, pins):
    """Independent direct finite-law sum in Q(sqrt(5)); no moment tensors."""
    sites = list(status)
    result = Q5(0)
    supports = [range(12 if status[x] == 'U' else 13) for x in sites]
    for values in product(*supports):
        n = dict(zip(sites, values))
        value = Q5(1)
        for x in sites:
            value *= (F(1, 12) if status[x] == 'U' else
                      F(2, 5) if n[x] == 12 else F(1, 20))
        for x, y in bonds:
            value *= 1 + gram[n[x]][n[y]]
        for (x, radius, _), pin in zip(fields, pins):
            value *= 1 + radius * gram[n[x]][pin]
        value *= 1 + sum(gram[n[x]][n[y]] / 3 for x, y in pairs)
        result += value
    return result


def zeros(n, m=None):
    return [[0 for _ in range(n if m is None else m)] for _ in range(n)]


def transpose(a):
    return [list(c) for c in zip(*a)]


def matmul(a, b):
    if not a or not b:
        return []
    bt = transpose(b)
    return [[sum(x * y for x, y in zip(row, col)) for col in bt] for row in a]


def real_operator(coeffs, k, inverted):
    """Sparse signed-Pauli action; phases are integers modulo four."""
    result = zeros(2 ** k)
    for a, coefficient in coeffs.items():
        assert sum(index == 2 for index in a) % 2 == 0
        if sum(a[i] != 0 for i in inverted) % 2:
            coefficient = -coefficient
        for col in range(2 ** k):
            bits = [(col >> (k - 1 - i)) & 1 for i in range(k)]
            phase = 0
            for i, index in enumerate(a):
                if index == 2:
                    phase += 1 if bits[i] == 0 else 3
                elif index == 3 and bits[i]:
                    phase += 2
                if index in (1, 2):
                    bits[i] ^= 1
            phase %= 4
            assert phase in (0, 2)
            row = sum(bit << (k - 1 - i) for i, bit in enumerate(bits))
            result[row][col] += coefficient if phase == 0 else -coefficient
    return result


def sector_basis(k, pair_status, sign):
    """In these tests, the sole pair (if present) occupies the last two slots."""
    singles = k - (2 if pair_status else 0)
    groups = [[[(0, 1)], [(1, 1)]] for _ in range(singles)]
    if pair_status:
        groups.append([[(0, 1)], [(1, 1), (2, 1)], [(3, 1)]] if sign == '+'
                      else [[(1, 1), (2, -1)]])
    basis = []
    for local_choices in product(*groups):
        column = [(0, 1)]
        for i, local in enumerate(local_choices):
            width = 1 if i < singles else 2
            column = [(row * (2 ** width) + bits, value * coefficient)
                      for row, value in column for bits, coefficient in local]
        weight = k - 2 * column[0][0].bit_count()
        if weight == singles % 2:
            basis.append(column)
    return basis


def form(matrix, basis):
    return [[sum(a * matrix[i][j] * b for i, a in left for j, b in right)
             for right in basis] for left in basis]


def check_reconstruction():
    cases = [
        ('scalar', {'e': 'D'}, [], [], [], None),
        ('one-tip', {'e': 'D'}, [], [('e', F(3, 5), 0)], [], None),
    ]
    for corner in ('U', 'D'):
        radius = F(1, 2) if corner == 'U' else F(1, 3)
        # Unreduced one-bond corner, and the corresponding reduced core.
        cases.extend([
            (f'{corner}-leaf-unreduced', {'e': 'U', 'z': corner}, [('e', 'z')],
             [('e', F(3, 5), 0), ('z', F(1), 0), ('z', F(1), 0)], [], corner),
            (f'{corner}-leaf-reduced', {'e': 'U'}, [],
             [('e', F(3, 5), 0), ('e', radius, 0)], [], None),
            (f'{corner}-two-bond', {'e': 'U', 'n': 'U', 'z': corner},
             [('e', 'z'), ('n', 'z')],
             [('e', F(3, 5), 0), ('n', F(3, 5), 0),
              ('z', F(1), 0), ('z', F(1), 0)], [('e', 'n')], corner),
        ])
    forms_checked = 0
    for name, status, bonds, fields, pairs, corner in cases:
        k = len(fields)
        cur = coefficients(status, bonds, fields, pairs)
        nxt = coefficients(status, bonds, fields, [])
        pins = [((3 * i + 1) % 12) for i in range(k)]
        assert polynomial_at_ico(cur, pins) == finite_sum(status, bonds, fields, pairs, pins), name
        assert polynomial_at_ico(nxt, pins) == finite_sum(status, bonds, fields, [], pins), name
        denominator = (15 ** sum(s == 'U' for s in status.values())
                       * 25 ** sum(s == 'D' for s in status.values())
                       * prod(radius.denominator for _, radius, _ in fields))
        tc = {a: 3 * denominator * c for a, c in cur.items()}
        tn = {a: 5 * denominator * c for a, c in nxt.items()}
        assert all(c.denominator == 1 for c in list(tc.values()) + list(tn.values()))
        # Invert an entire group: one single if present, otherwise the pair.
        inverted = {0} if k - (2 if corner else 0) else set(range(k))
        oc = real_operator(tc, k, inverted)
        on = real_operator(tn, k, inverted)
        assert oc == transpose(oc) and on == transpose(on)
        raising = zeros(2 ** k)
        weights = [k - 2 * i.bit_count() for i in range(2 ** k)]
        for j in range(2 ** k):
            for bit in range(k):
                if j & (1 << bit):
                    raising[j ^ (1 << bit)][j] = 1
        for op in (oc, on):
            assert all(op[i][j] * (weights[i] - weights[j]) == 0
                       for i in range(2 ** k) for j in range(2 ** k))
            assert matmul(op, raising) == matmul(raising, op)
            assert matmul(op, transpose(raising)) == matmul(transpose(raising), op)
            if corner:
                def swap(index):
                    return index ^ 3 if index & 3 in (1, 2) else index
                if corner == 'U':
                    assert all(op[i][swap(j)] == op[i][j]
                               for i in range(2 ** k) for j in range(2 ** k))
                else:
                    assert all(op[swap(i)][swap(j)] == op[i][j]
                               for i in range(2 ** k) for j in range(2 ** k))
        fc = {a: cur.get(a, F(0)) - F(187, 200) * nxt.get(a, F(0))
              for a in cur.keys() | nxt.keys()}
        of = real_operator({a: c for a, c in fc.items() if c}, k, inverted)
        signs = ('+', '-') if corner == 'D' else ('+',)
        for sign in signs:
            basis = sector_basis(k, corner, sign)
            ac, an, hf = form(oc, basis), form(on, basis), form(of, basis)
            assert all(5 * 200 * ac[i][j] - 3 * 187 * an[i][j]
                       == 15 * denominator * 200 * hf[i][j]
                       for i in range(len(basis)) for j in range(len(basis)))
            forms_checked += 1
    print(f'PASS: {len(cases)} core networks against direct finite sums; denominators,')
    print(f'      Pauli symmetries/support, and positive-scale reconstruction in {forms_checked} sectors.')


def determinant(matrix):
    a = [[F(x) for x in row] for row in matrix]
    answer = F(1)
    for j in range(len(a)):
        nonzero = next((i for i in range(j, len(a)) if a[i][j]), None)
        if nonzero is None:
            return F(0)
        if nonzero != j:
            a[j], a[nonzero] = a[nonzero], a[j]
            answer = -answer
        pivot = a[j][j]
        answer *= pivot
        for i in range(j + 1, len(a)):
            ratio = a[i][j] / pivot
            for l in range(j + 1, len(a)):
                a[i][l] -= ratio * a[j][l]
    return answer


def check_gram_bareiss():
    for n in range(7):
        l0 = [[(i + 2 * j) % 5 - 2 if j <= i else 0 for j in range(n)]
              for i in range(n)]
        # Force a singular Gram factor as well as the n=0 case.
        if n:
            l0[-1] = [0] * n
        e0 = [[((i + j) % 3 - 1) if i != j else 0 for j in range(n)] for i in range(n)]
        for i in range(n):
            e0[i][i] = 1 + sum(abs(x) for x in e0[i])
        gram0 = matmul(l0, transpose(l0))
        g, d, scale = 3, 2, 3
        ell = [[d * scale * x for x in row] for row in l0]
        matrix = [[e0[i][j] + g * d * gram0[i][j] for j in range(n)] for i in range(n)]
        gram1 = matmul(ell, transpose(ell))
        residual = [[d * scale ** 2 * matrix[i][j] - g * gram1[i][j]
                     for j in range(n)] for i in range(n)]
        assert all(residual[i][j] == d * scale ** 2 * e0[i][j]
                   for i in range(n) for j in range(n))
        assert all(residual[i][i] > sum(abs(residual[i][j]) for j in range(n) if j != i)
                   for i in range(n))
        a = [row[:] for row in matrix]
        previous = 1
        for j in range(n):
            pivot = a[j][j]
            assert pivot == determinant([row[:j + 1] for row in matrix[:j + 1]]) > 0
            for i in range(j + 1, n):
                for l in range(j + 1, n):
                    numerator = pivot * a[i][l] - a[i][j] * a[j][l]
                    assert numerator % previous == 0
                    a[i][l] = numerator // previous
            previous = pivot
    print('PASS: Gram/residual witnesses with singular L and nonunit scales, sizes 0--6;')
    print('      exact Bareiss divisions and pivots equal independent leading determinants.')


if __name__ == '__main__':
    check_statements()
    check_moments_and_leaves()
    check_reconstruction()
    check_gram_bareiss()
