"""Independent finite checks, reading only the assigned Lean input."""
import ast
import re
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

source = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean').read_text()
packed = {}

def literal(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.Name):
        return packed[node.id]
    if isinstance(node, ast.BinOp):
        a, b = literal(node.left), literal(node.right)
        if isinstance(node.op, ast.Add):
            return a + b
        if isinstance(node.op, ast.LShift):
            return a << b
    raise ValueError(ast.dump(node))

for name, expr in re.findall(r'^(?:private )?noncomputable def (\w+) : ℕ := (.+)$', source, re.M):
    packed[name] = literal(ast.parse(expr.replace('<<<', '<<'), mode='eval').body)

def lanes(name, width, count):
    # Byte extraction avoids shifting a million-lane integer at every index.
    data = packed[name].to_bytes((width * count + 7) // 8, 'little')
    result = []
    for i in range(count):
        bit = width * i
        start, offset = divmod(bit, 8)
        value = int.from_bytes(data[start:start + (offset + width + 7) // 8], 'little')
        result.append((value >> offset) & ((1 << width) - 1))
    return result

raw = lanes('rawClass', 12, 4**10)
reps = lanes('representatives', 20, 3741)
dest = lanes('destinations', 12, 4 * 3741)
kinds = lanes('edgeKinds', 2, 4 * 3741)
assert max(raw) == 3741
assert sum(a < 3741 for a in raw) == 60092
assert max(dest) <= 3741
assert all((d == 0) == (k == 3) for d, k in zip(dest, kinds))

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))

def move(x, d):
    v = steps[d]
    return (x[0] + v[0], x[1] + v[1])

def bond(x, y):
    return (x, y) if x < y else (y, x)

def decode(code):
    return tuple((code // 4**(9-i)) % 4 for i in range(10))

def walk(word):
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        y = move(vertices[-1], d)
        b = bond(vertices[-1], y)
        assert b not in bonds
        bonds.add(b)
        vertices.append(y)
    return vertices, bonds

for a, code in enumerate(reps):
    assert code < 4**10
    assert raw[code] == a
    walk(decode(code))

raw_count = 0
length_counts = [0] * 11

def check_raw(word, vertices, bonds, code):
    global raw_count
    length_counts[len(word)] += 1
    if len(word) < 10:
        for d in range(4):
            y = move(vertices[-1], d)
            b = bond(vertices[-1], y)
            if b not in bonds:
                check_raw(word + (d,), vertices + [y], bonds | {b}, code*4 + d)
        return
    raw_count += 1
    a = raw[code]
    assert a < 3741
    x = vertices[-1]
    for d in range(4):
        allowed = d != (word[-1] + 2) % 4 and bond(x, move(x, d)) not in bonds
        index = 4*a + d
        assert (dest[index] != 0) == allowed
        if allowed:
            k = 2 if x in vertices[:-1] else (0 if d == word[-1] else 1)
            assert kinds[index] == k
            next_code = (code % 4**9)*4 + d
            assert dest[index] - 1 == raw[next_code]
            if k != 2:
                assert reps[a] % 4 == word[-1]

check_raw((), [(0, 0)], set(), 0)
assert raw_count == 60092
assert length_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert Counter(k for d, k in zip(dest, kinds) if d) == {0: 2516, 1: 5032, 2: 1872}
print('Supplied quotient: all 60092 raw words, 3741 representatives, and labelled transitions checked.')
print('Edge counts: straight=2516, turn=5032, revisit=1872.')

def prefix_counts(target, first_direction):
    counts = [0, 0, 0]  # nodes, surviving prefixes, short first hits

    def visit(x, used, n):
        counts[0] += 1
        if x == target:
            counts[2] += 1
            return
        if n == 12:
            counts[1] += 1
            return
        for d in (range(4) if n else [first_direction]):
            y = move(x, d)
            b = bond(x, y)
            if y != (0, 0) and b not in used:
                visit(y, used | {b}, n + 1)

    visit((-1, 0), set(), 0)
    return counts

cases = [('B/N', (1, 0), 1), ('B/W', (1, 0), 2),
         ('C/N', (0, 1), 1), ('C/W', (0, 1), 2), ('C/S', (0, 1), 3)]
expected = [[139985, 89150, 937], [161929, 103257, 922],
            [105025, 66947, 715], [155673, 99168, 1036], [145485, 92748, 861]]
for case, expected_counts in zip(cases, expected):
    label, target, direction = case
    actual = prefix_counts(target, direction)
    assert actual == expected_counts
    print(f'{label}: nodes={actual[0]}, surviving={actual[1]}, first_hits={actual[2]}')

assert (2*70+1)**2 == 19881
assert 4*3741*(19881-2) == 297469356
rho = F(993015, 10**6)
h_c = F(5404319552844595, 4503599627370496)
assert 0 < rho < 1 and h_c > 1
assert F(2*351207554 + 290599163, 10**9) < rho
assert F(527872005 + 380754375 + 273048088, 10**9) < F(119, 100) < rho*h_c
D = 2**48
ceil = lambda x: -(-x.numerator // x.denominator)
assert [ceil(D*x) for x in [F(1000, 961*3), F(200, 187*3), F(1, 3), F(1, 5)]] == [97632666219444, 100347585280092, 93824992236886, 56294995342132]
print('Square size, local-row count, exact assembly inequalities, and diagonal ceilings checked.')
