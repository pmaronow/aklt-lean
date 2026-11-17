"""Independent integer and lattice check of the supplied Lean literal tables.

Reads only the supplied Automaton10Data.lean. No Lean execution or input writes.
"""

import ast
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
values = {}
trees = {}
literal_widths = {}


def evaluate(node):
    if isinstance(node, ast.Constant):
        assert isinstance(node.value, int) and node.value >= 0
        return node.value
    if isinstance(node, ast.Name):
        return values[node.id]
    assert isinstance(node, ast.BinOp)
    left, right = evaluate(node.left), evaluate(node.right)
    if isinstance(node.op, ast.Add):
        return left + right
    assert isinstance(node.op, ast.LShift)
    return left << right


for name, expression in re.findall(
    r'^(?:private )?noncomputable def (\w+) : ℕ := (.+)$', text, re.M
):
    node = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
    values[name] = evaluate(node)
    trees[name] = node
    if expression.startswith('0x'):
        literal_widths[name] = 4 * (len(expression) - 2)


def offsets(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return offsets(node.left, shift) + offsets(node.right, shift)
    assert isinstance(node.op, ast.LShift)
    return offsets(node.left, shift + evaluate(node.right))


def unpack(name, width, count):
    number = values[name]
    assert number < 1 << (width * count)
    bits = format(number, f'0{width * count}b')
    return [int(bits[i:i + width], 2)
            for i in range(0, len(bits), width)][::-1]


N, Q = 4**10, 3741
raw = unpack('rawClass', 12, N)
representatives = unpack('representatives', 20, Q)
destinations = unpack('destinations', 12, Q * 4)
kinds = unpack('edgeKinds', 2, Q * 4)

# Check the actual shift/add expression, not just apparent string concatenation.
raw_offsets = dict(offsets(trees['rawClass']))
assert len(raw_offsets) == 768
last_bit = 0
for i in reversed(range(768)):
    name = f'rawClass_{i}'
    assert raw_offsets[name] == last_bit
    assert values[name] < 1 << literal_widths[name]
    last_bit += literal_widths[name]
assert last_bit == 12 * N - 4  # the top class has one leading zero hex digit
assert values['rawClass'] == int(''.join(
    format(values[f'rawClass_{i}'], f'0{literal_widths[f"rawClass_{i}"] // 4}x')
    for i in range(768)), 16)

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    assert 0 <= code < N
    return tuple((code // 4**(9 - i)) % 4 for i in range(10))


def edge(x, y):
    return tuple(sorted((x, y)))


def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        x = vertices[-1]
        y = (x[0] + steps[d][0], x[1] + steps[d][1])
        b = edge(x, y)
        assert b not in bonds
        bonds.add(b)
        vertices.append(y)
    return vertices[-1], bonds, set(vertices[:-1])


def row(word, endpoint, bonds, departures):
    answer = []
    for d, step in enumerate(steps):
        y = (endpoint[0] + step[0], endpoint[1] + step[1])
        allowed = d != (word[-1] + 2) % 4 and edge(endpoint, y) not in bonds
        kind = 2 if endpoint in departures else 0 if d == word[-1] else 1
        answer.append((allowed, kind))
    return answer


rep_words = [decode(c) for c in representatives]
rep_rows = []
edge_counts = Counter()
for a, word in enumerate(rep_words):
    assert raw[representatives[a]] == a
    computed = row(word, *geometry(word))
    rep_rows.append(computed)
    for d, (allowed, kind) in enumerate(computed):
        destination, stored_kind = destinations[4*a+d], kinds[4*a+d]
        assert 0 <= destination <= Q
        assert (destination == 0) == (stored_kind == 3)
        assert allowed == (destination != 0)
        if allowed:
            assert stored_kind == kind
            edge_counts[kind] += 1
            successor_code = (representatives[a] % 4**9) * 4 + d
            assert raw[successor_code] == destination - 1
assert [edge_counts[i] for i in range(3)] == [2516, 5032, 1872]

valid = bytearray(N)
depth_counts = [0] * 11
class_sizes = Counter()
checked_directions = 0


def visit(word, code, vertices, bonds):
    global checked_directions
    depth_counts[len(word)] += 1
    endpoint = vertices[-1]
    if len(word) == 10:
        valid[code] = 1
        a = raw[code]
        assert 0 <= a < Q
        class_sizes[a] += 1
        computed = row(word, endpoint, bonds, set(vertices[:-1]))
        for d, (allowed, kind) in enumerate(computed):
            # Includes kind compatibility on inadmissible directions as well.
            assert rep_rows[a][d] == (allowed, kind)
            if allowed:
                assert kinds[4*a+d] == kind
                successor_code = (code % 4**9) * 4 + d
                assert raw[successor_code] == destinations[4*a+d] - 1
                assert raw[successor_code] < Q
                if kind != 2:
                    assert rep_words[a][-1] == word[-1]
            checked_directions += 1
        return
    for d, step in enumerate(steps):
        y = (endpoint[0] + step[0], endpoint[1] + step[1])
        b = edge(endpoint, y)
        if b not in bonds:
            bonds.add(b)
            visit(word + (d,), code * 4 + d, vertices + [y], bonds)
            bonds.remove(b)


visit((), 0, [(0, 0)], set())
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert len(class_sizes) == Q
assert all(0 <= a <= Q and (a < Q) == bool(valid[c])
           for c, a in enumerate(raw))
print('Raw counts at depths 1..10:', depth_counts[1:])
print('All 1,048,576 codes: valid iff class < 3741; every invalid code has sentinel 3741.')
print('All 3,741 representatives: valid, project to own class, and match stored rows.')
print(f'All {checked_directions:,} raw-word/direction comparisons pass, including forbidden-direction kinds.')
print('All admitted successor classes and non-revisit final directions agree.')
print('Labelled edge counts (straight, turn, revisit):', [edge_counts[i] for i in range(3)])
for i in range(155, 160):
    name = f'rawClass_{i}'
    low = raw_offsets[name]
    high = low + literal_widths[name] - 1
    codes = range(low // 12, high // 12 + 1)
    valid_count = sum(valid[c] for c in codes)
    print(f'{name}: bits {low}..{high}; touches codes {codes.start}..{codes.stop-1}; '
          f'{valid_count} valid, {len(codes)-valid_count} invalid.')
print('PASS')
