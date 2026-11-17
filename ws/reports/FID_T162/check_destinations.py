"""Read-only audit of the packed Lean automaton against the paper's raw rules."""

import ast
from collections import Counter
import hashlib
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_pattern = r'^private noncomputable def (\w+_\d+) : ℕ := (0x[0-9a-fA-F]+)$'
literals = {name: int(hexadecimal, 16) for name, hexadecimal in re.findall(literal_pattern, text, re.M)}


def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id], {node.id: 0}
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value, {}
    if isinstance(node, ast.BinOp):
        left, locations = evaluate(node.left)
        right, other = evaluate(node.right)
        if isinstance(node.op, ast.Add):
            assert not set(locations).intersection(other)
            return left + right, locations | other
        if isinstance(node.op, ast.LShift):
            assert not other
            return left << right, {name: offset + right for name, offset in locations.items()}
    raise ValueError(ast.dump(node))


def packed(name, width, count):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.*)$', text, re.M)[1]
    value, locations = evaluate(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    assert value < 1 << (width * count)
    data = value.to_bytes((width * count + 7) // 8, 'little')
    lanes = []
    for i in range(count):
        bit = i * width
        byte, offset = divmod(bit, 8)
        take = (width + offset + 7) // 8
        lanes.append((int.from_bytes(data[byte:byte + take], 'little') >> offset) & ((1 << width) - 1))
    return value, locations, lanes


_, _, classes = packed('rawClass', 12, 4**10)
_, _, representatives = packed('representatives', 20, 3741)
destinations, destination_locations, stored = packed('destinations', 12, 3741 * 4)
_, _, kinds = packed('edgeKinds', 2, 3741 * 4)

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(x, y):
    return tuple(sorted((x, y)))


def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def geometry(word):
    vertices = [(0, 0)]
    bonds = []
    for d in word:
        x, y = vertices[-1]
        dx, dy = STEPS[d]
        v = x + dx, y + dy
        bonds.append(bond(vertices[-1], v))
        vertices.append(v)
    return vertices, set(bonds), len(set(bonds)) == 10


def row(code):
    word = decode(code)
    vertices, bonds, valid = geometry(word)
    assert valid
    x, y = vertices[-1]
    is_revisit = vertices[-1] in vertices[:-1]
    destinations_row, kinds_row = [], []
    for d, (dx, dy) in enumerate(STEPS):
        if d == (word[-1] + 2) % 4 or bond((x, y), (x + dx, y + dy)) in bonds:
            destinations_row.append(0)
            kinds_row.append(3)
        else:
            successor = (code % 4**9) * 4 + d
            assert classes[successor] < 3741
            destinations_row.append(classes[successor] + 1)
            kinds_row.append(2 if is_revisit else (0 if d == word[-1] else 1))
    return destinations_row, kinds_row, word[-1]


# Independently enumerate all raw words by adding exactly one unused bond.
raw_codes = []
counts = [0] * 11


def visit(depth, code, position, used):
    counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        return
    x, y = position
    for d, (dx, dy) in enumerate(STEPS):
        nxt = x + dx, y + dy
        edge = bond(position, nxt)
        if edge not in used:
            used.add(edge)
            visit(depth + 1, code * 4 + d, nxt, used)
            used.remove(edge)


visit(0, 0, (0, 0), set())
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert raw_codes == sorted(set(raw_codes))
raw_set = set(raw_codes)
assert all(0 <= a <= 3741 and ((a < 3741) == (code in raw_set)) for code, a in enumerate(classes))
assert set(classes[code] for code in raw_codes) == set(range(3741))
assert all(code < 4**10 and code in raw_set and classes[code] == a for a, code in enumerate(representatives))
assert all(0 <= v <= 3741 for v in stored)
assert all((v == 0) == (k == 3) for v, k in zip(stored, kinds))

expected, expected_kinds, arrivals = [], [], []
for code in representatives:
    destination_row, kind_row, arrival = row(code)
    expected.extend(destination_row)
    expected_kinds.extend(kind_row)
    arrivals.append(arrival)

destination_errors = [(i // 4, i % 4, v, expected[i]) for i, v in enumerate(stored) if v != expected[i]]
kind_errors = [(i // 4, i % 4, v, expected_kinds[i]) for i, v in enumerate(kinds) if v != expected_kinds[i]]
assert not destination_errors, destination_errors[:10]
assert not kind_errors, kind_errors[:10]

raw_comparisons = 0
for code in raw_codes:
    a = classes[code]
    regenerated, regenerated_kinds, arrival = row(code)
    assert regenerated == stored[4 * a:4 * a + 4], (code, a, regenerated)
    # The paper compares kind even for inadmissible directions. In a raw row
    # those kinds are independent of the sentinel stored in an absent edge.
    rep_vertices, _, _ = geometry(decode(representatives[a]))
    vertices, _, _ = geometry(decode(code))
    for d in range(4):
        raw_kind = 2 if vertices[-1] in vertices[:-1] else (0 if d == arrival else 1)
        rep_kind = 2 if rep_vertices[-1] in rep_vertices[:-1] else (0 if d == arrivals[a] else 1)
        assert raw_kind == rep_kind, (code, a, d)
        if regenerated[d] != 0:
            assert regenerated_kinds[d] == kinds[4 * a + d]
            if regenerated_kinds[d] != 2:
                assert arrival == arrivals[a]
        raw_comparisons += 1

assert Counter(k for k, v in zip(kinds, stored) if v) == {0: 2516, 1: 5032, 2: 1872}

expected_value = sum(v << (12 * i) for i, v in enumerate(expected))
print('Raw depth counts:', counts[1:])
print('Raw labelled direction comparisons:', raw_comparisons)
print('Representative labelled rows:', len(stored))
print('All raw coverage, representative, successor, kind, and arrival checks passed.')
print('Admissible kinds:', dict(sorted(Counter(k for k, v in zip(kinds, stored) if v).items())))
for chunk in range(5):
    name = f'destinations_{chunk}'
    offset = destination_locations[name]
    value = literals[name]
    assert value < 1 << 16384
    expected_chunk = (expected_value >> offset) & ((1 << 16384) - 1)
    assert value == expected_chunk
    lower, upper = offset // 12, (offset + 16383) // 12
    print(f'{name}: offset={offset}, width=16384, intersected lanes={lower}..{upper}, '
          f'classes={lower // 4}..{upper // 4}, '
          f'sha256_big_endian_2048_bytes={hashlib.sha256(value.to_bytes(2048, "big")).hexdigest()}')
print('PASS: all five complete literals equal the independently regenerated packed slices.')
