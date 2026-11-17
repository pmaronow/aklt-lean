"""Independent finite reconstruction of the supplied Lean memory-ten data.
Reads only the permitted Lean input; no archived witness or checker is used.
"""
from pathlib import Path
import collections
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
hex_widths = {}
line_numbers = {}
for line_number, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        hex_widths[name] = len(digits) * 4
        line_numbers[name] = line_number
assert len(literals) == 768 + 5 + 11 + 2

# Parse the actual fully parenthesized Lean packing expressions, including
# every shift amount, rather than assuming a fixed chunk order or alignment.
def packing(name):
    match = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M)
    expression = match[1]
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    pos = 0
    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            result = expr()
            assert tokens[pos] == ')'
            pos += 1
            return result
        if token.isdigit():
            return int(token), []
        assert token in literals
        return literals[token], [(token, 0)]
    def expr():
        nonlocal pos
        value, leaves = atom()
        while pos < len(tokens) and tokens[pos] != ')':
            op = tokens[pos]
            pos += 1
            right, other = atom()
            if op == '<<<':
                assert not other
                value <<= right
                leaves = [(leaf, offset + right) for leaf, offset in leaves]
            else:
                assert op == '+'
                assert value & right == 0, 'Overlapping nonzero summands'
                value += right
                leaves += other
        return value, leaves
    value, leaves = expr()
    assert pos == len(tokens)
    assert len({leaf for leaf, _ in leaves}) == len(leaves)
    cursor = 0
    for leaf, offset in sorted(leaves, key=lambda item: item[1]):
        assert offset == cursor, (name, leaf, offset, cursor)
        cursor += hex_widths[leaf]
    return value, dict(leaves), cursor

raw, offsets, raw_width = packing('rawClass')
# A second construction validates the parser's result and the order of every
# raw chunk directly against concatenation of its hexadecimal digits.
raw_hex = ''.join(re.search(
    r'^private noncomputable def rawClass_' + str(j) + r' : ℕ := 0x([0-9a-fA-F]+)$',
    source, re.M
)[1] for j in range(768))
assert raw == int(raw_hex, 16)
reps, _, rep_width = packing('representatives')
dest, _, dest_width = packing('destinations')
kinds, _, kind_width = packing('edgeKinds')
# Hex numerals omit their leading zero nibbles; reserve complete high lanes.
assert raw_width <= 12 * 4**10
assert rep_width <= 20 * 3741
assert dest_width <= 12 * 3741 * 4
assert kind_width <= 2 * 3741 * 4

# Byte extraction avoids repeatedly dividing a twelve-million-bit integer.
def lanes(value, width, count):
    data = value.to_bytes((width * count + 7) // 8, 'little') + b'\0\0\0\0'
    result = []
    for index in range(count):
        bit = width * index
        start = bit // 8
        word = int.from_bytes(data[start:start + 4], 'little')
        result.append((word >> (bit % 8)) & ((1 << width) - 1))
    return result

classes = lanes(raw, 12, 4**10)
representatives = lanes(reps, 20, 3741)
destinations = lanes(dest, 12, 3741 * 4)
edge_kinds = lanes(kinds, 2, 3741 * 4)
assert all(0 <= value <= 3741 for value in classes)
assert all(value < 4**10 for value in representatives)
assert all(0 <= value <= 3741 for value in destinations)
assert all((d == 0) == (k == 3) for d, k in zip(destinations, edge_kinds))

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
def bond(x, y):
    return tuple(sorted((x, y)))
def add(x, y):
    return x[0] + y[0], x[1] + y[1]
def decode(code):
    return tuple((code // 4**(9 - index)) % 4 for index in range(10))
def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        nxt = add(vertices[-1], STEPS[d])
        bonds.add(bond(vertices[-1], nxt))
        vertices.append(nxt)
    return vertices, bonds

# Generate Omega_j directly by adjoining each of the four absolute directions
# unless the resulting unoriented bond has already been used.
valid = {}
depth_counts = [0] * 11
def extend(word, code, vertices, used):
    depth = len(word)
    depth_counts[depth] += 1
    if depth == 10:
        valid[code] = (word, vertices, used)
        return
    x = vertices[-1]
    for d, step in enumerate(STEPS):
        y = add(x, step)
        edge = bond(x, y)
        if edge not in used:
            extend(word + (d,), 4 * code + d, vertices + (y,), used | {edge})
extend((), 0, ((0, 0),), set())
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((value < 3741) == (code in valid) for code, value in enumerate(classes))
assert set(classes[code] for code in valid) == set(range(3741))
for a, code in enumerate(representatives):
    assert code in valid and classes[code] == a

edge_counts = collections.Counter()
for a in range(3741):
    for d in range(4):
        if destinations[4 * a + d] != 0:
            edge_counts[edge_kinds[4 * a + d]] += 1
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

checks = collections.Counter()
for code, (word, vertices, used) in valid.items():
    a = classes[code]
    rword, rvertices, rused = valid[representatives[a]]
    revisit = vertices[-1] in vertices[:-1]
    representative_revisit = rvertices[-1] in rvertices[:-1]
    for d, step in enumerate(STEPS):
        allowed = d != (word[-1] + 2) % 4 and bond(vertices[-1], add(vertices[-1], step)) not in used
        rallowed = d != (rword[-1] + 2) % 4 and bond(rvertices[-1], add(rvertices[-1], step)) not in rused
        kind = 2 if revisit else 0 if d == word[-1] else 1
        rkind = 2 if representative_revisit else 0 if d == rword[-1] else 1
        assert allowed == rallowed
        assert kind == rkind, ('Kind mismatch even on inadmissible direction', code, d)
        assert allowed == (destinations[4 * a + d] != 0), (code, a, d)
        checks['admissibility_comparisons'] += 1
        checks['representative_kind_comparisons_all_directions'] += 1
        if allowed:
            successor = (code % 4**9) * 4 + d
            assert successor in valid
            assert classes[successor] == destinations[4 * a + d] - 1
            assert kind == edge_kinds[4 * a + d]
            checks['admissible_kind_and_successor_comparisons'] += 1
            if kind != 2:
                assert word[-1] == representatives[a] % 4
                checks['nonrevisit_arrival_comparisons'] += 1

# Detailed evidence for exactly the five assigned literal chunks. A chunk may
# contain only part of its first or last 12-bit lane, so test all intersecting
# lanes and retain the neighboring chunks during extraction.
chunks = []
for j in range(575, 580):
    name = f'rawClass_{j}'
    offset = offsets[name]
    width = hex_widths[name]
    lo = offset // 12
    hi = (offset + width - 1) // 12
    raw_codes = [code for code in range(lo, hi + 1) if code in valid]
    chunks.append({
        'declaration': name,
        'source_line': line_numbers[name],
        'hex_digits': width // 4,
        'bit_offset': offset,
        'bit_end_inclusive': offset + width - 1,
        'intersecting_code_interval_inclusive': [lo, hi],
        'intersecting_codes': hi - lo + 1,
        'raw_words': len(raw_codes),
        'invalid_word_sentinel_lanes': hi - lo + 1 - len(raw_codes),
        'distinct_class_values': len({classes[code] for code in raw_codes}),
        'first_valid_example': None if not raw_codes else {
            'code': raw_codes[0],
            'word_ENWS': ''.join('ENWS'[d] for d in decode(raw_codes[0])),
            'class': classes[raw_codes[0]],
            'representative_code': representatives[classes[raw_codes[0]]],
        },
        'literal_sha256_ascii_hex': hashlib.sha256(re.search(
            r'^private noncomputable def ' + name + r' : ℕ := 0x([0-9a-fA-F]+)$', source, re.M
        )[1].encode()).hexdigest(),
    })

result = {
    'input': str(SOURCE),
    'arithmetic': 'Exact Python integers; actual Lean packing AST parsed; all finite lanes and every raw transition reconstructed.',
    'packed_widths_bits': {'rawClass': raw_width, 'representatives': rep_width, 'destinations': dest_width, 'edgeKinds': kind_width},
    'raw_window_counts_by_depth_1_to_10': depth_counts[1:],
    'all_code_lanes_checked': len(classes),
    'raw_window_count': len(valid),
    'class_count': 3741,
    'edge_counts': dict(sorted(edge_counts.items())),
    'comparisons': dict(checks),
    'assigned_chunks': chunks,
    'result': 'All assertions passed',
}
print(json.dumps(result, indent=2))
