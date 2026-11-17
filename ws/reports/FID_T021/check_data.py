"""Read-only reconstruction of the paper's memory-ten data contract.

Uses only the supplied Lean source, and mirrors its natural-number packing.
Run with Python 3; no Lean processes or third-party packages are needed.
"""

import ast
import hashlib
import json
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
TOTAL_BITS = {'rawClass': 12 * 4**10, 'representatives': 20 * 3741,
              'destinations': 12 * 4 * 3741, 'edgeKinds': 2 * 4 * 3741}
tables = {}
offsets_by_name = {}
literals_by_name = {}


def offsets(node):
    if isinstance(node, ast.Name):
        return {node.id: 0}
    assert isinstance(node, ast.BinOp), ast.dump(node)
    if isinstance(node.op, ast.Add):
        left, right = offsets(node.left), offsets(node.right)
        assert left.keys().isdisjoint(right)
        return left | right
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant)
    assert isinstance(node.right.value, int) and node.right.value >= 0
    return {key: val + node.right.value for key, val in offsets(node.left).items()}


for family, total_bits in TOTAL_BITS.items():
    chunks = [(int(i), h) for i, h in re.findall(
        rf'^private noncomputable def {family}_(\d+) : ℕ := 0x([0-9a-f]+)$', text, re.M)]
    assert [i for i, _ in chunks] == list(range(len(chunks)))
    expression = re.search(rf'^noncomputable def {family} : ℕ := (.+)$', text, re.M).group(1)
    actual_offsets = offsets(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    literal_bits = sum(4 * len(h) for _, h in chunks)
    assert literal_bits <= total_bits
    assert all(len(h) == 4096 for _, h in chunks[:-1])
    expected_offsets = {f'{family}_{i}': max(0, literal_bits - 16384 * (i + 1)) for i, _ in chunks}
    assert actual_offsets == expected_offsets, family
    packed = 0
    for i, h in chunks:
        name = f'{family}_{i}'
        value = int(h, 16)
        width = 4 * len(h)
        assert width > 0 and value.bit_length() <= width
        packed += value << actual_offsets[name]
        literals_by_name[name] = value
    assert packed.bit_length() <= total_bits
    tables[family] = packed.to_bytes((total_bits + 7) // 8, 'little')
    offsets_by_name |= actual_offsets


def lane(family, width, index):
    bit = width * index
    byte, skip = divmod(bit, 8)
    value = int.from_bytes(tables[family][byte:byte + (skip + width + 7) // 8], 'little')
    return (value >> skip) & ((1 << width) - 1)


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
NAMES = 'ENWS'
raw_words = {}
counts = [0] * 11


def bond(a, b):
    return tuple(sorted((a, b)))


def generate(word=(), code=0, endpoint=(0, 0), used=None):
    if used is None:
        used = set()
    counts[len(word)] += 1
    if len(word) == 10:
        assert code not in raw_words
        raw_words[code] = word
        return
    for direction, (dx, dy) in enumerate(STEPS):
        next_vertex = (endpoint[0] + dx, endpoint[1] + dy)
        edge = bond(endpoint, next_vertex)
        if edge not in used:
            used.add(edge)
            generate(word + (direction,), 4 * code + direction, next_vertex, used)
            used.remove(edge)


generate()
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
raw_map = [lane('rawClass', 12, code) for code in range(4**10)]
coverage_failures = [code for code, cls in enumerate(raw_map)
                     if cls > 3741 or ((cls < 3741) != (code in raw_words))]
assert not coverage_failures, coverage_failures[:10]


def raw_row(word):
    endpoint = (0, 0)
    used, departures = set(), set()
    for direction in word:
        departures.add(endpoint)
        dx, dy = STEPS[direction]
        next_vertex = (endpoint[0] + dx, endpoint[1] + dy)
        used.add(bond(endpoint, next_vertex))
        endpoint = next_vertex
    revisit = endpoint in departures
    rows = []
    for direction, (dx, dy) in enumerate(STEPS):
        next_vertex = (endpoint[0] + dx, endpoint[1] + dy)
        allowed = direction != (word[-1] + 2) % 4 and bond(endpoint, next_vertex) not in used
        kind = 2 if revisit else (0 if direction == word[-1] else 1)
        rows.append((allowed, kind))
    return rows


representatives = [lane('representatives', 20, a) for a in range(3741)]
representative_rows = []
for a, code in enumerate(representatives):
    assert code < 4**10 and code in raw_words and raw_map[code] == a, (a, code)
    representative_rows.append(raw_row(raw_words[code]))

edge_counts = Counter()
for a, rep in enumerate(representatives):
    for direction in range(4):
        allowed, kind = representative_rows[a][direction]
        destination = lane('destinations', 12, a * 4 + direction)
        stored_kind = lane('edgeKinds', 2, a * 4 + direction)
        assert destination <= 3741
        assert (destination == 0) == (stored_kind == 3)
        assert (destination != 0) == allowed
        if allowed:
            assert stored_kind == kind
            successor_code = (rep % 4**9) * 4 + direction
            assert destination - 1 == raw_map[successor_code]
            edge_counts[kind] += 1
assert [edge_counts[k] for k in range(3)] == [2516, 5032, 1872]

# Check the projection's raw admissibility, kind (also on excluded directions),
# allowed successors, and non-revisit final directions against each representative.
for code, word in raw_words.items():
    a = raw_map[code]
    rep = representatives[a]
    rows = raw_row(word)
    for direction, (allowed, kind) in enumerate(rows):
        assert (allowed, kind) == representative_rows[a][direction], (code, a, direction)
        if allowed:
            successor_code = (code % 4**9) * 4 + direction
            assert raw_map[successor_code] == lane('destinations', 12, a * 4 + direction) - 1
            if kind != 2:
                assert word[-1] == rep % 4

result = {
    'raw_counts_depth_1_to_10': counts[1:],
    'raw_coverage_mismatches': len(coverage_failures),
    'representatives_checked': len(representatives),
    'raw_rows_checked': len(raw_words),
    'edge_counts_straight_turn_revisit': [edge_counts[k] for k in range(3)],
    'chunks': [],
}

for i in range(70, 75):
    name = f'rawClass_{i}'
    offset, width = offsets_by_name[name], 16384
    first, last = offset // 12, (offset + width - 1) // 12
    valid_codes = [code for code in range(first, last + 1) if code in raw_words]
    expected = 0
    # Form a second bit stream directly from enumerated raw words and the sentinel,
    # then intersect each 12-bit lane with this literal's precise bit interval.
    for code in range(first, last + 1):
        cls = raw_map[code] if code in raw_words else 3741
        relative = 12 * code - offset
        if relative >= 0:
            expected |= cls << relative
        else:
            expected |= cls >> -relative
    expected &= (1 << width) - 1
    assert expected == literals_by_name[name], name
    result['chunks'].append({
        'name': name, 'source_line': 15 + 2 * i,
        'least_bit': offset, 'greatest_bit': offset + width - 1,
        'first_code_intersected': first, 'last_code_intersected': last,
        'first_lane_offset_within_literal': 12 * first - offset,
        'last_lane_bits_in_literal': offset + width - 12 * last,
        'intersected_codes': last - first + 1,
        'raw_codes': len(valid_codes), 'nonraw_codes': last - first + 1 - len(valid_codes),
        'literal_matches_regeneration': True,
        'sha256_of_2048_little_endian_bytes': hashlib.sha256(
            literals_by_name[name].to_bytes(2048, 'little')).hexdigest(),
        'first_valid_codes': [
            {'code': c, 'word': ''.join(NAMES[d] for d in raw_words[c]), 'class': raw_map[c]}
            for c in valid_codes[:3]],
        'last_valid_codes': [
            {'code': c, 'word': ''.join(NAMES[d] for d in raw_words[c]), 'class': raw_map[c]}
            for c in valid_codes[-3:]],
    })

print(json.dumps(result, indent=2))
