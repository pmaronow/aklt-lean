"""Independent finite reconstruction of the permitted Lean automaton literals.

Reads only Automaton10Data.lean. This is an external arithmetic cross-check,
not a Lean proof or a comparison with the unavailable archived text file.
"""

import ast
import collections
import hashlib
import json
import re
from pathlib import Path


INPUT = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
SOURCE = INPUT.read_text()
LITERALS = {}
LINE_NUMBERS = {}
for line_number, line in enumerate(SOURCE.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, hexadecimal = match.groups()
        assert name not in LITERALS
        LITERALS[name] = (int(hexadecimal, 16), 4 * len(hexadecimal))
        LINE_NUMBERS[name] = line_number


def read_table(name, width, count):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', SOURCE, re.M)[1]
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
    leaves = []

    def collect(node, offset=0):
        if isinstance(node, ast.Name):
            leaves.append((node.id, offset))
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            collect(node.left, offset)
            collect(node.right, offset)
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant)
            assert isinstance(node.right.value, int) and node.right.value >= 0
            collect(node.left, offset + node.right.value)
        else:
            raise AssertionError(ast.dump(node))

    collect(tree)
    assert len({key for key, _ in leaves}) == len(leaves)
    assert {key for key, _ in leaves} == {key for key in LITERALS if key.startswith(name + '_')}
    packed = 0
    next_offset = 0
    for key, offset in reversed(leaves):
        value, bits = LITERALS[key]
        assert offset == next_offset, (key, offset, next_offset)
        assert value < 1 << bits
        packed += value << offset
        next_offset += bits
    assert packed < 1 << (width * count)
    assert width % 4 == 0 or width == 2
    # One to_bytes conversion avoids repeatedly shifting a twelve-million-bit int.
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    lanes = []
    for index in range(count):
        byte_index, bit_index = divmod(width * index, 8)
        value = int.from_bytes(data[byte_index:byte_index + (bit_index + width + 7) // 8], 'little')
        lanes.append((value >> bit_index) & ((1 << width) - 1))
    # Check the byte-based extraction against Nat-style division and remainder.
    for index in {0, 1, count // 2, count - 2, count - 1}:
        assert lanes[index] == packed // (2 ** (width * index)) % (2 ** width)
    return lanes, dict(leaves), packed.bit_length()


RAW, RAW_OFFSETS, RAW_BITS = read_table('rawClass', 12, 4 ** 10)
REPS, _, _ = read_table('representatives', 20, 3741)
DESTS, _, _ = read_table('destinations', 12, 3741 * 4)
KINDS, _, _ = read_table('edgeKinds', 2, 3741 * 4)
assert all(0 <= a <= 3741 for a in RAW)
assert all(0 <= code < 4 ** 10 for code in REPS)
assert all(0 <= b <= 3741 for b in DESTS)
assert all((b == 0) == (k == 3) for b, k in zip(DESTS, KINDS))

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def move(vertex, direction):
    dx, dy = STEPS[direction]
    return vertex[0] + dx, vertex[1] + dy


def bond(v, w):
    return tuple(sorted((v, w)))


def decode(code):
    return tuple((code // (4 ** (9 - i))) % 4 for i in range(10))


def encode(word):
    return sum(d * 4 ** (9 - i) for i, d in enumerate(word))


def geometry(word):
    vertices = [(0, 0)]
    bonds = []
    for direction in word:
        v = move(vertices[-1], direction)
        bonds.append(bond(vertices[-1], v))
        vertices.append(v)
    return vertices, bonds


def row(word, vertices, bonds):
    used = set(bonds)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    result = []
    for direction in range(4):
        allowed = direction != (word[-1] + 2) % 4 and bond(endpoint, move(endpoint, direction)) not in used
        kind = 2 if revisit else (0 if direction == word[-1] else 1)
        successor_code = encode(word[1:] + (direction,))
        result.append((allowed, kind, successor_code))
    return result


# Generate distinct-unoriented-bond paths independently of the table, as prescribed
# in app-input-contracts.tex:232-237 and 390-401. No first-step restriction is used.
WINDOWS = {}
COUNTS = [0] * 11


def generate(word=(), vertices=((0, 0),), bonds=frozenset(), code=0):
    depth = len(word)
    COUNTS[depth] += 1
    if depth == 10:
        assert code not in WINDOWS
        WINDOWS[code] = (word, vertices, bonds)
        return
    for direction in range(4):
        new_vertex = move(vertices[-1], direction)
        new_bond = bond(vertices[-1], new_vertex)
        if new_bond not in bonds:
            generate(word + (direction,), vertices + (new_vertex,), bonds | {new_bond}, 4 * code + direction)


generate()
assert COUNTS == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert len(WINDOWS) == 60092
assert all((class_id < 3741) == (code in WINDOWS) for code, class_id in enumerate(RAW))
assert set(RAW[code] for code in WINDOWS) == set(range(3741))
REP_ROWS = []
for class_id, code in enumerate(REPS):
    assert code in WINDOWS and RAW[code] == class_id
    word, vertices, bonds = WINDOWS[code]
    assert decode(code) == word and encode(word) == code
    regenerated = row(word, vertices, bonds)
    REP_ROWS.append(regenerated)
    for direction, (allowed, kind, successor_code) in enumerate(regenerated):
        position = 4 * class_id + direction
        assert (DESTS[position] != 0) == allowed
        if allowed:
            assert successor_code in WINDOWS
            assert DESTS[position] - 1 == RAW[successor_code]
            assert KINDS[position] == kind

edge_counts = collections.Counter()
for class_id in range(3741):
    for direction in range(4):
        position = 4 * class_id + direction
        if DESTS[position]:
            edge_counts[KINDS[position]] += 1
assert dict(edge_counts) == {0: 2516, 1: 5032, 2: 1872}

# Test the quotient hypotheses for every raw word, including the equality of
# intrinsic kinds even on inadmissible directions. Stored kind 3 is just a sentinel.
for code, (word, vertices, bonds) in WINDOWS.items():
    class_id = RAW[code]
    for direction, (allowed, kind, successor_code) in enumerate(row(word, vertices, bonds)):
        position = 4 * class_id + direction
        rep_allowed, rep_kind, rep_successor_code = REP_ROWS[class_id][direction]
        assert allowed == rep_allowed == (DESTS[position] != 0)
        assert kind == rep_kind
        if allowed:
            assert successor_code in WINDOWS
            assert kind == KINDS[position]
            assert RAW[successor_code] == RAW[rep_successor_code] == DESTS[position] - 1
            if kind != 2:
                assert word[-1] == REPS[class_id] % 4

report = {
    'source_sha256': hashlib.sha256(SOURCE.encode()).hexdigest(),
    'scope': 'external exact-integer reconstruction, not a kernel-checked Lean proof',
    'counts_depth_0_through_10': COUNTS,
    'raw_packed_bit_length': RAW_BITS,
    'raw_codes_checked': len(RAW),
    'raw_window_direction_pairs_checked': 4 * len(WINDOWS),
    'class_rows_checked': len(REPS),
    'edge_counts_straight_turn_revisit': [edge_counts[i] for i in range(3)],
    'declarations': {},
}
for index in range(560, 565):
    name = f'rawClass_{index}'
    value, bits = LITERALS[name]
    offset = RAW_OFFSETS[name]
    first, last = offset // 12, (offset + bits - 1) // 12
    covered = range(first, last + 1)
    raw_codes = [code for code in covered if code in WINDOWS]
    fully_contained = [code for code in covered if offset <= 12 * code and 12 * code + 12 <= offset + bits]
    # Compare every contributing bit, including fragments of boundary lanes.
    rebuilt = sum(RAW[code] << (12 * (code - first)) for code in covered)
    expected_chunk = (rebuilt >> (offset - 12 * first)) & ((1 << bits) - 1)
    assert expected_chunk == value
    report['declarations'][name] = {
        'line': LINE_NUMBERS[name],
        'bits_allocated': bits,
        'bit_offset': offset,
        'offset_mod_12': offset % 12,
        'intersecting_code_range_inclusive': [first, last],
        'intersecting_lanes': len(covered),
        'fully_contained_lanes': len(fully_contained),
        'valid_raw_windows': len(raw_codes),
        'sentinel_lanes': len(covered) - len(raw_codes),
        'distinct_classes': len({RAW[code] for code in raw_codes}),
        'raw_direction_pairs_checked': 4 * len(raw_codes),
        'first_valid_example': None if not raw_codes else {
            'code': raw_codes[0], 'directions': ''.join('ENWS'[d] for d in decode(raw_codes[0])),
            'class': RAW[raw_codes[0]], 'representative_code': REPS[RAW[raw_codes[0]]],
        },
        'result': 'PASS',
    }

print(json.dumps(report, indent=2))
