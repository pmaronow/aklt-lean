"""Read-only reconstruction of the literal automaton and its paper contract."""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
OUT = Path('/home/ubuntu/aklt/reports/FID_T034')
text = SOURCE.read_text()
literals = {}
line_numbers = {}
expressions = {}
for number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        literals[match[1]] = match[2]
        line_numbers[match[1]] = number
    match = re.fullmatch(r'noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        expressions[match[1]] = match[2]


def terms(node, offset=0):
    if isinstance(node, ast.Name):
        assert node.id in literals
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return terms(node.left, offset) + terms(node.right, offset)
    assert isinstance(node.op, ast.LShift) and isinstance(node.right, ast.Constant)
    return terms(node.left, offset + node.right.value)


def unpack(name, width, length):
    tree = ast.parse(expressions[name].replace('<<<', '<<'), mode='eval')
    leaves = terms(tree.body)
    assert len(leaves) == len(set(n for n, _ in leaves))
    assert [n for n, _ in leaves] == [f'{name}_{i}' for i in range(len(leaves))]
    ordered = sorted(leaves, key=lambda v: v[1])
    assert ordered[0][1] == 0
    for (n, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert int(literals[n], 16).bit_length() <= next_offset - offset
    assert int(literals[ordered[-1][0]], 16).bit_length() + ordered[-1][1] <= width * length
    packed = sum(int(literals[n], 16) << offset for n, offset in leaves)
    data = packed.to_bytes((width * length + 7) // 8, 'little')
    values = []
    for index in range(length):
        bit = width * index
        byte, remainder = divmod(bit, 8)
        size = (remainder + width + 7) // 8
        values.append((int.from_bytes(data[byte:byte + size], 'little') >> remainder) & ((1 << width) - 1))
    return values, dict(leaves), packed.bit_length()


N = 4 ** 10
raw, offsets, bit_length = unpack('rawClass', 12, N)
representatives, _, _ = unpack('representatives', 20, 3741)
destinations, _, _ = unpack('destinations', 12, 3741 * 4)
kinds, _, _ = unpack('edgeKinds', 2, 3741 * 4)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
direction_names = 'ENWS'
counts = [0] * 11
windows = {}


def edge(a, b):
    return tuple(sorted((a, b)))


def generate(word, code, positions, bonds):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        windows[code] = (word, positions, bonds)
        return
    x, y = positions[-1]
    for d, (dx, dy) in enumerate(steps):
        target = (x + dx, y + dy)
        bond = edge(positions[-1], target)
        if bond not in bonds:
            generate(word + (d,), 4 * code + d, positions + (target,), bonds | {bond})


generate((), 0, ((0, 0),), frozenset())
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]


def word_label(code):
    return ''.join(direction_names[(code // (4 ** (9 - i))) % 4] for i in range(10))


def row(code):
    word, positions, bonds = windows[code]
    endpoint = positions[-1]
    revisit = endpoint in positions[:-1]
    result = []
    for d, (dx, dy) in enumerate(steps):
        allowed = d != (word[-1] + 2) % 4 and edge(endpoint, (endpoint[0] + dx, endpoint[1] + dy)) not in bonds
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        successor = (code % (4 ** 9)) * 4 + d
        if allowed:
            assert successor in windows
        result.append((allowed, kind, successor))
    return result


coverage_errors = []
for code, value in enumerate(raw):
    if value > 3741 or ((value < 3741) != (code in windows)):
        coverage_errors.append((code, value, code in windows))

representative_errors = []
for a, code in enumerate(representatives):
    if code not in windows or raw[code] != a:
        representative_errors.append((a, code, raw[code] if code < N else None))

row_errors = []
arrival_errors = []
compatibility_errors = []
for code in windows:
    a = raw[code]
    if a >= 3741:
        row_errors.append((code, a, 'invalid class'))
        continue
    representative = representatives[a]
    if representative not in windows:
        row_errors.append((code, a, 'invalid representative'))
        continue
    original_row = row(code)
    representative_row = row(representative)
    for d, (allowed, kind, successor) in enumerate(original_row):
        index = 4 * a + d
        stored_allowed = destinations[index] != 0
        if stored_allowed != allowed:
            row_errors.append((code, a, d, 'admissibility', allowed, stored_allowed))
        if allowed:
            if kinds[index] != kind:
                row_errors.append((code, a, d, 'kind', kind, kinds[index]))
            if destinations[index] - 1 != raw[successor]:
                row_errors.append((code, a, d, 'successor', raw[successor], destinations[index] - 1))
            if kind != 2 and code % 4 != representative % 4:
                arrival_errors.append((code, a, d, code % 4, representative % 4))
        rep_allowed, rep_kind, rep_successor = representative_row[d]
        if allowed != rep_allowed or kind != rep_kind or (allowed and raw[successor] != raw[rep_successor]):
            compatibility_errors.append((code, a, d))

storage_errors = []
edge_counts = Counter()
for a in range(3741):
    for d in range(4):
        destination, kind = destinations[4 * a + d], kinds[4 * a + d]
        if destination > 3741 or ((destination == 0) != (kind == 3)) or (destination != 0 and kind >= 3):
            storage_errors.append((a, d, destination, kind))
        if destination != 0:
            edge_counts[kind] += 1

selected = {}
for i in range(135, 140):
    name = f'rawClass_{i}'
    offset = offsets[name]
    bits = len(literals[name]) * 4
    first, last = offset // 12, (offset + bits - 1) // 12
    affected = set(range(first, last + 1))
    valid = sorted(affected & windows.keys())
    invalid = sorted(affected - windows.keys())
    phase = offset % 12
    lane_count = (phase + bits + 11) // 12
    repeated_sentinel = 3741 * ((1 << (12 * lane_count)) - 1) // 4095
    expected_literal = (repeated_sentinel >> phase) & ((1 << bits) - 1)
    assert int(literals[name], 16) == expected_literal
    assert 13 * 4**8 <= first <= last < 14 * 4**8
    related = [r for r in row_errors + arrival_errors + compatibility_errors if r[0] in affected]
    selected[name] = {
        'line': line_numbers[name],
        'hex_sha256': hashlib.sha256(literals[name].encode()).hexdigest(),
        'bit_offset': offset,
        'bits': bits,
        'exact_sentinel_pattern': True,
        'all_words_start_south_north': True,
        'first_code': first,
        'last_code': last,
        'first_lane_local_bit': offset % 12,
        'valid_windows': len(valid),
        'invalid_words': len(invalid),
        'classes': sorted(set(raw[c] for c in valid)),
        'coverage_errors': [v for v in coverage_errors if v[0] in affected],
        'row_errors': related,
        'first_valid': None if not valid else (valid[0], word_label(valid[0]), raw[valid[0]]),
        'last_valid': None if not valid else (valid[-1], word_label(valid[-1]), raw[valid[-1]]),
        'first_invalid': None if not invalid else (invalid[0], word_label(invalid[0]), raw[invalid[0]]),
        'lanes': [(c, raw[c]) for c in valid],
    }

result = {
    'raw_literal_count': len(offsets),
    'raw_packed_bit_length': bit_length,
    'raw_counts': counts,
    'raw_value_range': [min(raw), max(raw)],
    'sentinel_count': raw.count(3741),
    'coverage_errors': coverage_errors[:20],
    'coverage_error_count': len(coverage_errors),
    'representative_errors': representative_errors[:20],
    'representative_error_count': len(representative_errors),
    'row_errors': row_errors[:20],
    'row_error_count': len(row_errors),
    'arrival_error_count': len(arrival_errors),
    'compatibility_error_count': len(compatibility_errors),
    'storage_error_count': len(storage_errors),
    'edge_counts': dict(edge_counts),
    'selected': selected,
}
(OUT / 'check_results.json').write_text(json.dumps(result, indent=2) + '\n')
for k, v in result.items():
    if k == 'selected':
        for name, details in v.items():
            print(name, json.dumps({a: b for a, b in details.items() if a not in ('classes', 'lanes')}, sort_keys=True))
    else:
        print(k, v)
