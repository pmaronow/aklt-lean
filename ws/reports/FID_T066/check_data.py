"""Read-only reconstruction of the finite data used by the assigned declarations."""

import ast
import collections
import json
import re
from pathlib import Path

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', source, re.M
    )
}


def packed_table(name):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.*)$', source, re.M)[1]
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body

    def evaluate(node):
        if isinstance(node, ast.Name):
            return literals[node.id], {node.id: 0}
        assert isinstance(node, ast.BinOp)
        left, offsets = evaluate(node.left)
        if isinstance(node.op, ast.LShift):
            shift = ast.literal_eval(node.right)
            return left << shift, {key: offset + shift for key, offset in offsets.items()}
        assert isinstance(node.op, ast.Add)
        right, right_offsets = evaluate(node.right)
        assert not offsets.keys() & right_offsets.keys()
        assert left & right == 0, 'Unexpected overlap/carry in packed assembly'
        return left + right, offsets | right_offsets

    value, offsets = evaluate(tree)
    assert set(offsets) == {key for key in literals if key.startswith(name + '_')}
    data = value.to_bytes((value.bit_length() + 7) // 8, 'little')

    def lane(width, index):
        bit = width * index
        byte = bit // 8
        part = int.from_bytes(data[byte:byte + (width + 14) // 8], 'little')
        return (part >> (bit % 8)) & ((1 << width) - 1)

    return lane, offsets, value.bit_length()


raw, offsets, raw_bits = packed_table('rawClass')
representative, _, _ = packed_table('representatives')
destination, _, _ = packed_table('destinations')
kind, _, _ = packed_table('edgeKinds')
steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def decode(code):
    return [(code >> (2 * (9 - i))) & 3 for i in range(10)]


def path(word):
    vertices = [(0, 0)]
    bonds = []
    for direction in word:
        x, y = vertices[-1]
        dx, dy = steps[direction]
        end = (x + dx, y + dy)
        bonds.append(tuple(sorted((vertices[-1], end))))
        vertices.append(end)
    return vertices, bonds


raw_words = {}
depth_counts = [0] * 11


def generate(word, code, vertices, bonds):
    depth_counts[len(word)] += 1
    if len(word) == 10:
        raw_words[code] = (word, vertices, bonds)
        return
    x, y = vertices[-1]
    for direction, (dx, dy) in enumerate(steps):
        end = (x + dx, y + dy)
        bond = tuple(sorted(((x, y), end)))
        if bond not in bonds:
            generate(word + [direction], code * 4 + direction,
                     vertices + [end], bonds | {bond})


generate([], 0, [(0, 0)], set())
coverage_errors = []
for code in range(4**10):
    value = raw(12, code)
    if value > 3741 or (value < 3741) != (code in raw_words):
        coverage_errors.append((code, value, code in raw_words))

assigned = []
for index in range(295, 300):
    name = f'rawClass_{index}'
    low = offsets[name]
    high = low + 16384 - 1
    first, last = low // 12, high // 12
    affected_raw = [code for code in range(first, last + 1) if code in raw_words]
    departures = []
    for code in range(first, last + 1):
        vertices, bonds = path(decode(code))
        duplicate = next(((i, bonds.index(bonds[i])) for i in range(10)
                          if bonds[i] in bonds[:i]), None)
        if duplicate is not None:
            departures.append(duplicate)
    expected = 0
    assert affected_raw == ([638975] if index == 299 else [])
    for code in range(first, last + 1):
        expected |= (218 if code == 638975 else 3741) << (12 * (code - first))
    expected = (expected >> (low - 12 * first)) & ((1 << 16384) - 1)
    assigned.append({
        'declaration': name, 'bit_range': [low, high], 'code_range': [first, last],
        'overlapping_lanes': last - first + 1,
        'raw_words': [(code, raw(12, code), decode(code)) for code in affected_raw],
        'literal_matches_expected_bits': literals[name] == expected,
        'differing_bits': (literals[name] ^ expected).bit_count(),
        'difference_positions_within_chunk': [i for i in range(16384)
                                              if ((literals[name] ^ expected) >> i) & 1],
        'decoded_lane_values': dict(collections.Counter(raw(12, c) for c in range(first, last + 1))),
        'first_duplicate_bond_indices': dict(collections.Counter(str(x) for x in departures)),
    })

representative_errors = []
representatives = []
for a in range(3741):
    code = representative(20, a)
    representatives.append(code)
    if code >= 4**10 or code not in raw_words or raw(12, code) != a:
        representative_errors.append((a, code, raw(12, code)))

transition_errors = []
edge_counts = collections.Counter()
for code, (word, vertices, bonds) in raw_words.items():
    a = raw(12, code)
    if a >= 3741:
        transition_errors.append(('class_out_of_range', code, a))
        continue
    end = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        bond = tuple(sorted((end, (end[0] + dx, end[1] + dy))))
        admissible = d != (word[-1] + 2) % 4 and bond not in bonds
        k = 2 if end in vertices[:-1] else (0 if d == word[-1] else 1)
        stored_dest = destination(12, a * 4 + d)
        stored_kind = kind(2, a * 4 + d)
        if (stored_dest != 0) != admissible:
            transition_errors.append(('admissibility', code, a, d, stored_dest))
        if admissible:
            successor = (code % 4**9) * 4 + d
            if stored_kind != k or stored_dest != raw(12, successor) + 1:
                transition_errors.append(('kind_or_successor', code, a, d, stored_kind, k,
                                          stored_dest, raw(12, successor)))
            if k != 2 and representatives[a] % 4 != word[-1]:
                transition_errors.append(('arrival', code, a, d))

row_errors = []
for a in range(3741):
    for d in range(4):
        target, k = destination(12, a * 4 + d), kind(2, a * 4 + d)
        if target > 3741 or (target == 0) != (k == 3):
            row_errors.append((a, d, target, k))
        if target:
            edge_counts[k] += 1

result = {
    'parsed_literal_count': len(literals), 'raw_table_bit_length': raw_bits,
    'depth_counts': depth_counts,
    'coverage_error_count': len(coverage_errors), 'coverage_errors_first': coverage_errors[:20],
    'assigned': assigned,
    'representative_error_count': len(representative_errors),
    'representative_errors_first': representative_errors[:20],
    'transition_error_count': len(transition_errors), 'transition_errors_first': transition_errors[:20],
    'row_error_count': len(row_errors), 'edge_counts': dict(edge_counts),
}
print(json.dumps(result, indent=2))
