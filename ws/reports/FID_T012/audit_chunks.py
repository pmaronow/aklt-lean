"""Read-only arithmetic audit of the five assigned packed-data chunks."""

import ast
import hashlib
import json
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', source
))
literals = {m[1]: int(m[2], 16) for m in literal_matches}
hex_strings = {m[1]: m[2] for m in literal_matches}
raw_names = [f'rawClass_{i}' for i in range(768)]
assert all(name in literals for name in raw_names)
assert all(len(hex_strings[name]) == (4095 if i == 767 else 4096)
           for i, name in enumerate(raw_names))

expression = re.search(r'^noncomputable def rawClass : ℕ := (.*)$', source, re.M)[1]
tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        assert node.id in raw_names
        return literals[node.id], {node.id: 0}
    assert isinstance(node, ast.BinOp)
    left, offsets = evaluate(node.left)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        shift = node.right.value
        assert isinstance(shift, int) and shift >= 0
        return left << shift, {name: offset + shift for name, offset in offsets.items()}
    assert isinstance(node.op, ast.Add)
    right, other_offsets = evaluate(node.right)
    assert not offsets.keys() & other_offsets.keys()
    return left + right, offsets | other_offsets


packed, offsets = evaluate(tree)
assert len(offsets) == 768
joined_hex = ''.join(hex_strings[name] for name in raw_names)
assert packed == int(joined_hex, 16)
assert len(joined_hex) == 3145727
assert offsets['rawClass_767'] == 0
for i in range(767):
    next_name = raw_names[i + 1]
    assert offsets[raw_names[i]] == offsets[next_name] + 4 * len(hex_strings[next_name])


def decode(code):
    return tuple((code // 4 ** (9 - i)) % 4 for i in range(10))


def repeated_bonds(word):
    steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
    x = (0, 0)
    seen = {}
    duplicates = []
    for i, direction in enumerate(word):
        step = steps[direction]
        y = (x[0] + step[0], x[1] + step[1])
        bond = tuple(sorted((x, y)))
        if bond in seen:
            duplicates.append((seen[bond], i))
        else:
            seen[bond] = i
        x = y
    return duplicates


rows = []
all_codes = set()
for i in range(25, 30):
    name = raw_names[i]
    lo_bit = offsets[name]
    width = len(hex_strings[name]) * 4
    hi_bit = lo_bit + width - 1
    first = lo_bit // 12
    last = hi_bit // 12
    assert 0 <= first <= last < 4 ** 10
    # A lane's three hex digits are the stored natural in [0,4095].
    # Slice the reversed lane order directly, then independently check bits.
    values = []
    prefixes = set()
    for code in range(first, last + 1):
        start = len(joined_hex) - 3 * (code + 1)
        h = joined_hex[max(start, 0):start + 3]
        value = int(h, 16)
        assert value == ((packed >> (12 * code)) & 4095)
        assert value == 3741
        values.append(value)
        word = decode(code)
        assert word[:3] == (3, 3, 1)
        assert (1, 2) in repeated_bonds(word)
        prefixes.add(''.join('ENWS'[d] for d in word[:4]))
        all_codes.add(code)
    # Compare all 16,384 bits, including portions of boundary lanes,
    # with the all-invalid (3741) map over these intersecting codes.
    expected_region = sum(3741 << (12 * (code - first))
                          for code in range(first, last + 1))
    expected_chunk = (expected_region >> (lo_bit - 12 * first)) & ((1 << width) - 1)
    assert literals[name] == expected_chunk
    rows.append({
        'declaration': name,
        'source_line': source.count('\n', 0, next(m.start() for m in literal_matches if m[1] == name)) + 1,
        'hex_digits': len(hex_strings[name]),
        'hex_sha256': hashlib.sha256(hex_strings[name].encode()).hexdigest(),
        'bit_interval_inclusive': [lo_bit, hi_bit],
        'intersecting_code_interval_inclusive': [first, last],
        'intersecting_lanes': len(values),
        'boundary_offsets_mod_12': [lo_bit % 12, (hi_bit + 1) % 12],
        'decoded_four_direction_prefixes': sorted(prefixes),
        'distinct_lane_values': sorted(set(values)),
        'all_words_repeat_bond_at_zero_based_indices': [1, 2],
        'all_bits_equal_expected_invalid_marker': True,
    })

print(json.dumps({
    'source': str(SOURCE),
    'all_raw_literal_chunks_read': len(raw_names),
    'exact_shift_add_assembly_matches_hex_concatenation': True,
    'raw_class_hex_digits': len(joined_hex),
    'marker_decimal': 3741,
    'marker_hex': 'e9d',
    'union_code_interval_inclusive': [min(all_codes), max(all_codes)],
    'distinct_codes_checked': len(all_codes),
    'chunks': rows,
}, indent=2))
