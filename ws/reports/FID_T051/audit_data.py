"""Read-only reconstruction of the assigned packed-data blocks."""
from pathlib import Path
from collections import Counter
import json
import re

LEAN = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = LEAN.read_text()
hex_values = dict(re.findall(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', text))


def parse_packing(name):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.*)$', text, re.M)[1]
    tokens = re.findall(r'<<<|[()+]|\w+', expression)
    cursor = 0

    def atom():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == '(':
            result = expr()
            assert tokens[cursor] == ')'
            cursor += 1
            return result
        assert token in hex_values
        return [(token, 0)]

    def expr():
        nonlocal cursor
        result = atom()
        while cursor < len(tokens) and tokens[cursor] != ')':
            operator = tokens[cursor]
            cursor += 1
            if operator == '<<<':
                shift = int(tokens[cursor])
                cursor += 1
                result = [(leaf, offset + shift) for leaf, offset in result]
            else:
                assert operator == '+'
                result += atom()
        return result

    leaves = expr()
    assert cursor == len(tokens)
    sorted_leaves = sorted(leaves, key=lambda leaf: leaf[1])
    next_offset = 0
    for leaf, offset in sorted_leaves:
        assert offset == next_offset, (leaf, offset, next_offset)
        next_offset += len(hex_values[leaf]) * 4
    return dict(leaves), ''.join(hex_values[leaf] for leaf, _ in reversed(sorted_leaves))


offsets, packed_hex = parse_packing('rawClass')
assert len(offsets) == 768
packed_value = int(packed_hex, 16)
lane_count = 4**10
# Pad omitted leading zeros before splitting into complete 12-bit lanes.
full_hex = packed_hex.zfill(lane_count * 3)
assert len(full_hex) == lane_count * 3
classes = [int(full_hex[i:i + 3], 16) for i in range(0, len(full_hex), 3)][::-1]

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def directions(code):
    return [(code // 4**(9 - i)) % 4 for i in range(10)]


def raw_word(code):
    vertex = (0, 0)
    used = set()
    for direction in directions(code):
        dx, dy = steps[direction]
        successor = (vertex[0] + dx, vertex[1] + dy)
        bond = tuple(sorted((vertex, successor)))
        if bond in used:
            return False
        used.add(bond)
        vertex = successor
    return True


summaries = []
for i in range(220, 225):
    name = f'rawClass_{i}'
    offset = offsets[name]
    width = 4 * len(hex_values[name])
    low = offset // 12
    high = (offset + width - 1) // 12
    codes = range(low, high + 1)
    entries = Counter(classes[code] for code in codes)
    valid_codes = [code for code in codes if raw_word(code)]
    assert entries == {3741: len(codes)}, entries
    assert not valid_codes, valid_codes
    prefix_counts = Counter(''.join(map(str, directions(code)[:4])) for code in codes)
    summaries.append(dict(
        declaration=name, line=text[:text.index(f'private noncomputable def {name} :')].count('\n') + 1,
        bits=[offset, offset + width - 1], code_range=[low, high],
        overlapping_lanes=len(codes), invalid_sentinel_lanes=entries[3741],
        valid_raw_words=len(valid_codes), first_word=directions(low),
        last_word=directions(high), four_direction_prefixes=dict(prefix_counts)))

# Independent enumeration follows the paper's append-unused-bond recursion.
raw_codes = set()
counts = [0] * 11


def enumerate_raw(depth, vertex, used, code):
    counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for direction, (dx, dy) in enumerate(steps):
        successor = (vertex[0] + dx, vertex[1] + dy)
        bond = tuple(sorted((vertex, successor)))
        if bond not in used:
            used.add(bond)
            enumerate_raw(depth + 1, successor, used, code * 4 + direction)
            used.remove(bond)


enumerate_raw(0, (0, 0), set(), 0)
coverage_mismatches = sum((value < 3741) != (code in raw_codes)
                          for code, value in enumerate(classes))
out_of_range = sum(value > 3741 for value in classes)
assert coverage_mismatches == 0
assert out_of_range == 0
result = dict(assigned=summaries, raw_window_counts=counts[1:],
              global_coverage_mismatches=coverage_mismatches,
              global_out_of_range_lanes=out_of_range,
              represented_class_count=len({classes[code] for code in raw_codes}),
              raw_packed_hex_digits=len(packed_hex),
              leading_zero_bits=12 * lane_count - len(packed_hex) * 4)
print(json.dumps(result, indent=2))
