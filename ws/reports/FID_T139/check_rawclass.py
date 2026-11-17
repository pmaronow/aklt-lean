"""Read-only arithmetic audit of the five assigned packed table fragments."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_pattern = re.compile(
    r'^private noncomputable def rawClass_(\d+) : ℕ := 0x([0-9a-f]+)$', re.M
)
literals = {int(m[1]): m[2] for m in literal_pattern.finditer(text)}
assert sorted(literals) == list(range(768))
expression = re.search(r'^noncomputable def rawClass : ℕ := (.*)$', text, re.M)[1]
token_pattern = re.compile(r'rawClass_\d+|<<<|\d+|[()+]')
tokens = token_pattern.findall(expression)
assert ''.join(tokens) == re.sub(r'\s+', '', expression)
position = 0


def parse():
    """Expand the fully parenthesized sum/shift tree into leaf bit offsets."""
    global position
    token = tokens[position]
    position += 1
    if token.startswith('rawClass_'):
        return {int(token[9:]): 0}
    assert token == '('
    left = parse()
    operation = tokens[position]
    position += 1
    if operation == '<<<':
        shift = int(tokens[position])
        position += 1
        result = {key: offset + shift for key, offset in left.items()}
    else:
        assert operation == '+'
        right = parse()
        assert not left.keys() & right.keys()
        result = left | right
    assert tokens[position] == ')'
    position += 1
    return result


offsets = parse()
assert position == len(tokens)
assert sorted(offsets) == list(range(768))
widths = {key: len(value) * 4 for key, value in literals.items()}
cursor = 0
for key in sorted(offsets, key=offsets.get):
    assert offsets[key] == cursor  # No gaps or overlapping summands; no carries.
    assert int(literals[key], 16) < 1 << widths[key]
    cursor += widths[key]
assert cursor == 12 * 4**10 - 4  # Four omitted leading zero bits, not missing lanes.
packed_hex = ''.join(literals[key] for key in sorted(offsets, key=offsets.get, reverse=True))
packed_hex = packed_hex.zfill(3 * 4**10)


def lane(code):
    end = len(packed_hex) - 3 * code
    return int(packed_hex[end - 3:end], 16)


def decode(code):
    return tuple((code // 4**power) % 4 for power in range(9, -1, -1))


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def is_raw(directions):
    vertex = (0, 0)
    used = set()
    for direction in directions:
        dx, dy = STEPS[direction]
        next_vertex = vertex[0] + dx, vertex[1] + dy
        bond = frozenset((vertex, next_vertex))
        if bond in used:
            return False
        used.add(bond)
        vertex = next_vertex
    return True


results = []
all_codes = set()
for key in range(660, 665):
    offset, width = offsets[key], widths[key]
    phase = offset % 12
    count = (phase + width + 11) // 12
    periodic_marker = 3741 * ((1 << (12 * count)) - 1) // ((1 << 12) - 1)
    expected = (periodic_marker >> phase) & ((1 << width) - 1)
    assert int(literals[key], 16) == expected  # Checks every assigned literal bit.
    low, high = offset // 12, (offset + width - 1) // 12
    codes = list(range(low, high + 1))
    all_codes.update(codes)
    assert all(decode(code)[:2] == (0, 2) for code in codes)
    assert all(not is_raw(decode(code)) for code in codes)
    assert all(lane(code) == 3741 for code in codes)  # Includes boundary neighbors.
    results.append({
        'declaration': f'rawClass_{key}',
        'lean_line': text[:literal_pattern.search(text, text.index(f'private noncomputable def rawClass_{key} ')).start()].count('\n') + 1,
        'bit_interval_half_open': [offset, offset + width],
        'offset_mod_12': phase,
        'hex_digits': len(literals[key]),
        'hex_text_sha256': hashlib.sha256(literals[key].encode()).hexdigest(),
        'overlapping_code_interval_inclusive': [low, high],
        'overlapping_lane_count': len(codes),
        'decoded_lane_values': dict(Counter(lane(code) for code in codes)),
        'raw_windows': 0,
        'exact_periodic_marker_match': True,
    })

# Independently regenerate the finite raw-window set using the paper's recursion.
raw_codes = []
depth_counts = [0] * 11


def generate(depth, code, vertex, used):
    depth_counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        return
    for direction, (dx, dy) in enumerate(STEPS):
        next_vertex = vertex[0] + dx, vertex[1] + dy
        bond = frozenset((vertex, next_vertex))
        if bond not in used:
            used.add(bond)
            generate(depth + 1, 4 * code + direction, next_vertex, used)
            used.remove(bond)


generate(0, 0, (0, 0), set())
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert not set(raw_codes) & all_codes
assert is_raw((0,) * 10)  # The raw domain is inhabited.
assert lane(0) < 3741

evidence = {
    'source': str(SOURCE),
    'assembled_storage_bits': cursor,
    'logical_lane_count': 4**10,
    'lane_width': 12,
    'invalid_window_marker': 3741,
    'distinct_codes_touched': len(all_codes),
    'all_touched_words_begin_with': 'E,W',
    'regenerated_raw_counts_depth_1_through_10': depth_counts[1:],
    'results': results,
}
Path('check_evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps(evidence, indent=2))
