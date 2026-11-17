"""Read-only semantic check of assigned Automaton10Data literal chunks.

Only the supplied Lean/paper source tree and Mathlib are review inputs.
This script evaluates the explicit packing expression and independently
reconstructs lattice bonds; it does not consult an external data archive.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+_\d+) : ℕ := 0x([0-9a-f]+)$',
    text, re.M))
literals = {m[1]: int(m[2], 16) for m in literal_matches}


def parse_packing(name):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', text, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expr)
    assert ''.join(tokens) == re.sub(r'\s', '', expr)
    cursor = 0

    def atom():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == '(':
            result = expression()
            assert tokens[cursor] == ')'
            cursor += 1
            return result
        if token.isdecimal():
            return int(token), {}
        return literals[token], {token: 0}

    def expression():
        nonlocal cursor
        value, offsets = atom()
        while cursor < len(tokens) and tokens[cursor] != ')':
            op = tokens[cursor]
            cursor += 1
            rhs, rhs_offsets = atom()
            if op == '<<<':
                assert not rhs_offsets
                value <<= rhs
                offsets = {k: v + rhs for k, v in offsets.items()}
            else:
                assert op == '+' and not (offsets.keys() & rhs_offsets.keys())
                value += rhs
                offsets |= rhs_offsets
        return value, offsets

    value, offsets = expression()
    assert cursor == len(tokens)
    return value, offsets


packed, offsets = parse_packing('rawClass')
sorted_chunks = sorted(offsets, key=offsets.get)
widths = {}
for idx, name in enumerate(sorted_chunks):
    upper = offsets[sorted_chunks[idx+1]] if idx+1 < len(sorted_chunks) else 12 * 4**10
    widths[name] = upper - offsets[name]
    assert literals[name] < 2**widths[name]
    assert (packed >> offsets[name]) & (2**widths[name] - 1) == literals[name]
assert sorted_chunks == [f'rawClass_{i}' for i in reversed(range(768))]


def directions(code):
    return tuple((code >> (2 * (9-i))) & 3 for i in range(10))


def raw_window(code):
    x, y = 0, 0
    used = set()
    for d in directions(code):
        dx, dy = ((1, 0), (0, 1), (-1, 0), (0, -1))[d]
        nxt = x + dx, y + dy
        bond = frozenset(((x, y), nxt))
        if bond in used:
            return False
        used.add(bond)
        x, y = nxt
    return True


results = []
for index in range(405, 410):
    name = f'rawClass_{index}'
    offset, width = offsets[name], widths[name]
    first, last = offset // 12, (offset + width - 1) // 12
    codes = range(first, last + 1)
    lanes = Counter((packed >> (12*code)) & 4095 for code in codes)
    # Avoid repeated extraction from the 12-million-bit integer: each selected
    # chunk is compared to the exact same-width segment of sentinel lanes.
    sentinel_region = sum(3741 << (12*k) for k in range(last-first+1))
    expected = (sentinel_region >> (offset % 12)) % 2**width
    raw_codes = [code for code in codes if raw_window(code)]
    results.append({
        'declaration': name,
        'source_line': text.count('\n', 0, text.index('private noncomputable def ' + name + ' ')) + 1,
        'bit_offset': offset,
        'bit_width': width,
        'bit_offset_mod_12': offset % 12,
        'first_code': first,
        'last_code': last,
        'touched_lanes': len(codes),
        'complete_lane_count': (offset+width)//12 - (offset+11)//12,
        'decoded_lane_counts': dict(lanes),
        'raw_window_count': len(raw_codes),
        'raw_window_examples': raw_codes[:5],
        'equals_sentinel_bit_segment': literals[name] == expected,
        'first_word': ''.join('ENWS'[d] for d in directions(first)),
        'last_word': ''.join('ENWS'[d] for d in directions(last)),
        'literal_sha256': hashlib.sha256(literals[name].to_bytes((width+7)//8, 'big')).hexdigest(),
    })

print(json.dumps({
    'source_characters': len(text),
    'source_lines': len(text.splitlines()),
    'literal_counts': dict(Counter(m[1].rsplit('_', 1)[0] for m in literal_matches)),
    'raw_class_packing': {
        'chunk_count': len(offsets),
        'width_counts': dict(Counter(widths.values())),
        'bits': packed.bit_length(),
        'allocated_bits': sum(widths.values()),
        'no_overlap_or_carry': True,
    },
    'assigned_chunks': results,
}, indent=2))
