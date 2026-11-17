"""Read-only audit of the supplied Lean literals against the paper's raw model."""

from collections import Counter
from pathlib import Path
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
literal_text = {}
locations = {}
for number, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', line)
    if match:
        name, value = match.groups()
        literals[name] = int(value, 16)
        literal_text[name] = value[2:]
        locations[name] = number
assert sum(name.startswith('rawClass_') for name in literals) == 768


def packed_expression(name):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', source, re.M)[1]
    tokens = re.findall(r'<<<|[()+]|\w+', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    cursor = 0

    def atom():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == '(':
            value, offsets = expr()
            assert tokens[cursor] == ')'
            cursor += 1
            return value, offsets
        if token.isdigit():
            return int(token), {}
        return literals[token], {token: 0}

    def expr():
        nonlocal cursor
        value, offsets = atom()
        # The exported expressions parenthesize every binary operation.
        if cursor < len(tokens) and tokens[cursor] != ')':
            operation = tokens[cursor]
            cursor += 1
            right, right_offsets = atom()
            if operation == '+':
                assert not offsets.keys() & right_offsets.keys()
                value += right
                offsets.update(right_offsets)
            else:
                assert operation == '<<<' and not right_offsets
                value <<= right
                offsets = {key: offset + right for key, offset in offsets.items()}
            assert cursor == len(tokens) or tokens[cursor] == ')'
        return value, offsets

    result = expr()
    assert cursor == len(tokens)
    return result


def unpack(value, width, count):
    assert width % 4 == 0
    digit_width = width // 4
    text = format(value, 'x').zfill(digit_width * count)
    assert len(text) == digit_width * count
    return [int(text[pos:pos + digit_width], 16)
            for pos in range(len(text) - digit_width, -1, -digit_width)]


raw_packed, raw_offsets = packed_expression('rawClass')
representative_packed, _ = packed_expression('representatives')
destination_packed, _ = packed_expression('destinations')
kind_packed, _ = packed_expression('edgeKinds')
raw = unpack(raw_packed, 12, 4**10)
representatives = unpack(representative_packed, 20, 3741)
destinations = unpack(destination_packed, 12, 3741 * 4)
kinds = [(kind_packed >> (2 * index)) & 3 for index in range(3741 * 4)]
assert kind_packed < 2**(2 * 3741 * 4)

# Check the complete placement of the raw-class chunks, not just their names.
assert len(raw_offsets) == 768
for index in range(768):
    name = f'rawClass_{index}'
    expected_offset = max(0, (3145727 - 4096 * (index + 1)) * 4)
    assert raw_offsets[name] == expected_offset
    assert len(literal_text[name]) == (4095 if index == 767 else 4096)
    width = len(literal_text[name]) * 4
    assert ((raw_packed >> expected_offset) & (2**width - 1)) == literals[name]

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
generated = {}


def enumerate_windows(word=(), vertices=((0, 0),), bonds=frozenset(), code=0):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        generated[code] = (word, vertices, bonds)
        return
    x, y = vertices[-1]
    for direction, (dx, dy) in enumerate(steps):
        new_vertex = (x + dx, y + dy)
        bond = frozenset((vertices[-1], new_vertex))
        if bond not in bonds:
            enumerate_windows(word + (direction,), vertices + (new_vertex,),
                              bonds | {bond}, code * 4 + direction)


enumerate_windows()
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert len(generated) == 60092
assert all(value <= 3741 for value in raw)
assert {code for code, value in enumerate(raw) if value < 3741} == generated.keys()
assert all(code < 4**10 and code in generated and raw[code] == index
           for index, code in enumerate(representatives))
assert all(0 <= value <= 3741 for value in destinations)
assert all((value == 0) == (kind == 3) for value, kind in zip(destinations, kinds))


def raw_row(code):
    word, vertices, bonds = generated[code]
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    row = []
    for direction, (dx, dy) in enumerate(steps):
        new_vertex = (endpoint[0] + dx, endpoint[1] + dy)
        allowed = direction != (word[-1] + 2) % 4 and frozenset((endpoint, new_vertex)) not in bonds
        kind = 2 if revisit else (0 if direction == word[-1] else 1)
        successor_code = (code % 4**9) * 4 + direction
        row.append((allowed, kind, successor_code))
    return row


checked_edges = 0
for code, (word, vertices, bonds) in generated.items():
    class_id = raw[code]
    rep_code = representatives[class_id]
    rep_word = generated[rep_code][0]
    for direction, ((allowed, kind, successor), (rep_allowed, rep_kind, rep_successor)) in enumerate(
            zip(raw_row(code), raw_row(rep_code))):
        lane = class_id * 4 + direction
        assert allowed == rep_allowed == (destinations[lane] != 0), (code, direction, 'admissibility')
        assert kind == rep_kind, (code, direction, 'raw kind on every absolute direction')
        if allowed:
            checked_edges += 1
            assert kind == rep_kind == kinds[lane], (code, direction, 'kind')
            assert successor in generated and rep_successor in generated
            assert raw[successor] == raw[rep_successor] == destinations[lane] - 1, (code, direction, 'successor')
            if kind != 2:
                assert word[-1] == rep_word[-1], (code, direction, 'arrival')

edge_counts = Counter(kind for destination, kind in zip(destinations, kinds) if destination)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

chunk_results = {}
for index in range(190, 195):
    name = f'rawClass_{index}'
    start = raw_offsets[name]
    stop = start + len(literal_text[name]) * 4
    first_touched, last_touched = start // 12, (stop - 1) // 12
    first_whole, last_whole = (start + 11) // 12, stop // 12 - 1
    codes = range(first_touched, last_touched + 1)
    valid_codes = [code for code in codes if code in generated]
    chunk_results[name] = {
        'line': locations[name],
        'hex_digits': len(literal_text[name]),
        'sha256_hex_text': hashlib.sha256(literal_text[name].encode()).hexdigest(),
        'bit_interval_half_open': [start, stop],
        'touched_code_interval_inclusive': [first_touched, last_touched],
        'whole_code_interval_inclusive': [first_whole, last_whole],
        'touched_valid_words': len(valid_codes),
        'touched_invalid_words': len(codes) - len(valid_codes),
        'valid_class_range': [min(raw[code] for code in valid_codes), max(raw[code] for code in valid_codes)],
        'example': {
            'code': valid_codes[0],
            'directions': ''.join('ENWS'[d] for d in generated[valid_codes[0]][0]),
            'class': raw[valid_codes[0]],
            'representative_code': representatives[raw[valid_codes[0]]],
        },
    }

result = {
    'raw_window_counts': counts[1:],
    'raw_map_lane_count': len(raw),
    'valid_lane_count': len(generated),
    'invalid_sentinel': 3741,
    'invalid_lane_count': len(raw) - len(generated),
    'representative_count': len(representatives),
    'raw_admissible_edges_checked': checked_edges,
    'quotient_edge_counts': dict(edge_counts),
    'chunks': chunk_results,
    'result': 'All assertions passed',
}
Path('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
