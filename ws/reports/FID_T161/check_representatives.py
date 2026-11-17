"""Independent finite audit of the Lean literals against p:automaton10.

Reads only the supplied Lean definition file. Uses Python integers and a fresh
bond-distinct lattice-path generator; it does not invoke Lean or trust a stored
list of raw windows.
"""

import ast
import hashlib
import json
import re
from array import array
from collections import Counter
from pathlib import Path


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
values = {}
expressions = {}


def evaluate(node):
    if isinstance(node, ast.Expression):
        return evaluate(node.body)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.BinOp):
        left, right = evaluate(node.left), evaluate(node.right)
        if isinstance(node.op, ast.LShift):
            return left << right
        if isinstance(node.op, ast.Add):
            return left + right
    raise ValueError(ast.dump(node))


for name, expression in re.findall(
    r'^(?:private )?noncomputable def (\w+) : ℕ := (.+)$', source, re.M
):
    expressions[name] = expression
    values[name] = evaluate(ast.parse(expression.replace('<<<', '<<'), mode='eval'))


def lanes(name, width, count):
    value = values[name]
    assert value < 1 << (width * count), name
    data = value.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    result = array('I')
    for index in range(count):
        start, offset = divmod(width * index, 8)
        size = (offset + width + 7) // 8
        result.append((int.from_bytes(data[start:start + size], 'little') >> offset) & mask)
    return result


# Verify the exact concatenation expression, including chunks that cut a lane.
chunk_widths = [16384, 16384, 16384, 16384, 9284]
chunk_offsets = [58436, 42052, 25668, 9284, 0]
chunks = [values[f'representatives_{i}'] for i in range(5)]
assert sum(chunk_widths) == 3741 * 20
assert all(value < 1 << width for value, width in zip(chunks, chunk_widths))
assert values['representatives'] == sum(
    value << offset for value, offset in zip(chunks, chunk_offsets)
)

representatives = lanes('representatives', 20, 3741)
classes = lanes('rawClass', 12, 4**10)
destinations = lanes('destinations', 12, 3741 * 4)
kinds = lanes('edgeKinds', 2, 3741 * 4)
assert all(value <= 3741 for value in classes)
assert len(set(representatives)) == 3741
assert all(value < 4**10 for value in representatives)
assert all(classes[code] == a for a, code in enumerate(representatives))

steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
raw_words = {}
depth_counts = [0] * 11


def bond(x, y):
    return tuple(sorted((x, y)))


def generate(word=(), code=0, position=(0, 0), used=None, departures=()):
    if used is None:
        used = set()
    depth_counts[len(word)] += 1
    if len(word) == 10:
        raw_words[code] = (word, position, frozenset(used), frozenset(departures))
        return
    for direction, step in enumerate(steps):
        following = (position[0] + step[0], position[1] + step[1])
        edge = bond(position, following)
        if edge not in used:
            generate(word + (direction,), 4 * code + direction, following,
                     used | {edge}, departures + (position,))


generate()
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert {code for code, a in enumerate(classes) if a < 3741} == raw_words.keys()
assert all(code in raw_words for code in representatives)
assert set(classes[code] for code in raw_words) == set(range(3741))


def properties(raw):
    word, position, used, departures = raw
    arrival = word[-1]
    revisit = position in departures
    allowed = []
    kind = []
    for direction, step in enumerate(steps):
        following = (position[0] + step[0], position[1] + step[1])
        allowed.append(direction != (arrival + 2) % 4 and bond(position, following) not in used)
        kind.append(2 if revisit else 0 if direction == arrival else 1)
    return allowed, kind, arrival


representative_properties = [properties(raw_words[code]) for code in representatives]
edge_counts = Counter()
for a, code in enumerate(representatives):
    allowed, kind, arrival = representative_properties[a]
    assert arrival == code % 4
    for direction in range(4):
        index = 4 * a + direction
        successor_code = (code % 4**9) * 4 + direction
        expected_destination = classes[successor_code] + 1 if allowed[direction] else 0
        assert destinations[index] == expected_destination
        assert kinds[index] == (kind[direction] if allowed[direction] else 3)
        if allowed[direction]:
            edge_counts[kind[direction]] += 1

for code, raw in raw_words.items():
    a = classes[code]
    allowed, kind, arrival = properties(raw)
    rep_allowed, rep_kind, rep_arrival = representative_properties[a]
    assert allowed == rep_allowed
    assert kind == rep_kind
    for direction in range(4):
        if allowed[direction]:
            successor_code = (code % 4**9) * 4 + direction
            assert classes[successor_code] + 1 == destinations[4 * a + direction]
            if kind[direction] != 2:
                assert arrival == rep_arrival

assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

# Each chunk's affected class range includes any partially intersected lane.
chunk_results = []
for i, (width, offset) in enumerate(zip(chunk_widths, chunk_offsets)):
    chunk_results.append({
        'name': f'representatives_{i}',
        'width': width,
        'actual_bit_length': chunks[i].bit_length(),
        'least_bit_offset': offset,
        'affected_classes_inclusive': [offset // 20, (offset + width - 1) // 20],
    })

result = {
    'result': 'PASS',
    'chunks': chunk_results,
    'representative_count': len(representatives),
    'representative_min': min(representatives),
    'representative_max': max(representatives),
    'raw_window_counts_depth_1_to_10': depth_counts[1:],
    'raw_code_domain_size': len(classes),
    'raw_windows_checked': len(raw_words),
    'raw_direction_comparisons': 4 * len(raw_words),
    'edge_counts_straight_turn_revisit': [edge_counts[i] for i in range(3)],
    'representative_codes_sha256_as_u32le': hashlib.sha256(
        b''.join(code.to_bytes(4, 'little') for code in representatives)
    ).hexdigest(),
    'first_10_representatives': list(representatives[:10]),
    'last_10_representatives': list(representatives[-10:]),
    'lean_processes_used': 0,
}
print(json.dumps(result, indent=2))
