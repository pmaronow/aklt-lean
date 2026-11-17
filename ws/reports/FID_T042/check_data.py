"""Read-only reconstruction of the paper's memory-ten finite checks.

Run with python3 check_data.py. Only the supplied Lean source is read.
No Lean process or external archive is used.
"""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', source, re.M
    )
}
offsets = {}


def assemble(name):
    expression = re.search(
        r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M
    )[1]
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval')
    leaves = []

    def evaluate(node, offset=0):
        if isinstance(node, ast.Expression):
            return evaluate(node.body, offset)
        if isinstance(node, ast.Name):
            leaves.append(node.id)
            offsets[node.id] = offset
            return literals[node.id]
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            return evaluate(node.left, offset) + evaluate(node.right, offset)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
            shift = evaluate(node.right)
            return evaluate(node.left, offset + shift) << shift
        raise ValueError(ast.dump(node))

    value = evaluate(tree)
    assert len(leaves) == len(set(leaves))
    assert set(leaves) == {key for key in literals if key.startswith(name + '_')}
    ordered = sorted(leaves, key=lambda key: offsets[key])
    assert ordered == sorted(leaves, key=lambda key: -int(key.rsplit('_', 1)[1]))
    # Every lower chunk fits below the next one: addition cannot carry between chunks.
    for low, high in zip(ordered, ordered[1:]):
        assert literals[low].bit_length() <= offsets[high] - offsets[low]
    return value


def lanes(value, width, count):
    assert value.bit_length() <= width * count
    if width % 4 == 0:
        stride = width // 4
        digits = f'{value:0{count * stride}x}'
        return [int(digits[i:i + stride], 16)
                for i in range(len(digits) - stride, -1, -stride)]
    assert width == 2
    data = value.to_bytes((count + 3) // 4, 'little')
    return [(data[i // 4] >> (2 * (i % 4))) & 3 for i in range(count)]


raw = lanes(assemble('rawClass'), 12, 4**10)
representatives = lanes(assemble('representatives'), 20, 3741)
destinations = lanes(assemble('destinations'), 12, 3741 * 4)
kinds = lanes(assemble('edgeKinds'), 2, 3741 * 4)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def endpoint(vertex, direction):
    dx, dy = steps[direction]
    return vertex[0] + dx, vertex[1] + dy


def bond(v, w):
    return tuple(sorted((v, w)))


def decode(code):
    return tuple((code // 4**i) % 4 for i in range(9, -1, -1))


def encode(word):
    code = 0
    for direction in word:
        code = 4 * code + direction
    return code


# Independent depth-ten recursion from app-input-contracts.tex:232-237,390-401.
counts = [0] * 11
windows = {}


def generate(word=(), code=0, vertex=(0, 0), used=frozenset(), departures=()):
    counts[len(word)] += 1
    if len(word) == 10:
        assert code not in windows
        windows[code] = word, vertex, used, departures
        return
    for direction in range(4):
        next_vertex = endpoint(vertex, direction)
        edge = bond(vertex, next_vertex)
        if edge not in used:
            generate(word + (direction,), 4 * code + direction,
                     next_vertex, used | {edge}, departures + (vertex,))


generate()
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all(value <= 3741 for value in raw)
assert {code for code, value in enumerate(raw) if value < 3741} == set(windows)
assert {raw[code] for code in windows} == set(range(3741))
assert all(encode(decode(code)) == code for code in range(4**10))
assert all(code in windows and raw[code] == a for a, code in enumerate(representatives))
assert all(value <= 3741 for value in destinations)
assert all((destination == 0) == (kind == 3)
           for destination, kind in zip(destinations, kinds))
assert all(destination == 0 or kind < 3
           for destination, kind in zip(destinations, kinds))


def actual_row(state):
    word, vertex, used, departures = state
    arrival = word[-1]
    revisit = vertex in departures
    row = []
    for direction in range(4):
        admissible = (direction != (arrival + 2) % 4
                      and bond(vertex, endpoint(vertex, direction)) not in used)
        kind = 2 if revisit else 0 if direction == arrival else 1
        row.append((admissible, kind))
    return arrival, row


representative_rows = [actual_row(windows[code]) for code in representatives]
edge_counts = Counter()
for a, code in enumerate(representatives):
    arrival, row = representative_rows[a]
    for direction, (admissible, kind) in enumerate(row):
        index = 4 * a + direction
        assert (destinations[index] != 0) == admissible
        if admissible:
            successor = (code % 4**9) * 4 + direction
            assert successor in windows
            assert destinations[index] - 1 == raw[successor]
            assert kinds[index] == kind
            edge_counts[kind] += 1
assert dict(edge_counts) == {0: 2516, 1: 5032, 2: 1872}

# Check every raw row against its designated representative, including kinds on
# inadmissible directions and final directions on admitted nonrevisit edges.
for code, state in windows.items():
    a = raw[code]
    arrival, row = actual_row(state)
    rep_arrival, rep_row = representative_rows[a]
    assert row == rep_row
    for direction, (admissible, kind) in enumerate(row):
        if admissible:
            successor = (code % 4**9) * 4 + direction
            assert successor in windows
            assert destinations[4 * a + direction] - 1 == raw[successor]
            if kind != 2:
                assert arrival == rep_arrival

target_results = []
for number in range(175, 180):
    name = f'rawClass_{number}'
    low = offsets[name]
    high = low + 16384 - 1
    first, last = low // 12, high // 12
    valid = [code for code in range(first, last + 1) if code in windows]
    target_results.append({
        'name': name,
        'lean_line': 15 + 2 * number,
        'bit_interval_inclusive': [low, high],
        'code_interval_inclusive': [first, last],
        'intersected_lanes': last - first + 1,
        'raw_window_lanes': len(valid),
        'invalid_word_lanes': last - first + 1 - len(valid),
        'first_raw_example': None if not valid else {
            'code': valid[0], 'word': ''.join('ENWS'[d] for d in decode(valid[0])),
            'class': raw[valid[0]],
            'representative_code': representatives[raw[valid[0]]],
        },
        'sha256_hex_literal': hashlib.sha256(f'{literals[name]:04096x}'.encode()).hexdigest(),
    })

result = {
    'status': 'PASS',
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'literal_counts': dict(Counter(name.rsplit('_', 1)[0] for name in literals)),
    'window_counts_m0_through_m10': counts,
    'invalid_raw_word_count': len(raw) - len(windows),
    'classes': len(representatives),
    'admitted_class_edge_counts_straight_turn_revisit': [edge_counts[i] for i in range(3)],
    'raw_direction_comparisons': len(windows) * 4,
    'all_raw_and_representative_checks_pass': True,
    'targets': target_results,
}
print(json.dumps(result, indent=2))
