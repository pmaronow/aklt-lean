"""Independent finite check of the supplied Lean automaton literals.

Reads only the assigned Lean input. Uses exact Python natural arithmetic,
unoriented lattice edges, and the paper's append/delete successor rule.
"""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
values = {}
layouts = {}
literal_widths = {}
literal_lines = {}


def arithmetic(node):
    if isinstance(node, ast.Name):
        return values[node.id], [(node.id, 0)]
    if isinstance(node, ast.Constant):
        assert type(node.value) is int and node.value >= 0
        return node.value, []
    assert isinstance(node, ast.BinOp)
    left, ll = arithmetic(node.left)
    right, rl = arithmetic(node.right)
    if isinstance(node.op, ast.Add):
        return left + right, ll + rl
    assert isinstance(node.op, ast.LShift) and not rl
    return left << right, [(name, offset + right) for name, offset in ll]


for line_no, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if not match:
        continue
    name, expression = match.groups()
    if re.fullmatch(r'0x[0-9a-f]+', expression):
        values[name] = int(expression, 16)
        literal_widths[name] = 4 * (len(expression) - 2)
        literal_lines[name] = line_no
    else:
        values[name], layouts[name] = arithmetic(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)


def lanes(name, width, count):
    number = values[name]
    assert number < 1 << (width * count), name
    data = number.to_bytes((width * count + 7) // 8, 'little') + b'\0\0\0'
    result = []
    for index in range(count):
        start = width * index
        pos, bit = divmod(start, 8)
        result.append((int.from_bytes(data[pos:pos + 4], 'little') >> bit) & ((1 << width) - 1))
    return result


for name, layout in layouts.items():
    ordered = sorted(layout, key=lambda item: item[1])
    assert ordered[0][1] == 0
    for (low, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert offset + literal_widths[low] == next_offset, (name, low)
    assert len({chunk for chunk, _ in layout}) == len(layout)

raw = lanes('rawClass', 12, 4**10)
representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741 * 4)
kinds = lanes('edgeKinds', 2, 3741 * 4)
assert max(raw) == 3741
assert max(destinations) <= 3741
assert all((dest == 0) == (kind == 3) for dest, kind in zip(destinations, kinds))
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
valid_codes = set()
depth_counts = [0] * 11
errors = Counter()
examples = {}
raw_edges = Counter()
raw_edges_by_chunk = Counter()
seen_class = Counter()
nonrevisit_arrivals = {}
owner_by_lane = {}
chunk_details = {}

for name, offset in layouts['destinations']:
    if name not in {f'destinations_{i}' for i in range(5, 10)}:
        continue
    high = offset + literal_widths[name] - 1
    touched = list(range(offset // 12, high // 12 + 1))
    for index in touched:
        owner_by_lane.setdefault(index, []).append(name)
    chunk_details[name] = {
        'lean_line': literal_lines[name],
        'literal_hex_digits': literal_widths[name] // 4,
        'bit_range_in_destinations': [offset, high],
        'edge_lane_range': [touched[0], touched[-1]],
        'class_range': [touched[0] // 4, touched[-1] // 4],
        'positive_destinations_in_touched_lanes': sum(destinations[i] > 0 for i in touched),
    }


def check(condition, kind, example):
    if not condition:
        errors[kind] += 1
        examples.setdefault(kind, example)


def visit(word, code, point, bonds, departures):
    depth = len(word)
    depth_counts[depth] += 1
    if depth < 10:
        for d, (dx, dy) in enumerate(steps):
            new_point = (point[0] + dx, point[1] + dy)
            bond = frozenset((point, new_point))
            if bond not in bonds:
                visit(word + (d,), 4 * code + d, new_point,
                      bonds | {bond}, departures | {point})
        return
    valid_codes.add(code)
    a = raw[code]
    check(a < 3741, 'raw_class_range', code)
    if a >= 3741:
        return
    seen_class[a] += 1
    arrival = word[-1]
    revisit = point in departures
    for d, (dx, dy) in enumerate(steps):
        index = 4 * a + d
        new_point = (point[0] + dx, point[1] + dy)
        allowed = d != (arrival + 2) % 4 and frozenset((point, new_point)) not in bonds
        check((destinations[index] != 0) == allowed, 'admissibility', (code, a, d))
        if allowed:
            kind = 2 if revisit else (0 if d == arrival else 1)
            successor_code = (code % (4**9)) * 4 + d
            expected = raw[successor_code] + 1
            check(raw[successor_code] < 3741, 'raw_successor', (code, d))
            check(destinations[index] == expected, 'successor', (code, a, d, expected, destinations[index]))
            check(kinds[index] == kind, 'kind', (code, a, d, kind, kinds[index]))
            raw_edges[kind] += 1
            for chunk in owner_by_lane.get(index, []):
                raw_edges_by_chunk[chunk] += 1
            if not revisit:
                check(representatives[a] % 4 == arrival, 'arrival', (code, a, d))
                nonrevisit_arrivals.setdefault(a, set()).add(arrival)


visit((), 0, (0, 0), frozenset(), frozenset())
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((raw[code] < 3741) == (code in valid_codes) for code in range(4**10))
assert len(seen_class) == 3741
assert all(code in valid_codes and raw[code] == a for a, code in enumerate(representatives))
assert all(len(arrivals) == 1 for arrivals in nonrevisit_arrivals.values())
quotient_counts = Counter(kind for dest, kind in zip(destinations, kinds) if dest != 0)
assert quotient_counts == {0: 2516, 1: 5032, 2: 1872}
for name, details in chunk_details.items():
    details['raw_admissible_successor_comparisons'] = raw_edges_by_chunk[name]
    details['sha256_literal_big_endian_fixed_width'] = hashlib.sha256(
        values[name].to_bytes(literal_widths[name] // 8, 'big')).hexdigest()
summary = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'raw_windows': len(valid_codes),
    'depth_counts': depth_counts,
    'classes': len(seen_class),
    'raw_admissible_edges': dict(raw_edges),
    'quotient_admissible_edges': dict(quotient_counts),
    'raw_code_lanes_checked': len(raw),
    'quotient_edge_lanes_checked': len(destinations),
    'chunk_details': chunk_details,
    'errors': dict(errors),
    'first_error_examples': examples,
}
print(json.dumps(summary, indent=2))
assert not errors, errors
