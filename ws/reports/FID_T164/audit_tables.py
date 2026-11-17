"""Read-only reconstruction of the supplied Lean tables and paper contract."""

import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
values = {}
expressions = {}
literal_lengths = {}
line_numbers = {}


def evaluate(node):
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Add):
            return evaluate(node.left) + evaluate(node.right)
        if isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant)
            return evaluate(node.left) << evaluate(node.right)
    raise ValueError(ast.dump(node))


def offsets(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return offsets(node.left, offset) + offsets(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return offsets(node.left, offset + node.right.value)
    raise ValueError(ast.dump(node))


for lineno, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if not match:
        continue
    name, body = match.groups()
    line_numbers[name] = lineno
    if re.fullmatch(r'0x[0-9a-f]+', body):
        values[name] = int(body, 16)
        literal_lengths[name] = 4 * (len(body) - 2)
    else:
        tree = ast.parse(body.replace('<<<', '<<'), mode='eval').body
        values[name] = evaluate(tree)
        expressions[name] = offsets(tree)

assert len(literal_lengths) == 768 + 5 + 11 + 2
packing = {}
for name, parts in expressions.items():
    ordered = sorted(parts, key=lambda part: part[1])
    for (lower, shift), (_, next_shift) in zip(ordered, ordered[1:]):
        assert values[lower].bit_length() <= next_shift - shift
        assert literal_lengths[lower] == next_shift - shift
    assert ordered[0][1] == 0
    packing[name] = {
        'bit_length': values[name].bit_length(),
        'parts': len(parts),
        'chunk_offsets': {part: shift for part, shift in parts}
        if name in ('destinations', 'edgeKinds', 'representatives') else '768 checked',
    }


def unpack(name, width, count):
    value = values[name]
    data = value.to_bytes((value.bit_length() + 7) // 8, 'little')
    mask = (1 << width) - 1
    result = []
    for i in range(count):
        bit = i * width
        byte, remainder = divmod(bit, 8)
        length = (width + remainder + 7) // 8
        result.append((int.from_bytes(data[byte:byte + length], 'little') >> remainder) & mask)
    return result


raw = unpack('rawClass', 12, 4**10)
representatives = unpack('representatives', 20, 3741)
destinations = unpack('destinations', 12, 3741 * 4)
kinds = unpack('edgeKinds', 2, 3741 * 4)
assert max(raw) == 3741
assert max(representatives) < 4**10
assert max(destinations) <= 3741
assert all((dest == 0) == (kind == 3) for dest, kind in zip(destinations, kinds))

# Regenerate words from the paper's unoriented-bond recursion, retaining all
# four possible first directions. The endpoint can revisit a departure vertex.
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = Counter()
words = {}


def bond(a, b):
    return tuple(sorted((a, b)))


def generate(word, code, vertices, bonds):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        words[code] = (word, vertices, bonds)
        return
    x, y = vertices[-1]
    for direction, (dx, dy) in enumerate(steps):
        end = (x + dx, y + dy)
        edge = bond((x, y), end)
        if edge not in bonds:
            generate(word + (direction,), code * 4 + direction,
                     vertices + (end,), bonds | {edge})


generate((), 0, ((0, 0),), frozenset())
assert [counts[i] for i in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((cls < 3741) == (code in words) for code, cls in enumerate(raw))
assert len(set(raw[code] for code in words)) == 3741
assert all(code in words and raw[code] == cls for cls, code in enumerate(representatives))

errors = []
checks = Counter()
for code, (word, vertices, bonds) in words.items():
    cls = raw[code]
    rep, rep_vertices, _ = words[representatives[cls]]
    rep_revisit = rep_vertices[-1] in rep_vertices[:-1]
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    for direction, (dx, dy) in enumerate(steps):
        index = cls * 4 + direction
        admissible = direction != (word[-1] + 2) % 4 and bond((x, y), (x + dx, y + dy)) not in bonds
        expected_kind = 2 if revisit else int(direction != word[-1])
        rep_kind = 2 if rep_revisit else int(direction != rep[-1])
        if expected_kind != rep_kind:
            errors.append(('all_direction_kind_invariance', code, cls, direction))
        checks['raw_direction_kind_invariance'] += 1
        if (destinations[index] != 0) != admissible:
            errors.append(('admissibility', code, cls, direction))
        checks['raw_direction_admissibility'] += 1
        if admissible:
            successor = (code % (4**9)) * 4 + direction
            assert successor in words
            if destinations[index] != raw[successor] + 1:
                errors.append(('successor', code, cls, direction, destinations[index], raw[successor] + 1))
            if kinds[index] != expected_kind:
                errors.append(('kind', code, cls, direction, kinds[index], expected_kind))
            if expected_kind != 2 and rep[-1] != word[-1]:
                errors.append(('arrival', code, cls, direction))
            checks['admitted_successor_and_kind'] += 1
            if expected_kind != 2:
                checks['nonrevisit_arrival'] += 1

edge_counts = Counter(k for d, k in zip(destinations, kinds) if d)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

# Verify the literal fragments, including the destination fragment cutting a
# lane after eight bits, against the independently regenerated representative
# rows. This makes no correctness assumption about stored transition data.
expected_destinations = []
expected_kinds = []
for code in representatives:
    word, vertices, bonds = words[code]
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    for direction, (dx, dy) in enumerate(steps):
        admissible = direction != (word[-1] + 2) % 4 and bond((x, y), (x + dx, y + dy)) not in bonds
        if admissible:
            expected_destinations.append(raw[(code % (4**9)) * 4 + direction] + 1)
            expected_kinds.append(2 if revisit else int(direction != word[-1]))
        else:
            expected_destinations.append(0)
            expected_kinds.append(3)


def pack(lanes, width):
    # Small tables only, avoiding repeated shifts of the large raw class map.
    result = 0
    for lane in reversed(lanes):
        result = (result << width) + lane
    return result


expected_dest = pack(expected_destinations, 12)
expected_kind = pack(expected_kinds, 2)
assert expected_dest == values['destinations']
assert expected_kind == values['edgeKinds']
fragment_checks = {}
for name, assembled, width in (
    ('destinations_10', expected_dest, 15704),
    ('edgeKinds_0', expected_kind >> 13544, 16384),
    ('edgeKinds_1', expected_kind, 13544),
):
    assert values[name] == assembled & ((1 << width) - 1)
    fragment_checks[name] = {'line': line_numbers[name], 'bits': width, 'matches_regenerated': True}

summary = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'source_lines_read': len(source.splitlines()),
    'literal_count': len(literal_lengths),
    'packing': packing,
    'fragments': fragment_checks,
    'raw_counts': {i: counts[i] for i in range(1, 11)},
    'class_count': len(representatives),
    'raw_lane_counts': dict(Counter(cls == 3741 for cls in raw)),
    'destination_range': [min(destinations), max(destinations)],
    'kind_lane_counts': dict(Counter(kinds)),
    'edge_counts': dict(edge_counts),
    'checks': dict(checks),
    'errors': errors,
    'destination_fragment_boundary': {
        'complete_lanes': 15704 // 12,
        'partial_lane_bits': 15704 % 12,
        'class': (15704 // 12) // 4,
        'direction': (15704 // 12) % 4,
        'destination_lane': destinations[15704 // 12],
    },
    'highest_destination_lanes': destinations[-4:],
}
Path('audit_evidence.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
assert not errors, errors[:10]
