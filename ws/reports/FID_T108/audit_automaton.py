"""Read only the supplied Lean data; regenerate the paper's finite contract."""
from pathlib import Path
import ast
import collections
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', source
    )
}


def expression(name):
    text = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M)[1]
    tree = ast.parse(text.replace('<<<', '<<'), mode='eval').body

    def visit(node):
        if isinstance(node, ast.Name):
            return literals[node.id], {node.id: 0}
        if isinstance(node, ast.Constant):
            return node.value, {}
        assert isinstance(node, ast.BinOp)
        left, left_offsets = visit(node.left)
        right, right_offsets = visit(node.right)
        if isinstance(node.op, ast.LShift):
            assert not right_offsets
            return left << right, {k: v + right for k, v in left_offsets.items()}
        assert isinstance(node.op, ast.Add)
        assert not (left & right), 'overlapping nonzero fields'
        assert left_offsets.keys().isdisjoint(right_offsets)
        return left + right, left_offsets | right_offsets

    return visit(tree)


def unpack(packed, width, count):
    # Take short byte slices instead of repeatedly shifting a multi-megabit int.
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    return [
        (int.from_bytes(data[(width * i) // 8:(width * i + width + 7) // 8], 'little')
         >> ((width * i) % 8)) & mask
        for i in range(count)
    ]


raw_packed, offsets = expression('rawClass')
raw = unpack(raw_packed, 12, 4**10)
representatives = unpack(expression('representatives')[0], 20, 3741)
destinations = unpack(expression('destinations')[0], 12, 4 * 3741)
kinds = unpack(expression('edgeKinds')[0], 2, 4 * 3741)
assert set(offsets) == {f'rawClass_{i}' for i in range(768)}
assert all(offsets[f'rawClass_{i}'] == (767 - i) * 16384 - 4 for i in range(767))
assert offsets['rawClass_767'] == 0
assert all((raw_packed >> offsets[k]) & ((1 << 16384) - 1) == literals[k]
           for k in offsets if k != 'rawClass_767')

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def edge(x, y):
    return tuple(sorted((x, y)))


def decode(code):
    return tuple((code // 4**i) % 4 for i in range(9, -1, -1))


def geometry(word):
    position = (0, 0)
    vertices = [position]
    bonds = set()
    for d in word:
        dx, dy = STEPS[d]
        new = (position[0] + dx, position[1] + dy)
        bond = edge(position, new)
        assert bond not in bonds
        bonds.add(bond)
        vertices.append(new)
        position = new
    return position, bonds, set(vertices[:-1])


def transitions(code):
    word = decode(code)
    position, bonds, departures = geometry(word)
    revisit = position in departures
    rows = []
    for d, (dx, dy) in enumerate(STEPS):
        new = (position[0] + dx, position[1] + dy)
        allowed = d != (word[-1] + 2) % 4 and edge(position, new) not in bonds
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        successor = (code % 4**9) * 4 + d
        rows.append((allowed, kind, successor))
    return word[-1], rows


counts = [0] * 11
raw_codes = []


def generate(word, code, position, bonds):
    counts[len(word)] += 1
    if len(word) == 10:
        raw_codes.append(code)
        return
    for d, (dx, dy) in enumerate(STEPS):
        new = (position[0] + dx, position[1] + dy)
        bond = edge(position, new)
        if bond not in bonds:
            generate(word + (d,), code * 4 + d, new, bonds | {bond})


generate((), 0, (0, 0), set())
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert raw_codes == sorted(set(raw_codes))
raw_set = set(raw_codes)
assert max(raw) <= 3741
assert {i for i, cls in enumerate(raw) if cls < 3741} == raw_set
assert {raw[code] for code in raw_codes} == set(range(3741))

edge_counts = [0, 0, 0]
representative_transitions = []
for cls, code in enumerate(representatives):
    assert code < 4**10 and code in raw_set and raw[code] == cls
    arrival, rows = transitions(code)
    representative_transitions.append((arrival, rows))
    for d, (allowed, kind, successor) in enumerate(rows):
        dest = destinations[4 * cls + d]
        stored_kind = kinds[4 * cls + d]
        assert 0 <= dest <= 3741
        assert (dest == 0) == (stored_kind == 3)
        assert allowed == (dest != 0)
        if allowed:
            assert stored_kind == kind
            assert successor in raw_set
            assert dest - 1 == raw[successor]
            edge_counts[kind] += 1

admissible_raw_edges = 0
for code in raw_codes:
    cls = raw[code]
    arrival, rows = transitions(code)
    rep_arrival, rep_rows = representative_transitions[cls]
    for d, (allowed, kind, successor) in enumerate(rows):
        rep_allowed, rep_kind, _ = rep_rows[d]
        assert allowed == rep_allowed
        assert kind == rep_kind  # Also check kinds on inadmissible directions.
        if allowed:
            admissible_raw_edges += 1
            assert successor in raw_set
            assert raw[successor] == destinations[4 * cls + d] - 1
            if kind != 2:
                assert arrival == rep_arrival
assert edge_counts == [2516, 5032, 1872]

summary = {
    'raw_count_by_depth': counts,
    'raw_coverage': len(raw_codes),
    'invalid_sentinel_count': len(raw) - len(raw_codes),
    'class_count': len(set(raw[code] for code in raw_codes)),
    'quotient_edge_counts': edge_counts,
    'admissible_raw_edges_checked': admissible_raw_edges,
    'chunks': [],
}
for i in range(505, 510):
    name = f'rawClass_{i}'
    start = offsets[name]
    end = start + 16384
    low, high = start // 12, (end - 1) // 12
    affected = list(range(low, high + 1))
    valid = [code for code in affected if code in raw_set]
    examples = valid[:3] + valid[-3:]
    info = {
        'name': name,
        'source_line': next(n for n, line in enumerate(source.splitlines(), 1)
                            if line.startswith('private noncomputable def ' + name + ' ')),
        'bit_offset_inclusive': [start, end - 1],
        'bit_length': literals[name].bit_length(),
        'code_range_inclusive': [low, high],
        'touched_lane_count': len(affected),
        'valid_windows': len(valid),
        'invalid_windows': len(affected) - len(valid),
        'distinct_valid_classes': len({raw[code] for code in valid}),
        'examples': [dict(code=code, word=''.join('ENWS'[d] for d in decode(code)),
                          cls=raw[code], representative=representatives[raw[code]])
                     for code in examples],
        'first_lane_bits_from_chunk': 12 - start % 12,
        'last_lane_bits_from_chunk': end % 12 or 12,
    }
    summary['chunks'].append(info)

print(json.dumps(summary, indent=2))
