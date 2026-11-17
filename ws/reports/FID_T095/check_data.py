"""Read-only reconstruction check for the assigned Automaton10Data literals."""

import ast
from array import array
from collections import Counter
from pathlib import Path
import json
import re
import hashlib


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    name: int(digits, 16)
    for name, digits in re.findall(r'def (\w+) : ℕ := 0x([0-9a-f]+)', text)
}
hex_widths = {
    name: 4 * len(digits)
    for name, digits in re.findall(r'def (\w+) : ℕ := 0x([0-9a-f]+)', text)
}


def evaluate(node):
    """Evaluate only names, naturals, addition, and shift; track literal offsets."""
    if isinstance(node, ast.Name):
        return literals[node.id], {node.id: 0}
    if isinstance(node, ast.Constant):
        assert isinstance(node.value, int) and node.value >= 0
        return node.value, {}
    assert isinstance(node, ast.BinOp)
    left, left_offsets = evaluate(node.left)
    right, right_offsets = evaluate(node.right)
    if isinstance(node.op, ast.Add):
        assert not (left & right), 'overlapping occupied bits in assembly'
        assert not (left_offsets.keys() & right_offsets.keys()), 'repeated chunk'
        return left + right, left_offsets | right_offsets
    assert isinstance(node.op, ast.LShift) and not right_offsets
    return left << right, {name: offset + right for name, offset in left_offsets.items()}


def unpack(name, width, count):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    value, offsets = evaluate(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    assert value < 1 << (width * count)
    blob = value.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    lanes = array('I')
    for index in range(count):
        start = width * index
        lanes.append((int.from_bytes(blob[start // 8:(start + width + 7) // 8], 'little') >> (start % 8)) & mask)
    return lanes, offsets


classes, raw_offsets = unpack('rawClass', 12, 4**10)
representatives, _ = unpack('representatives', 20, 3741)
destinations, _ = unpack('destinations', 12, 4 * 3741)
kinds, _ = unpack('edgeKinds', 2, 4 * 3741)
assert len(raw_offsets) == 768
intervals = sorted((offset, offset + hex_widths[name]) for name, offset in raw_offsets.items())
assert intervals[0][0] == 0
assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw = {}
depth_counts = Counter()


def bond(a, b):
    return (a, b) if a < b else (b, a)


def visit(code, directions, vertices, bonds):
    depth_counts[len(directions)] += 1
    end = vertices[-1]
    if len(directions) == 10:
        revisit = end in vertices[:-1]
        arrival = directions[-1]
        allowed = []
        raw_kinds = []
        for d, (dx, dy) in enumerate(steps):
            new_end = (end[0] + dx, end[1] + dy)
            allowed.append(d != (arrival + 2) % 4 and bond(end, new_end) not in bonds)
            raw_kinds.append(2 if revisit else 0 if d == arrival else 1)
        assert code not in raw
        raw[code] = (arrival, tuple(allowed), tuple(raw_kinds))
        return
    for d, (dx, dy) in enumerate(steps):
        new_end = (end[0] + dx, end[1] + dy)
        new_bond = bond(end, new_end)
        if new_bond not in bonds:
            visit(4 * code + d, directions + (d,), vertices + (new_end,), bonds | {new_bond})


visit(0, (), ((0, 0),), set())
assert [depth_counts[j] for j in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
for code, cls in enumerate(classes):
    assert cls <= 3741, (code, cls)
    assert (cls < 3741) == (code in raw), (code, cls)
assert len(set(classes[code] for code in raw)) == 3741

edge_counts = Counter()
for cls, code in enumerate(representatives):
    assert code < 4**10 and code in raw and classes[code] == cls, (cls, code)
    arrival, allowed, raw_kinds = raw[code]
    assert code % 4 == arrival
    for d in range(4):
        dest, kind = destinations[4 * cls + d], kinds[4 * cls + d]
        assert dest <= 3741
        assert (dest == 0) == (kind == 3)
        assert (dest != 0) == allowed[d]
        if dest:
            assert kind == raw_kinds[d]
            assert dest - 1 == classes[(code % 4**9) * 4 + d]
            edge_counts[kind] += 1

raw_edge_count = 0
for code, (arrival, allowed, raw_kinds) in raw.items():
    cls = classes[code]
    representative = representatives[cls]
    rep_arrival, rep_allowed, rep_kinds = raw[representative]
    assert allowed == rep_allowed
    # The paper's quotient lemma also states kind constancy on every direction.
    assert raw_kinds == rep_kinds
    for d in range(4):
        dest, kind = destinations[4 * cls + d], kinds[4 * cls + d]
        assert (dest != 0) == allowed[d]
        if allowed[d]:
            assert kind == raw_kinds[d]
            successor = (code % 4**9) * 4 + d
            assert successor in raw
            assert dest - 1 == classes[successor]
            if kind != 2:
                assert rep_arrival == arrival
            raw_edge_count += 1

assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
archive_lines = ['60092 3741']
archive_lines.extend(f'{code} {classes[code]}' for code in sorted(raw))
for cls, representative in enumerate(representatives):
    row = ([representative]
           + [destinations[4 * cls + d] - 1 for d in range(4)]
           + [kinds[4 * cls + d] if destinations[4 * cls + d] else -1 for d in range(4)])
    archive_lines.append(' '.join(map(str, row)))
archive_bytes = ('\n'.join(archive_lines) + '\n').encode()
archive_hash = hashlib.sha256(archive_bytes).hexdigest()
assert archive_hash == '671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785'
summary = {
    'reconstructed_archive_sha256': archive_hash,
    'reconstructed_archive_rows': len(archive_lines),
    'reconstructed_archive_bytes': len(archive_bytes),
    'raw_windows': len(raw),
    'raw_depth_counts': [depth_counts[j] for j in range(1, 11)],
    'invalid_word_sentinels': sum(cls == 3741 for cls in classes),
    'representatives_checked': len(representatives),
    'raw_direction_comparisons': 4 * len(raw),
    'raw_admissible_edges_checked': raw_edge_count,
    'quotient_edge_counts': dict(edge_counts),
    'chunks': {},
}
for i in range(440, 445):
    name = f'rawClass_{i}'
    lo = raw_offsets[name]
    hi = lo + hex_widths[name]
    first, last = lo // 12, (hi - 1) // 12
    codes = range(first, last + 1)
    valid = [code for code in codes if code in raw]
    full_first, full_last = (lo + 11) // 12, hi // 12 - 1
    boundary = [code for code in codes if 12 * code < lo or 12 * (code + 1) > hi]
    summary['chunks'][name] = {
        'lean_line': 15 + 2 * i,
        'bit_interval_half_open': [lo, hi],
        'raw_codes_touched_inclusive': [first, last],
        'fully_contained_raw_codes_inclusive': [full_first, full_last],
        'boundary_raw_codes': boundary,
        'raw_codes_touched_count': len(codes),
        'valid_raw_codes_touched': len(valid),
        'invalid_raw_codes_touched': len(codes) - len(valid),
        'valid_raw_codes_first_last': [valid[0], valid[-1]] if valid else None,
        'classes_on_boundary': {code: classes[code] for code in boundary},
        'examples': {code: classes[code] for code in valid[:3]},
    }

print(json.dumps(summary, indent=2))
Path('check_results.json').write_text(json.dumps(summary, indent=2) + '\n')
