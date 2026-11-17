"""Read-only reconstruction of the finite contract in app-input-contracts.tex."""
from pathlib import Path
import ast
from collections import Counter
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
values = {name: int(value, 16) for name, value in re.findall(
    r'private noncomputable def (\w+) : ℕ := (0x[0-9a-fA-F]+)', source)}

def terms(tree, offset=0):
    if isinstance(tree, ast.Name):
        return [(tree.id, offset)]
    assert isinstance(tree, ast.BinOp)
    if isinstance(tree.op, ast.Add):
        return terms(tree.left, offset) + terms(tree.right, offset)
    assert isinstance(tree.op, ast.LShift) and isinstance(tree.right, ast.Constant)
    return terms(tree.left, offset + tree.right.value)

packed = {}
placements = {}
for family in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(r'noncomputable def ' + family + r' : ℕ := (.*)', source)[1]
    placements[family] = terms(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    assert Counter(n for n, _ in placements[family]) == Counter(
        n for n in values if n.startswith(family + '_'))
    intervals = sorted((offset, offset + values[name].bit_length())
                       for name, offset in placements[family])
    assert all(a[1] <= b[0] for a, b in zip(intervals, intervals[1:]))
    packed[family] = sum(values[name] << offset for name, offset in placements[family])

TOTAL = 4**10
# Extract the full 12-bit table in linear time, respecting little-endian lanes.
b = packed['rawClass'].to_bytes(TOTAL * 12 // 8, 'little')
classes = []
for i in range(0, len(b), 3):
    x = b[i] | (b[i + 1] << 8) | (b[i + 2] << 16)
    classes.extend((x & 4095, x >> 12))
assert len(classes) == TOTAL

def lanes(family, width, count):
    value = packed[family]
    return [(value >> (width * i)) & ((1 << width) - 1) for i in range(count)]

representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741 * 4)
kinds = lanes('edgeKinds', 2, 3741 * 4)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))

def bond(a, b):
    return tuple(sorted((a, b)))

raw = {}
counts = [0] * 11

def generate(code, directions, vertices, used):
    depth = len(directions)
    counts[depth] += 1
    if depth == 10:
        raw[code] = (directions, vertices, used)
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        nxt = (x + dx, y + dy)
        edge = bond((x, y), nxt)
        if edge not in used:
            generate(code * 4 + d, directions + (d,), vertices + (nxt,), used | {edge})

generate(0, (), ((0, 0),), frozenset())
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all(0 <= c <= 3741 for c in classes)
assert all((c < 3741) == (code in raw) for code, c in enumerate(classes))
assert all(rep < TOTAL and rep in raw and classes[rep] == a
           for a, rep in enumerate(representatives))
assert set(classes[code] for code in raw) == set(range(3741))
assert all(0 <= dest <= 3741 and ((dest == 0) == (kind == 3))
           for dest, kind in zip(destinations, kinds))

# Regenerate every raw row from its actual lattice geometry.
for code, (directions, vertices, used) in raw.items():
    a = classes[code]
    rep_directions, rep_vertices, _ = raw[representatives[a]]
    revisit = vertices[-1] in vertices[:-1]
    assert revisit == (rep_vertices[-1] in rep_vertices[:-1])
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        allowed = d != (directions[-1] + 2) % 4 and bond((x, y), (x + dx, y + dy)) not in used
        index = a * 4 + d
        assert (destinations[index] != 0) == allowed
        expected_kind = 2 if revisit else (0 if d == directions[-1] else 1)
        representative_kind = 2 if revisit else (0 if d == rep_directions[-1] else 1)
        assert expected_kind == representative_kind
        if allowed:
            successor = (code % (4**9)) * 4 + d
            assert successor in raw
            assert destinations[index] == classes[successor] + 1
            assert kinds[index] == expected_kind
            if expected_kind != 2:
                assert directions[-1] == rep_directions[-1]
        else:
            assert kinds[index] == 3

edge_counts = Counter(k for dest, k in zip(destinations, kinds) if dest)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
print('Raw counts by length:', counts)
print('Full coverage, class range, representatives, all 240368 raw direction checks: PASS')
print('Labelled edge counts:', dict(sorted(edge_counts.items())))

for name, offset in placements['rawClass']:
    if name not in {f'rawClass_{i}' for i in range(315, 320)}:
        continue
    low = offset // 12
    high = (offset + 16384 - 1) // 12
    selected = [code for code in range(low, high + 1) if code in raw]
    labels = [classes[code] for code in selected]
    print(name, 'bits', values[name].bit_length(), 'offset', offset,
          'codes', (low, high), 'raw', len(selected), 'invalid', high - low + 1 - len(selected),
          'distinct classes', len(set(labels)), 'class range', (min(labels), max(labels)) if labels else None)
    print('  boundary lanes:', [(code, classes[code], code in raw) for code in (low, high)])
    print('  first/last valid:', [(code, classes[code]) for code in selected[:2] + selected[-2:]])
print('All assertions passed.')
