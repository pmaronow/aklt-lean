"""Read-only, exact-integer reconstruction of the supplied Lean automaton data."""

import ast
from collections import Counter
import json
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TARGETS = [f'rawClass_{i}' for i in range(430, 435)]
Q = 3741
N = 4**10
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
text = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M))
literals = {m[1]: int(m[2], 16) for m in literal_matches}
assert len(literals) == 786
locations = {m[1]: text.count('\n', 0, m.start()) + 1 for m in literal_matches}


def expression(name):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    return ast.parse(expr.replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return evaluate(node.left) << node.right.value
    assert isinstance(node.op, ast.Add)
    return evaluate(node.left) + evaluate(node.right)


def placements(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node.op, ast.LShift):
        return placements(node.left, offset + node.right.value)
    assert isinstance(node.op, ast.Add)
    return placements(node.left, offset) + placements(node.right, offset)


def unpack(name, width, size):
    tree = expression(name)
    ordered = sorted(placements(tree), key=lambda pair: pair[1])
    assert len(ordered) == len(set(n for n, _ in ordered))
    for (left, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert literals[left].bit_length() <= next_offset - offset
    value = evaluate(tree)
    assert value.bit_length() <= width * size
    raw_bytes = value.to_bytes((width * size + 7) // 8, 'little')
    mask = (1 << width) - 1
    byte_count = (width + 14) // 8
    values = []
    for i in range(size):
        bit = width * i
        start, shift = divmod(bit, 8)
        values.append((int.from_bytes(raw_bytes[start:start + byte_count], 'little') >> shift) & mask)
    return values, dict(ordered)


raw_class, offsets = unpack('rawClass', 12, N)
representatives, _ = unpack('representatives', 20, Q)
destinations, _ = unpack('destinations', 12, Q * 4)
kinds, _ = unpack('edgeKinds', 2, Q * 4)
assert all(0 <= c <= Q for c in raw_class)
assert all(0 <= code < N for code in representatives)
assert all(0 <= d <= Q for d in destinations)
assert all((d == 0) == (k == 3) for d, k in zip(destinations, kinds))


def directions(code):
    return [(code >> (2 * (9 - i))) & 3 for i in range(10)]


def geometry(code):
    vertex = (0, 0)
    vertices, bonds = [], set()
    ds = directions(code)
    raw = True
    for d in ds:
        vertices.append(vertex)
        step = STEPS[d]
        nxt = (vertex[0] + step[0], vertex[1] + step[1])
        bond = tuple(sorted((vertex, nxt)))
        if bond in bonds:
            raw = False
        bonds.add(bond)
        vertex = nxt
    return raw, ds[-1], vertex, set(vertices), bonds


def edge_info(geom, d):
    _, arrival, vertex, earlier_departures, bonds = geom
    step = STEPS[d]
    nxt = (vertex[0] + step[0], vertex[1] + step[1])
    allowed = d != (arrival + 2) % 4 and tuple(sorted((vertex, nxt))) not in bonds
    kind = 2 if vertex in earlier_departures else 0 if d == arrival else 1
    return allowed, kind


rep_geom = [geometry(code) for code in representatives]
assert all(g[0] and raw_class[code] == a for a, (code, g) in enumerate(zip(representatives, rep_geom)))
for a, g in enumerate(rep_geom):
    for d in range(4):
        allowed, kind = edge_info(g, d)
        j = a * 4 + d
        assert allowed == (destinations[j] != 0), ('representative admissibility', a, d)
        if allowed:
            successor = ((representatives[a] % (4**9)) * 4) + d
            assert kinds[j] == kind, ('representative kind', a, d)
            assert destinations[j] == raw_class[successor] + 1, ('representative successor', a, d)

# Independently enumerate precisely the distinct-unoriented-bond words in the paper.
raw_codes = set()
prefix_counts = Counter()


def generate(depth, vertex, bonds, code):
    if depth:
        prefix_counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for d, step in enumerate(STEPS):
        nxt = (vertex[0] + step[0], vertex[1] + step[1])
        bond = tuple(sorted((vertex, nxt)))
        if bond not in bonds:
            bonds.add(bond)
            generate(depth + 1, nxt, bonds, code * 4 + d)
            bonds.remove(bond)


generate(0, (0, 0), set(), 0)
assert [prefix_counts[i] for i in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert {i for i, c in enumerate(raw_class) if c < Q} == raw_codes

# Verify quotient compatibility for every genuine raw word, not just representatives.
for code in sorted(raw_codes):
    a = raw_class[code]
    g = geometry(code)
    for d in range(4):
        allowed, kind = edge_info(g, d)
        rep_allowed, rep_kind = edge_info(rep_geom[a], d)
        assert (allowed, kind) == (rep_allowed, rep_kind), ('class compatibility', code, a, d)
        j = a * 4 + d
        if allowed:
            successor = ((code % (4**9)) * 4) + d
            assert raw_class[successor] == destinations[j] - 1, ('raw successor', code, a, d)
            assert kind == kinds[j], ('raw kind', code, a, d)
            if kind != 2:
                assert g[1] == rep_geom[a][1], ('nonrevisit arrival', code, a, d)

edge_counts = Counter(k for d, k in zip(destinations, kinds) if d != 0)
assert [edge_counts[i] for i in range(3)] == [2516, 5032, 1872]

results = []
for name in TARGETS:
    offset = offsets[name]
    width = 16384
    start, stop = offset // 12, (offset + width + 11) // 12
    codes = range(start, stop)
    valid = [c for c in codes if c in raw_codes]
    invalid = [c for c in codes if c not in raw_codes]
    # Independently decode every overlapping lane, including the split boundary lanes.
    for code in codes:
        assert geometry(code)[0] == (raw_class[code] < Q)
    results.append({
        'declaration': name,
        'source_line': locations[name],
        'bit_interval_inclusive': [offset, offset + width - 1],
        'overlapping_codes_inclusive': [start, stop - 1],
        'overlapping_lanes': stop - start,
        'raw_windows': len(valid),
        'invalid_words': len(invalid),
        'raw_class_values': dict(sorted(Counter(raw_class[c] for c in codes).items())),
        'first_raw_example': None if not valid else {
            'code': valid[0], 'directions': ''.join('ENWS'[d] for d in directions(valid[0])),
            'class': raw_class[valid[0]], 'representative_code': representatives[raw_class[valid[0]]],
        },
        'all_checks': 'PASS',
    })

summary = {
    'input_lines': len(text.splitlines()), 'literal_definitions': len(literals),
    'raw_window_counts': dict(sorted(prefix_counts.items())),
    'quotient_size': Q, 'edge_counts_straight_turn_revisit': [edge_counts[i] for i in range(3)],
    'global_coverage_and_quotient_checks': 'PASS', 'targets': results,
}
Path(__file__).with_name('audit_results.json').write_text(json.dumps(summary, indent=2) + '\n')
for item in results:
    print(item['declaration'], 'bits', item['bit_interval_inclusive'],
          'codes', item['overlapping_codes_inclusive'], 'lanes', item['overlapping_lanes'],
          'raw', item['raw_windows'], 'invalid', item['invalid_words'], 'PASS')
print('Global coverage, all representatives, all raw transitions, arrivals, and edge counts: PASS')
