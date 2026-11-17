"""Read-only reconstruction check of the supplied Lean automaton data."""
from collections import Counter
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(hx, 16)
    for name, hx in re.findall(r'def (\w+) : ℕ := 0x([0-9a-f]+)', source)
}


def parse_packing(name):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.+)$', source, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s', '', expression)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == '(':
            result = expr()
            assert tokens[position] == ')'
            position += 1
            return result
        if token.isdigit():
            return ('number', int(token))
        assert token in literals
        return ('literal', token)

    def expr():
        nonlocal position
        left = atom()
        # Every compound operand in this generated file is parenthesized.
        if position < len(tokens) and tokens[position] != ')':
            operator = tokens[position]
            assert operator in ('+', '<<<')
            position += 1
            left = (operator, left, atom())
        return left

    tree = expr()
    assert position == len(tokens)
    offsets = {}

    def evaluate(node, offset=0):
        if node[0] == 'number':
            return node[1]
        if node[0] == 'literal':
            assert node[1] not in offsets
            offsets[node[1]] = offset
            return literals[node[1]]
        if node[0] == '<<<':
            assert node[2][0] == 'number'
            shift = node[2][1]
            return evaluate(node[1], offset + shift) << shift
        left = evaluate(node[1], offset)
        right = evaluate(node[2], offset)
        # Addition must concatenate disjoint bits, with no hidden carry.
        assert left & right == 0
        return left + right

    value = evaluate(tree)
    assert set(offsets) == {key for key in literals if key.startswith(name + '_')}
    return value, offsets


def lanes(value, width, count):
    assert width % 4 == 0 or width == 2
    assert value < 1 << (width * count)
    if width == 2:
        data = value.to_bytes((count + 3) // 4, 'little')
        return [(data[i // 4] >> (2 * (i % 4))) & 3 for i in range(count)]
    digits = width // 4
    hx = format(value, f'0{digits * count}x')
    return [int(hx[i:i + digits], 16) for i in range(len(hx) - digits, -1, -digits)]


packed, offsets = parse_packing('rawClass')
classes = lanes(packed, 12, 4 ** 10)
representatives = lanes(parse_packing('representatives')[0], 20, 3741)
destinations = lanes(parse_packing('destinations')[0], 12, 3741 * 4)
kinds = lanes(parse_packing('edgeKinds')[0], 2, 3741 * 4)
assert all(offsets[f'rawClass_{i}'] == (767 - i) * 16384 - (4 if i < 767 else 0)
           for i in range(768))
assert all(literals[f'rawClass_{i}'] < 1 << 16384 for i in range(768))

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw = {}
depth_counts = [0] * 11


def bond(x, y):
    return tuple(sorted((x, y)))


def generate(code, vertices, used, last):
    depth = len(vertices) - 1
    depth_counts[depth] += 1
    endpoint = vertices[-1]
    if depth == 10:
        raw[code] = (endpoint, frozenset(used), endpoint in vertices[:-1], last)
        return
    for d, (dx, dy) in enumerate(steps):
        destination = (endpoint[0] + dx, endpoint[1] + dy)
        edge = bond(endpoint, destination)
        if edge not in used:
            used.add(edge)
            vertices.append(destination)
            generate(4 * code + d, vertices, used, d)
            vertices.pop()
            used.remove(edge)


generate(0, [(0, 0)], set(), None)
assert depth_counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert set(classes) <= set(range(3742))
assert {code for code, a in enumerate(classes) if a < 3741} == set(raw)
assert {classes[code] for code in raw} == set(range(3741))
assert all(code < 4 ** 10 and code in raw and classes[code] == a
           for a, code in enumerate(representatives))
assert all(0 <= dest <= 3741 for dest in destinations)
assert all((dest == 0) == (kind == 3) for dest, kind in zip(destinations, kinds))
assert all(kind < 3 for dest, kind in zip(destinations, kinds) if dest)

checked_allowed_edges = 0
for code, (endpoint, used, revisit, last) in raw.items():
    a = classes[code]
    rep = raw[representatives[a]]
    for d, (dx, dy) in enumerate(steps):
        edge = bond(endpoint, (endpoint[0] + dx, endpoint[1] + dy))
        admissible = d != (last + 2) % 4 and edge not in used
        raw_kind = 2 if revisit else (0 if d == last else 1)
        rep_kind = 2 if rep[2] else (0 if d == rep[3] else 1)
        assert raw_kind == rep_kind, ('kind compatibility', code, d, a)
        dest = destinations[4 * a + d]
        assert bool(dest) == admissible, ('admissibility', code, d, a)
        if admissible:
            checked_allowed_edges += 1
            successor = (code % 4 ** 9) * 4 + d
            assert successor in raw
            assert kinds[4 * a + d] == raw_kind, ('stored kind', code, d, a)
            assert dest - 1 == classes[successor], ('successor', code, d, a)
            if raw_kind != 2:
                assert last == representatives[a] % 4, ('arrival', code, d, a)

edge_counts = Counter(kind for dest, kind in zip(destinations, kinds) if dest)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

chunk_results = []
for i in range(460, 465):
    key = f'rawClass_{i}'
    low = offsets[key]
    high = low + 16384
    first, last = low // 12, (high - 1) // 12
    raw_codes = [code for code in range(first, last + 1) if code in raw]
    chunk_results.append({
        'declaration': key,
        'lean_line': source[:source.index('private noncomputable def ' + key + ' ')].count('\n') + 1,
        'bit_offset': low,
        'bit_end_exclusive': high,
        'first_touched_code': first,
        'last_touched_code': last,
        'touched_raw_codes': len(raw_codes),
        'touched_invalid_codes': last - first + 1 - len(raw_codes),
        'distinct_touched_classes': len({classes[code] for code in raw_codes}),
        'boundary_lanes_partial': [code for code in (first, last)
                                   if not (low <= code * 12 and (code + 1) * 12 <= high)],
        'sample_raw_mappings': [[code, classes[code]] for code in raw_codes[:3]],
    })

result = {
    'result': 'PASS',
    'literal_chunks_read': len(literals),
    'packing_additions_disjoint': True,
    'raw_depth_counts': depth_counts,
    'raw_codes_checked': len(classes),
    'raw_direction_checks': len(raw) * 4,
    'admissible_raw_edges_checked': checked_allowed_edges,
    'class_representatives_checked': len(representatives),
    'quotient_edge_counts': dict(edge_counts),
    'chunks': chunk_results,
}
(HERE / 'audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
