"""Read-only reconstruction check for the five assigned packed literals.

The only input read is the supplied Lean definition file. Geometry and
reconstruction follow paper/app-input-contracts.tex, d:memory-automaton and
p:automaton10. This is an independent Python check, not a Lean proof.
"""

import ast
import json
import re
from array import array
from collections import Counter
from pathlib import Path


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    match[1]: match[2][2:]
    for match in re.finditer(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', text)
}
values = {name: int(digits, 16) for name, digits in literals.items()}


def expression(name):
    match = re.search(rf'^noncomputable def {name} : ℕ := (.+)$', text, re.M)
    assert match is not None
    return ast.parse(match[1].replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.Constant):
        return node.value
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return evaluate(node.left) + evaluate(node.right)
    assert isinstance(node.op, ast.LShift)
    return evaluate(node.left) << evaluate(node.right)


def positions(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return positions(node.left, offset) + positions(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    return positions(node.left, offset + evaluate(node.right))


packed = {}
offsets = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    tree = expression(name)
    leaves = positions(tree)
    assert len(set(key for key, _ in leaves)) == len(leaves)
    expected_offset = 0
    for key, offset in reversed(leaves):
        assert offset == expected_offset, (key, offset, expected_offset)
        expected_offset += 4 * len(literals[key])
    offsets[name] = dict(leaves)
    packed[name] = evaluate(tree)
    assert format(packed[name], 'x') == ''.join(literals[key] for key, _ in leaves).lstrip('0')

# Each 12-bit lane is exactly three hexadecimal digits. Pad only the omitted
# leading zero nibble; preserve every internal and trailing zero.
hex_map = format(packed['rawClass'], 'x').zfill(3 * 4**10)
assert len(hex_map) == 3 * 4**10
classes = array('H', (int(hex_map[i:i+3], 16) for i in range(len(hex_map)-3, -1, -3)))


def lane(name, width, index):
    return (packed[name] >> (width * index)) & ((1 << width) - 1)


def decode(code):
    return tuple((code >> (2 * i)) & 3 for i in range(9, -1, -1))


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def add(point, step):
    return point[0] + step[0], point[1] + step[1]


def bond(a, b):
    return tuple(sorted((a, b)))


def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    for direction in word:
        new_point = add(vertices[-1], STEPS[direction])
        edge = bond(vertices[-1], new_point)
        assert edge not in bonds
        bonds.add(edge)
        vertices.append(new_point)
    return vertices, bonds


raw = {}
depth_counts = [0] * 11


def generate(word=(), code=0, point=(0, 0), used=frozenset()):
    depth_counts[len(word)] += 1
    if len(word) == 10:
        raw[code] = word
        return
    for direction, step in enumerate(STEPS):
        new_point = add(point, step)
        edge = bond(point, new_point)
        if edge not in used:
            generate(word + (direction,), 4 * code + direction, new_point, used | {edge})


generate()
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all(value <= 3741 for value in classes)
assert all((value < 3741) == (code in raw) for code, value in enumerate(classes))
assert set(classes[code] for code in raw) == set(range(3741))

representatives = [lane('representatives', 20, a) for a in range(3741)]
for a, code in enumerate(representatives):
    assert code < 4**10 and code in raw and classes[code] == a

edge_counts = Counter()
for a in range(3741):
    for d in range(4):
        destination = lane('destinations', 12, 4*a+d)
        kind = lane('edgeKinds', 2, 4*a+d)
        assert destination <= 3741
        assert (destination == 0) == (kind == 3)
        if destination:
            assert kind < 3
            edge_counts[kind] += 1
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

for code, word in raw.items():
    a = classes[code]
    vertices, used = geometry(word)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    incoming = word[-1]
    for d in range(4):
        destination = lane('destinations', 12, 4*a+d)
        stored_kind = lane('edgeKinds', 2, 4*a+d)
        admissible = d != (incoming + 2) % 4 and bond(endpoint, add(endpoint, STEPS[d])) not in used
        assert bool(destination) == admissible, ('admissibility', code, a, d)
        if admissible:
            kind = 2 if revisit else (0 if d == incoming else 1)
            successor_code = (code % 4**9) * 4 + d
            assert stored_kind == kind, ('kind', code, a, d)
            assert successor_code in raw
            assert destination - 1 == classes[successor_code], ('successor', code, a, d)
            if kind != 2:
                assert representatives[a] % 4 == incoming, ('arrival', code, a, d)

# The quotient lemma asks for matching kinds even at forbidden directions.
def kind_for(word, direction):
    vertices, _ = geometry(word)
    if vertices[-1] in vertices[:-1]:
        return 2
    return 0 if direction == word[-1] else 1


for code, word in raw.items():
    representative = raw[representatives[classes[code]]]
    assert all(kind_for(word, d) == kind_for(representative, d) for d in range(4))

summaries = []
for number in range(690, 695):
    name = f'rawClass_{number}'
    low = offsets['rawClass'][name]
    high = low + 4 * len(literals[name]) - 1
    first_code, last_code = low // 12, high // 12
    codes = range(first_code, last_code + 1)
    valid_codes = [code for code in codes if code in raw]
    counts = Counter(classes[code] for code in codes)
    boundary = []
    for code in (first_code, last_code):
        boundary.append({'code': code, 'word': ''.join('ENWS'[d] for d in decode(code)), 'class': classes[code]})
    summaries.append({
        'declaration': name,
        'source_line': text[:text.index(f'private noncomputable def {name} ')].count('\n') + 1,
        'hex_digits': len(literals[name]),
        'bit_range_inclusive': [low, high],
        'intersecting_code_range_inclusive': [first_code, last_code],
        'intersecting_code_count': last_code - first_code + 1,
        'raw_windows': len(valid_codes),
        'invalid_words': counts[3741],
        'distinct_raw_classes': len(set(classes[code] for code in valid_codes)),
        'boundary_lanes': boundary,
    })

result = {
    'result': 'PASS',
    'literal_declarations_parsed': len(literals),
    'raw_code_lanes_checked': len(classes),
    'depth_counts': depth_counts,
    'raw_windows_checked': len(raw),
    'class_representatives_checked': len(representatives),
    'raw_direction_checks': 4 * len(raw),
    'labelled_edge_counts': dict(edge_counts),
    'assigned': summaries,
}
print(json.dumps(result, indent=2))
